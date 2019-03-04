-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek

import tactic.basic
-- import data.list.basic

namespace environment
meta def decl_omap {α : Type} (e : environment) (f : declaration → option α) : list α :=
  e.fold [] $ λ d l, match f d with
                     | some r := r :: l
                     | none := l
                     end

meta def decl_map {α : Type} (e : environment) (f : declaration → α) : list α :=
  e.decl_omap $ λ d, some (f d)

meta def get_decls (e : environment) : list declaration :=
  e.decl_map id

meta def get_trusted_decl_names (e : environment) : list name :=
  e.decl_omap (λ d, if d.is_trusted then some d.to_name else none)

meta def get_decl_names (e : environment) : list name :=
  e.decl_map declaration.to_name
end environment

namespace tactic

@[user_attribute]
meta def back_attribute : user_attribute unit (option unit) := {
  name := `back,
  descr :=
"A lemma that should be applied to a goal whenever possible;
use the tactic `back` to automatically `apply` all lemmas tagged `[back]`.
Lemmas tagged with `[back!]` will be applied even if the
resulting subgoals cannot all be discharged.",
  parser := optional $ lean.parser.tk "!"
}

/-- Stub for implementing faster lemma filtering using Pi binders in the goal -/
private meta def is_lemma_applicable (lem : expr) : tactic bool := return true

meta def head_symbol : expr → name
| (expr.pi _ _ _ t) := head_symbol t
| (expr.app f _) := head_symbol f
| (expr.const n _) := n
| _ := `_

meta def head_symbols : expr → list name
| (expr.pi _ _ _ t) := head_symbols t
| `(%%a ↔ %%b) := head_symbols a ++ head_symbols b
| (expr.app f _) := head_symbols f
| (expr.const n _) := [n]
| _ := [`_]

meta def symbols : expr → list name
| (expr.pi _ _ e t) := symbols e ++ symbols t
| (expr.app f _) := head_symbols f
| (expr.const n _) := [n]
| _ := [`_]

-- #check list.forall_mem_inter_of_forall_left
-- example : true :=
-- begin
--   (do e ← to_expr ``(nat.dvd_add_iff_left) >>= infer_type, trace $ head_symbol e),
--   (do e ← to_expr ``(list.forall_mem_inter_of_forall_left) >>= infer_type, trace $ head_symbol e),
--   (do e ← to_expr ``(nat.dvd_add_iff_left) >>= infer_type, trace $ symbols e),
--   (do e ← to_expr ``(@list.forall_mem_inter_of_forall_left) >>= infer_type, trace $ symbols e),
-- end

-- example (l₁ l₂ : list ℕ): ∀ x, x ∈ l₁ ∩ l₂ → x = 2 :=
-- begin
--   apply list.forall_mem_inter_of_forall_left,
-- end

meta structure back_lemma :=
(lem       : expr)
(finishing : bool)
(index     : ℕ)

-- We fake an instance here for convenience. Correctness is ensured by creating unique index values.
meta instance : decidable_eq back_lemma :=
λ a b, if a.index = b.index then is_true undefined else is_false undefined

-- Can be much better!
meta def filter_lemmas (goal_type : expr) (lemmas : list back_lemma) : tactic (list back_lemma) :=
do -- trace format!"filtering lemmas for {goal_type}",
   let hs := head_symbol goal_type,
   -- trace hs,
  --  lemmas.mmap $ λ l, (do t ← infer_type l.lem, return (l.lem, head_symbols t)) >>= trace,
   result ← lemmas.mfilter $ λ l, (do t ← infer_type l.lem, return $ hs ∈ head_symbols t),
   -- trace $ result.map back_lemma.lem,
   return result

inductive apply_step
| facts    -- We're working on lemmas with no hypotheses (likely all local hypotheses).
| relevant -- We're working on lemmas with the same head constant as the goal.
| others   -- We're getting desperate, and working on all remaining lemmas.

def apply_step.weight : apply_step → ℕ
| apply_step.facts := 1
| apply_step.relevant := 4
| apply_step.others := 16

-- An expr representing a goal, along with a list of lemmas which we have not yet tried
-- `apply`ing against that goal.
meta structure apply_state :=
(goal      : expr)
(goal_type : expr) -- We store this explicitly, rather than looking it up with `infer_type` as needed, because we're doing manual tactic_state management
(committed : bool) -- If the goal is not 'committed', we can stash it if we get stuck.
(step      : apply_step)
(lemmas    : list back_lemma)

meta structure back_state :=
(steps        : ℕ := 0)
(limit        : ℕ)
/- We carry the full list of lemmas along, as we may want to reorder or discard some.
-- (e.g. we don't use `iff` lemmas more than once, to avoid loops) -/
(facts        : list back_lemma) -- A `fact` is a lemma with no hypotheses; usually a local hypothesis
(lemmas       : list back_lemma) -- All other lemmas
/- We carry along an internal `tactic_state`,
-- so metavariables aren't contaminated by other branches of the search. -/
(tactic_state : tactic_state)
(stashed      : list expr := {})   -- Stores goals which we're going to return to the user.
(completed    : list expr := {})   -- Stores completed goals.
(goals        : list apply_state)
(num_mvars    : ℕ)

-- meta instance : has_to_string back_state :=
-- { to_string := λ s, to_string format!"back_state: ({s.stashed.length}/{s.completed.length}) ({s.committed_new.length}/{s.in_progress_new.length}/{s.committed_fc.length}/{s.in_progress_fc.length}) ({s.num_mvars}/{s.steps})" }

-- meta instance has_to_format_back_state : has_to_format back_state :=
-- { to_format := λ s, to_string s }

-- meta instance has_to_tactic_format_back_state : has_to_tactic_format back_state :=
-- { to_tactic_format := λ s,
--     do return $ to_string s }

meta def back_state.done (s : back_state) : bool :=
s.goals.empty

-- TODO Think hard about what goes here; possibly allow customisation.
meta def back_state.complexity (s : back_state) : ℕ × bool × ℕ × ℕ :=
-- It's essential to put `stashed` first, so that stashed goals are not returned until
-- we've exhausted other branches of the search tree.
-- (s.stashed.length, s.done, 2 * s.in_progress_fc.length + 2 * s.committed_fc.length + s.steps, s.steps + s.num_mvars) -- works!
-- (s.stashed.length, s.done, 16 * s.in_progress_fc.length + 16 * s.committed_fc.length + 4 * s.in_progress_new.length + 4 * s.committed_new.length + s.steps, s.steps + s.num_mvars)
(s.stashed.length, s.done, 4 * (s.goals.map (λ as : apply_state, as.step.weight)).sum + s.steps, s.steps + s.num_mvars)

-- Count the number of arguments not determined by later arguments.
meta def count_arrows : expr → ℕ
| (expr.pi n bi d b) :=
   if b.has_var_idx 0 then count_arrows b
                      else 1 + count_arrows b
| `(%%a <-> %%b) := 1 + min (count_arrows a) (count_arrows b)
| _ := 0

/-- Sorts a list of lemmas according to the number of explicit arguments
    (more precisely, arguments which are not determined by later arguments). -/
meta def sort_by_arrows (L : list back_lemma) : tactic (list back_lemma) :=
do M ← L.mmap (λ e, do c ← count_arrows <$> infer_type e.lem, return (c, e)),
   return ((list.qsort (λ (p q : ℕ × back_lemma), p.1 ≤ q.1) M).map (λ p, p.2))

meta def back_state.init (goal : expr) (progress finishing : list expr) (limit : option ℕ) : tactic back_state :=
λ s, (do
   -- We sort the lemmas, preferring lemmas which, when applied, will produce fewer new goals.
   let all_lemmas : list back_lemma :=
     (finishing.enum.map (λ e, ⟨e.2, tt, e.1⟩)) ++
     (progress.enum.map  (λ e, ⟨e.2, ff, e.1 + finishing.length⟩)),
   lemmas_with_counts ← all_lemmas.mmap (λ e, do ty ← infer_type e.lem, return (count_arrows ty, expr.is_pi ty, e)),
   let (facts', lemmas) := lemmas_with_counts.partition (λ p : ℕ × bool × back_lemma, p.2.1 = ff),
   let facts := facts'.map (λ p, p.2.2),
   let sorted_lemmas := ((list.qsort (λ (p q : ℕ × bool × back_lemma), p.1 ≤ q.1) lemmas).map (λ p, p.2.2)),
  --  let sorted_lemmas := lemmas.map (λ p, p.2.2),
  --  trace "facts:",
  --  trace $ facts.map (λ f, f.lem),
  --  trace "lemmas:",
  --  trace $ sorted_lemmas.map (λ f, f.lem),
   goal_type ← infer_type goal,
   return
   { back_state .
     limit           := limit.get_or_else 20,
     facts           := facts,
     lemmas          := sorted_lemmas,
     tactic_state    := s,
     in_progress_new := [⟨goal, goal_type, facts⟩],
     num_mvars       := 0 }) s

-- keep only uninstantiable metavariables
meta def partition_mvars (L : list expr) : tactic (list expr × list expr) :=
(list.partition (λ e, e.is_meta_var)) <$>
  (L.mmap (λ e, instantiate_mvars e))

meta def partition_apply_state_mvars (L : list apply_state) : tactic (list apply_state × list apply_state) :=
(list.partition (λ as, as.goal.is_meta_var)) <$>
  (L.mmap (λ as, do e' ← instantiate_mvars as.goal, return ⟨e', as.goal_type, as.lemmas⟩))

-- TODO remove in cleanup
meta def pad_trace (n : ℕ) {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
do let s := (list.repeat '.' n).as_string,
   p ← pp a,
   trace (s ++ sformat!"{p}")

/--
* Discard any goals which have already been solved,
* increment the `step` counter,
* and remove applied iffs.
-/
meta def back_state.clean (s : back_state) (g : expr) (last_lemma : back_lemma) : tactic back_state :=
do (stashed,     completed_1) ← partition_mvars s.stashed,
   (committed_new,   completed_2) ← partition_apply_state_mvars s.committed_new,
   (in_progress_new, completed_3) ← partition_apply_state_mvars s.in_progress_new,
   (committed_fc,   completed_4) ← partition_apply_state_mvars s.committed_fc,
   (in_progress_fc, completed_5) ← partition_apply_state_mvars s.in_progress_fc,
   let completed := s.completed ++ completed_1 ++ (completed_2 ++ completed_3 ++ completed_4 ++ completed_5).map(apply_state.goal),
   -- We don't apply `iff` lemmas more than once.
   lemmas ← (iff_mp last_lemma.lem >> pure (s.lemmas.erase last_lemma))
            <|> pure s.lemmas,
   return
   { back_state.
     steps       := s.steps + 1,
     stashed     := stashed,
     completed   := g :: completed,
     committed_new   := committed_new,
     in_progress_new := in_progress_new,
     committed_fc    := committed_fc,
     in_progress_fc  := in_progress_fc,
     lemmas      := lemmas,
     .. s }

-- Given a tactic that produces a new back_state, we can run that in the context
-- of a tactic_state contained within a back_state...
meta def back_state.run_on_bundled_state (s : back_state) {α : Type*} (tac : tactic (back_state × α)) : tactic (back_state × α) :=
λ ts,
  match tac s.tactic_state with
  | result.success s' sts' := result.success ({ tactic_state := sts', ..s'.1 }, s'.2) ts
  | result.exception msg pos sts' := result.exception msg pos ts
  end

meta def back_state.apply_lemma (s : back_state) (g : expr) (e : back_lemma) (committed : bool) : tactic (back_state × bool) :=
s.run_on_bundled_state $
do --trace $ "attempting to apply " ++ to_string e.lem,
   set_goals [g],
   prop ← is_proof g,
   explicit ← (list.empty ∘ expr.list_meta_vars) <$> infer_type g,
   goal_types ← get_goals >>= λ gs, gs.mmap infer_type,
  --  pad_trace s.steps goal_types,
   apply_thorough e.lem,
  --  pad_trace s.steps goal_types,
  --  trace $  "successfully applied " ++ to_string e.lem,
  --  get_goals >>= λ gs, gs.mmap infer_type >>= pad_trace s.steps,
  --  goal_types ← get_goals >>= λ gs, gs.mmap infer_type,
  --  pad_trace s.steps e,
   s' ← s.clean g e,
   (done >> return (s', prop ∧ explicit)) <|> do
   gs ← get_goals,
   types ← gs.mmap infer_type,
   success_if_fail $ types.mfirst $ λ t, unify t expr.mk_false,
  --  guard ¬(expr.mk_false ∈ types),
   let num_mvars := (types.map expr.list_meta_vars).join.length,
   as ← gs.mmap $ λ g, (do t ← infer_type g, relevant_facts ← filter_lemmas t s.facts, return (⟨g, t, relevant_facts⟩ : apply_state)),
   if e.finishing ∨ committed then
     return ({ committed_new := as ++ s.committed_new, num_mvars := num_mvars, .. s' }, ff)
   else
     return ({ in_progress_new := as ++ s.in_progress_new, num_mvars := num_mvars, .. s' }, ff)


meta def back_state.add_goal (s : back_state) (new committed : bool) (as : apply_state) :=
if committed then
  if new then
    { committed_new := as :: s.committed_new .. s }
  else
    { committed_fc := as :: s.committed_fc .. s }
else
  if new then
    { in_progress_new := as :: s.in_progress_new .. s }
  else
    { in_progress_fc := as :: s.in_progress_fc .. s }

meta def back_state.apply (s : back_state) (new committed : bool) : apply_state → tactic (list back_state)
| as :=
  match as.lemmas with
  | [] := fail "No lemmas applied to the current goal."
  | (h :: t) :=
    do r ← try_core $ s.apply_lemma as.goal h committed,
       match r with
       | none := back_state.apply ⟨as.goal, as.goal_type, t⟩
       | (some (bs, prop_discharged)) :=
         do if prop_discharged then
              -- if we discharged a propositional goal, don't consider other ways to solve it!
              return [bs]
            else
              return [bs, s.add_goal new committed ⟨as.goal, as.goal_type, t⟩]
       end
  end

meta def back_state.apply_in_progress_fc (s : back_state) : tactic (list back_state) :=
match s.in_progress_fc with
| [] := undefined
| (p :: ps) :=
  do let s' := { in_progress_fc := ps, ..s },
     s'.apply ff ff p <|>
     return (if s'.steps > 0 then [{ stashed := p.goal :: s'.stashed, .. s' }] else [])
end

meta def back_state.apply_committed_fc (s : back_state) : tactic (list back_state) :=
match s.committed_fc with
| [] := undefined
| (c :: cs) :=
  -- We must discharge `c`.
  do let s' := { committed_fc := cs, ..s },
     s'.apply ff tt c <|> return []
end

meta def back_state.apply_in_progress_new (s : back_state) : tactic (list back_state) :=
match s.in_progress_new with
| [] := undefined
| (p :: ps) :=
  do let s' := { in_progress_new := ps, ..s },
     s'.apply tt ff p <|>
     do relevant_lemmas ← filter_lemmas p.goal_type s.lemmas,
        return [{ in_progress_fc := ⟨p.goal, p.goal_type, relevant_lemmas⟩ :: s'.in_progress_fc, .. s' }]
end

meta def back_state.apply_committed_new (s : back_state) : tactic (list back_state) :=
match s.committed_new with
| [] := undefined
| (c :: cs) :=
  -- We must discharge `c`.
  do let s' := { committed_new := cs, ..s },
     s'.apply tt tt c <|>
     return [{ committed_fc := ⟨c.goal, c.goal_type, s.lemmas⟩ :: s'.committed_fc, .. s' }]
end

meta def back_state.children (s : back_state) : tactic (list back_state) :=
if s.committed_new.empty then
  if s.in_progress_new.empty then
    if s.committed_fc.empty then
      s.apply_in_progress_fc
    else
      s.apply_committed_fc
  else
    s.apply_in_progress_new
else
  s.apply_committed_new

def lexicographic_preorder {α β : Type*} [preorder α] [preorder β] : preorder (α × β) :=
{ le := λ a b, a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2),
  le_refl := λ a, or.inr ⟨rfl, le_refl _⟩,
  le_trans := λ a b c h₁ h₂,
  begin
    dsimp at *,
    cases h₁,
    { left,
      cases h₂,
      { exact lt_trans h₁ h₂ },
      { rwa ←h₂.left } },
    { cases h₂,
      { left, rwa h₁.left },
      { right, exact ⟨eq.trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩ }
    } end }
local attribute [instance] lexicographic_preorder

-- Just a check that we're actually using lexicographic ordering here.
example : (5,10) ≤ (10,3) := by exact dec_trivial

def bool_preorder : preorder bool :=
{ le := λ a b, bor a (bnot b) = tt,
  le_refl := λ a, begin cases a; simp end,
  le_trans := λ a b c h₁ h₂, begin cases a; cases b; cases c; simp at *; assumption end }
local attribute [instance] bool_preorder

example : tt ≤ ff := by exact dec_trivial

private meta def insert_new_state : back_state → list back_state → list back_state
/- depth first search: -/
-- | s states := s :: states
/- complexity ordered search -/
| s (h :: t) := if s.complexity ≤ h.complexity then
                  s :: h :: t
                else
                  h :: (insert_new_state s t)
| s [] := [s]

private meta def insert_new_states : list back_state → list back_state → list back_state
| [] states := states
| (h :: t) states := insert_new_states t (insert_new_state h states)

-- Either return a completed back_state, or an updated list.
private meta def run_one_step : list back_state → tactic (back_state ⊕ (list back_state))
| [] := failed
| (h :: t) :=
  if h.done then
    return $ sum.inl h
  else
    do if h.steps > h.limit then
         return $ sum.inr t
       else do
        --  trace format!"running: {h}",
         c ← h.children,
        --  trace format!"children: {c}",
         return $ sum.inr $ insert_new_states c t

private meta def run : list back_state → tactic back_state
| states :=
  do
    --  trace "run:",
    --  trace states,
     r ← run_one_step states,
     match r with
     | (sum.inl success) := return success
     | (sum.inr states) := run states
     end

-- Whee! After selecting a successful back_state, we clobber the tactic_state with its
-- internal tactic_state; it's as if we got it right first try!
private meta def run' : list back_state → tactic back_state
| states :=
  λ ts, match run states ts with
        | result.success bs ts' := result.success bs bs.tactic_state
        | result.exception msg pos ts' := result.exception msg pos ts'
        end

/-- Takes two sets of lemmas, 'progress' lemmas and 'finishing' lemmas.

    Progress lemmas should be applied whenever possible, regardless of new hypotheses.
    Finishing lemmas should be applied only as part of a sequence of applications that close the goals.

    `back` succeeds if at least one progress lemma was applied, or all goals are discharged.
    -/
meta def back (progress finishing : list expr) (limit : option ℕ) : tactic unit :=
do g :: gs ← get_goals,
   i ← back_state.init g progress finishing limit,
   f ← run' [i],
   set_goals [g],
   g ← instantiate_mvars g,
   set_goals (g.list_meta_vars ++ gs),
   guard (f.steps > 0) -- Make sure some progress was made.

private meta def lookup_tagged_lemma (n : name) : tactic (bool × expr) :=
do is_elim ← back_attribute.get_param n,
   e ← mk_const n,
   return (is_elim.is_none, e)

private meta def collect_tagged_lemmas : list name → tactic (list expr × list expr)
| [] := return ([], [])
| (n :: rest) := do (normals, elims) ← collect_tagged_lemmas rest,
                    (is_elim, e) ← lookup_tagged_lemma n,
                    return $ if is_elim then (normals, e :: elims) else (e :: normals, elims)

open lean lean.parser expr interactive.types

-- `back_arg_type`, and associated definitions, are a close imitation of `simp_arg_type` from core.

@[derive has_reflect]
meta inductive back_arg_type : Type
| all_hyps : back_arg_type
| except   : name  → back_arg_type
| back     : pexpr → back_arg_type
| elim     : pexpr → back_arg_type

meta def back_arg : parser back_arg_type :=
(tk "*" *> return back_arg_type.all_hyps)
<|> (tk "-" *> back_arg_type.except <$> ident)
<|> (tk "!" *> (back_arg_type.back <$> texpr))
<|> (back_arg_type.elim <$> texpr)

meta def back_arg_list : parser (list back_arg_type) :=
(tk "*" *> return [back_arg_type.all_hyps]) <|> list_of back_arg <|> return []

local postfix *:9001 := many

meta def with_back_ident_list : parser (list (name × bool)) :=
(tk "with" *> (((λ n, (n, ff)) <$> ident_) <|> (tk "!" *> (λ n, (n, tt)) <$> ident))*) <|> return []

private meta def resolve_exception_ids (all_hyps : bool) :
  list name → list name → list name → tactic (list name × list name)
| []        gex hex := return (gex.reverse, hex.reverse)
| (id::ids) gex hex := do
  p ← resolve_name id,
  let e := p.erase_annotations.get_app_fn.erase_annotations,
  match e with
  | const n _           := resolve_exception_ids ids (n::gex) hex
  | local_const n _ _ _ := when (not all_hyps) (fail $ sformat! "invalid local exception {id}, '*' was not used") >>
                           resolve_exception_ids ids gex (n::hex)
  | _                   := fail $ sformat! "invalid exception {id}, unknown identifier"
  end

/- Return (pr, fi, gex, hex, all) -/
meta def decode_back_arg_list (hs : list back_arg_type) :
  tactic $ list pexpr × list pexpr × list name × list name × bool :=
do
  let (pr, fi, ex, all) := hs.foldl
    (λ r h,
       match r, h with
       | (ps, fs, ex, all), back_arg_type.all_hyps  := (ps, fs, ex, tt)
       | (ps, fs, ex, all), back_arg_type.except id := (ps, fs, id::ex, all)
       | (ps, fs, ex, all), back_arg_type.elim f    := (ps, f::fs, ex, all)
       | (ps, fs, ex, all), back_arg_type.back p    := (p::ps, fs, ex, all)
       end)
    ([], [], [], ff),
  (gex, hex) ← resolve_exception_ids all ex [] [],
  return (pr.reverse, fi.reverse, gex, hex, all)

meta def all_defs : tactic (list expr) :=
do env ← get_env,
   let names := env.get_trusted_decl_names,
   let names := names.filter $ λ n,
     n.components.head ≠ "_private" ∧ (to_string n.components.ilast).to_list.head ≠ '_'
       ∧ to_string n.components.ilast ≠ "inj_arrow" ∧ to_string n.components.ilast ≠ "cases_on",
   names.mmap mk_const

/--
Returns a list of "finishing lemmas" (which should only be applied as part of a
chain of applications which discharges the goal), and a list of "progress lemmas",
the successful application of any one of which counting as a success.
-/
--This is a close relative of `mk_assumption_set` in tactic/interactive.lean.
meta def mk_assumption_set (no_dflt : bool) (hs : list back_arg_type) (use : list (name × bool)) :
  tactic (list expr × list expr) :=
do (extra_pr_lemmas, extra_fi_lemmas, gex, hex, all_hyps) ← decode_back_arg_list hs,
   /- `extra_lemmas` is explicitly requested lemmas
      `gex` are the excluded names
      `hex` are the excluded local hypotheses
      `all_hyps` means all hypotheses were included, via `*` -/
   extra_pr_lemmas ← extra_pr_lemmas.mmap i_to_expr_for_apply,
   extra_fi_lemmas ← extra_fi_lemmas.mmap i_to_expr_for_apply,
   (tagged_pr_lemmas, tagged_fi_lemmas) ← attribute.get_instances `back >>= collect_tagged_lemmas,

   let use_fi := (use.filter (λ p : name × bool, ¬ p.2)).map (λ p, p.1),
   let use_pr := (use.filter (λ p : name × bool, p.2)).map (λ p, p.1),

   environment ← if `_ ∈ use_fi then all_defs else return [],
   let use_fi := use_fi.erase `_,

   with_fi_lemmas ← (list.join <$> use_fi.mmap attribute.get_instances) >>= list.mmap mk_const,
   with_pr_lemmas ← (list.join <$> use_pr.mmap attribute.get_instances) >>= list.mmap mk_const,

   -- If the goal is not propositional, we do not include the non-propositional local hypotheses,
   -- unless specifically included via `[*]`.
   prop ← succeeds propositional_goal,
   hypotheses ← list.filter (λ h : expr, h.local_uniq_name ∉ hex) <$>  -- remove explicitly removed hypotheses
   if (¬no_dflt ∧ prop) ∨ all_hyps then
     local_context
   else if no_dflt then
     return []
   else -- it's a non-propositional goal, no `[*]`, no `only`, so conservatively only take propositional hypotheses
     local_context >>= list.mfilter (λ e, is_proof e),

   let filter_excl : list expr → list expr := list.filter $ λ h, h.const_name ∉ gex,
   return (/- progress  lemmas -/ filter_excl $ extra_pr_lemmas ++ with_pr_lemmas ++ tagged_pr_lemmas,
           /- finishing lemmas -/ filter_excl $ extra_fi_lemmas ++ environment ++ with_fi_lemmas ++ hypotheses ++ tagged_fi_lemmas)

meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_meta_var then some (unchecked_cast pexpr.mk_placeholder) else none)

namespace interactive

open interactive interactive.types expr

/--
`back` performs backwards reasoning, recursively applying lemmas against the goal.

Lemmas can be specified via an optional argument, e.g. as `back [foo, bar]`. Every lemma
tagged with an attribute `qux` may be included using the syntax `back with qux`.
Additionally, `back` always includes any lemmas tagged with the attribute `@[back]`,
and all local propositional hypotheses.

(If the goal is a proposition, `back` is more aggressive and includes all hypotheses. This
can be achieved in other cases using `back [*]`.)

Lemmas which were included because of the `@[back]` attribute, or local hypotheses,
can be excluded using the notation `back [-h]`.

Further, lemmas can be tagged with the `@[back!]` attribute, or appear in the arguments with
a leading `!`, e.g. as `back [!foo]` or `back with !qux`. The tactic `back` will return
successfully if it either discharges the goal, or applies at least one `!` lemma.
(More precisely, `back` will apply some non-empty and maximal collection of the lemmas,
subject to the condition that if any lemma not marked with `!` is applied, all resulting
subgoals are later dischargeed.)

Finally, the search depth can be controlled, e.g. as `back 5`. The default value is 100.

`back?` will print a trace message showing the term it constructed. (Possibly with placeholders,
for use with `refine`.)

`back` will apply lemmas even if this introduces new metavariables (so for example it is possible
to apply transitivity lemmas), but with the proviso that any subgoals containing metavariables must
be subsequently discharged in a single step. -- FIXME this is no longer what's implemented!
-/
meta def back
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (wth : parse with_back_ident_list) (limit : parse (optional small_nat)) : tactic string :=
do g :: _ ← get_goals,
   (pr, fi) ← tactic.mk_assumption_set no_dflt hs wth,
   r ← (do
     tactic.back pr fi limit,
     g ← instantiate_mvars g,
     r ← pp (replace_mvars g),
     pure (if g.has_meta_var then sformat!"refine {r}" else sformat!"exact {r}")),
   if trace.is_some then tactic.trace r else skip,
   return r

end interactive

end tactic

attribute [back] congr_arg congr_fun

-- Some examples of lemmas that we might want to tag `back` or `back!`.

local attribute [back!] min_le_left min_le_right le_max_left le_max_right le_refl
local attribute [back] lt_min le_min max_lt max_le

-- Even transitivity lemmas are okay; back uses them, but somewhat conservatively.
local attribute [back] lt_of_lt_of_le lt_of_le_of_lt
