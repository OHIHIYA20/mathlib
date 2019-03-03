-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Keeley Hoek

import tactic.basic
import data.list.basic

namespace tactic

@[user_attribute]
meta def back_attribute : user_attribute unit (option unit) := {
  name := `back,
  descr :=
"A lemma that should be applied to a goal whenever possible;
use the tactic `back` to automatically `apply` all lemmas tagged `[back]`.
Lemmas tagged with `[back!]` will be applied even if the
resulting goals cannot all be discharged.",
  parser := optional $ lean.parser.tk "!"
}

/-- Stub for implementing faster lemma filtering using Pi binders in the goal -/
private meta def is_lemma_applicable (lem : expr) : tactic bool := return true

meta structure back_lemma :=
(lem       : expr)
(finishing : bool)
(index     : ℕ)

-- We fake an instance here for convenience. Correctness is ensured by creating unique index values.
meta instance : decidable_eq back_lemma :=
λ a b, if a.index = b.index then is_true undefined else is_false undefined

meta structure goal_mvar :=
(original synthetic : expr)

meta def mk_goal_mvar (g : expr) : tactic goal_mvar :=
do t ← infer_type g,
   s ← mk_meta_var t,
   return ⟨g, s⟩

meta def goal_mvar.new_mvars (g : goal_mvar) : tactic goal_mvar :=
do t ← infer_type g.original,
   s ← mk_meta_var t,
   return ⟨g.original, s⟩

-- An expr representing a goal, along with a list of lemmas which we have not yet tried
-- `apply`ing against that goal.
meta structure apply_state :=
(goal   : goal_mvar)
(lemmas : list back_lemma)

meta structure back_state :=
(steps       : ℕ := 0)
(limit       : option ℕ)
(lemmas      : list back_lemma) -- We carry the lemmas along, as we may want to reorder or discard some.
(stashed     : list goal_mvar := {})   -- Stores goals which we're going to return to the user after unification.
(completed   : list goal_mvar := {})   -- Stores completed goals, which should be unified on success.
(committed   : list apply_state := {}) -- Stores goals which we must complete.
(in_progress : list apply_state)       -- Stores goals which we're still working on.

-- TODO Think hard about what goes here; possibly allow customisation.
meta def back_state.complexity (s : back_state) : ℕ × ℕ × ℕ :=
(s.committed.length, s.in_progress.length, s.steps)

meta def back_state.done (s : back_state) : bool :=
s.committed.empty ∧ s.in_progress.empty

meta def back_state.add_goal (s : back_state) (committed : bool) (as : apply_state) :=
if committed then
  { committed := as :: s.committed .. s }
else
  { in_progress := as :: s.in_progress .. s }

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

meta def back_state.init (progress finishing : list expr) (limit : option ℕ): tactic back_state :=
do g :: _ ← get_goals,
   -- We sort the lemmas, preferring lemmas which, when applied, will produce fewer new goals.
   lemmas ← sort_by_arrows $ (finishing.enum.map (λ e, ⟨e.2, tt, e.1⟩)) ++
                             (progress.enum.map  (λ e, ⟨e.2, ff, e.1 + finishing.length⟩)),
   gmvar ← mk_goal_mvar g,
   return
   { limit       := limit,
     lemmas      := lemmas,
     in_progress := [⟨gmvar, lemmas⟩] }

-- keep only uninstantiable metavariables
meta def partition_mvars (L : list goal_mvar) : tactic (list goal_mvar × list goal_mvar) :=
(list.partition (λ e, e.synthetic.is_meta_var)) <$>
  (L.mmap (λ e, do e' ← instantiate_mvars e.synthetic, return ⟨e.original, e'⟩))

meta def partition_apply_state_mvars (L : list apply_state) : tactic (list apply_state × list apply_state) :=
(list.partition (λ as, as.goal.synthetic.is_meta_var)) <$>
  (L.mmap (λ as, do e' ← instantiate_mvars as.goal.synthetic, return ⟨⟨as.goal.original, e'⟩, as.lemmas⟩))

-- TODO remove in cleanup
meta def pad_trace (n : ℕ) {α : Type} [has_to_tactic_format α] (a : α) : tactic unit :=
do let s := (list.repeat ' ' n).as_string,
   p ← pp a,
   trace (s ++ sformat!"{p}")

/--
* Discard any goals which have already been solved,
* increment the `step` counter,
* and remove applied iffs.
-/
meta def back_state.clean (s : back_state) (last_lemma : back_lemma) : tactic back_state :=
do (stashed, completed_1) ← partition_mvars s.stashed,
   (committed, completed_2)   ← partition_apply_state_mvars s.committed,
   (in_progress, completed_3) ← partition_apply_state_mvars s.in_progress,
   let completed := s.completed ++ completed_1 ++ (completed_2 ++ completed_3).map(apply_state.goal),
   -- We don't apply `iff` lemmas more than once.
   lemmas ← (iff_mp last_lemma.lem >> pure (s.lemmas.erase last_lemma))
            <|> pure s.lemmas,
   return
   { steps       := s.steps + 1,
     stashed     := stashed,
     completed   := completed,
     committed   := committed,
     in_progress := in_progress,
     lemmas      := lemmas,
     .. s}

meta def back_state.apply_lemma (s : back_state) (e : back_lemma) (committed : bool) : tactic back_state :=
do trace $ "attempting to apply " ++ to_string e.lem,
   get_goals >>= λ gs, gs.mmap infer_type >>= pad_trace s.steps,
  apply_thorough e.lem,
  trace "!",
  --  goal_types ← get_goals >>= λ gs, gs.mmap infer_type,
  --  pad_trace s.steps e,
   s' ← s.clean e,
   (done >> return s') <|> do
   gs ← get_goals,
   as ← gs.mmap $ λ g, (do gmvar ← mk_goal_mvar g, return (⟨gmvar, s.lemmas⟩ : apply_state)),
   if e.finishing ∨ committed then
     return { committed := as ++ s.committed, .. s' }
   else
     return { in_progress := as ++ s.in_progress, .. s' }

meta def back_state.apply (s : back_state) (committed : bool) : apply_state → tactic (list back_state)
| as :=
  match as.lemmas with
  | [] := fail "No lemmas applied to the current goal."
  | (h :: t) := do r ← try_core $ s.apply_lemma h committed,
                   match r with
                   | none := back_state.apply ⟨as.goal, t⟩
                   | (some bs) := do ng ← as.goal.new_mvars,
                                     return [bs, s.add_goal committed ⟨ng, t⟩]
                   end
  end

meta def back_state.children (s : back_state) : tactic (list back_state) :=
do
match s.committed with
| [] :=
  -- Let's see if we can do anything with `in_progress` goals
  match s.in_progress with
  | [] := undefined
  | (p :: ps) :=
  do set_goals [p.goal.synthetic],
     s.apply ff p <|>
     return [{ in_progress := ps, stashed := p.goal :: s.stashed, .. s }]
  end
| (c :: cs) :=
  -- We must discharge `c`.
  do set_goals [c.goal.synthetic],
     s.apply tt c <|> return []
end

def lexicographic_preorder {α β : Type*} [preorder α] [decidable_eq α] [preorder β] : preorder (α × β) :=
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
      { exact or.inr ⟨eq.trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩ }
    } end }
local attribute [instance] lexicographic_preorder

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
    do c ← h.children,
       return $ sum.inr $ insert_new_states c t

private meta def run : list back_state → tactic back_state
| states :=
  do r ← run_one_step states,
     match r with
     | (sum.inl success) := return success
     | (sum.inr states) := run states
     end

-- meta def back_state.run : back_state → tactic back_state
-- | s :=
--   do
--   guard (s.steps ≤ s.limit.get_or_else 20),
--   match s.committed with
--   | [] :=
--     -- Let's see if we can do anything with `in_progress` goals
--     match s.in_progress with
--     | [] := return s -- Great, all done!
--     | (p :: ps) :=
--     do set_goals [p],
--       (s.lemmas.enum.any_of $ λ e, { in_progress := ps, .. s }.apply e.1 e.2.1 e.2.2 >>= back_state.run)
--       <|> { in_progress := ps, stashed := p :: s.stashed, .. s }.run
--     end
--   | (c :: cs) :=
--     -- We must discharge `c`.
--     do set_goals [c],
--       s.lemmas.enum.any_of $ λ e, { committed := cs, .. s }.apply e.1 e.2.1 tt >>= back_state.run
--   end

/-- Takes two sets of lemmas, 'progress' lemmas and 'finishing' lemmas.

    Progress lemmas should be applied whenever possible, regardless of new hypotheses.
    Finishing lemmas should be applied only as part of a sequence of applications that close the goals.

    `back` succeeds if at least one progress lemma was applied, or all goals are discharged.
    -/
meta def back (progress finishing : list expr) (limit : option ℕ) : tactic unit :=
do i ← back_state.init progress finishing limit,
   f ← run [i],
   f.completed.mmap (λ g, unify g.original g.synthetic),
   f.stashed.mmap   (λ g, unify g.original g.synthetic),
   set_goals (f.stashed.map(goal_mvar.original)),
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
(tk "with" *> (((λ n, (n, ff)) <$> ident_) <|> (tk "!" *> (λ n, (n, tt)) <$> ident_))*) <|> return []

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
           /- finishing lemmas -/ filter_excl $ extra_fi_lemmas ++ with_fi_lemmas ++ hypotheses ++ tagged_fi_lemmas)

meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_meta_var then some (unchecked_cast pexpr.mk_placeholder) else none)

namespace interactive

open interactive interactive.types expr

/--
`back` performs backwards reasoning, recursively applying lemmas against the goal.

Lemmas can be specified via an optional argument, e.g. as `back [foo, bar]`. Every lemma
tagged with an attribute `qux` may be included using the syntax `back using qux`.
Additionally, `back` always includes any lemmas tagged with the attribute `@[back]`,
and all local propositional hypotheses.

(If the goal is a proposition, `back` is more aggressive and includes all hypotheses. This
can be achieved in other cases using `back [*]`.)

Lemmas which were included because of the `@[back]` attribute, or local hypotheses,
can be excluded using the notation `back [-h]`.

Further, lemmas can be tagged with the `@[back!]` attribute, or appear in the arguments with
a leading `!`, e.g. as `back [!foo]` or `back using !qux`. The tactic `back` will return
successfully if it either discharges the goal, or applies at least one `!` lemma.
(More precisely, `back` will apply some non-empty and maximal collection of the lemmas,
subject to the condition that if any lemma not marked with `!` is applied, all resulting
subgoals are later dischargeed.)

Finally, the search depth can be controlled, e.g. as `back 5`. The default value is 100.

`back?` will print a trace message showing the term it constructed. (Possibly with placeholders,
for use with `refine`.)

`back` will apply lemmas even if this introduces new metavariables (so for example it is possible
to apply transitivity lemmas), but with the proviso that any subgoals containing metavariables must
be subsequently discharged in a single step.
-/
meta def back
  (trace : parse $ optional (tk "?")) (no_dflt : parse only_flag)
  (hs : parse back_arg_list) (wth : parse with_back_ident_list) (limit : parse (optional small_nat)) : tactic string :=
do g :: _ ← get_goals,
   (pr, fi) ← tactic.mk_assumption_set no_dflt hs wth,
   r ← focus1 $ (do
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
