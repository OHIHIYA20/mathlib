-- Copyright (c) 2018 Reid Barton. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Reid Barton, Scott Morrison

import category_theory.isomorphism
import category_theory.functor_category

universes v v' u u' -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def eq_to_hom {X Y : C} (p : X = Y) : X ⟶ Y := by rw p; exact 𝟙 _

@[simp] lemma eq_to_hom_refl (X : C) (p : X = X) : eq_to_hom p = 𝟙 X := rfl
@[simp] lemma eq_to_hom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_hom p ≫ eq_to_hom q = eq_to_hom (p.trans q) :=
by cases p; cases q; simp
@[simp] lemma eq_to_hom_trans_assoc {X Y Z W : C} (p : X = Y) (q : Y = Z) (f : Z ⟶ W) :
  eq_to_hom p ≫ (eq_to_hom q ≫ f) = eq_to_hom (p.trans q) ≫ f :=
by cases p; cases q; simp

def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y :=
⟨eq_to_hom p, eq_to_hom p.symm, by simp, by simp⟩

@[simp] lemma eq_to_iso.hom {X Y : C} (p : X = Y) : (eq_to_iso p).hom = eq_to_hom p :=
rfl

@[simp] lemma eq_to_iso_refl (X : C) (p : X = X) : eq_to_iso p = iso.refl X := rfl
@[simp] lemma eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_iso p ≪≫ eq_to_iso q = eq_to_iso (p.trans q) :=
by ext; simp

variables {D : Type u'} [𝒟 : category.{v'} D]
include 𝒟

namespace functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
lemma ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ X Y f, F.map f = eq_to_hom (h_obj X) ≫ G.map f ≫ eq_to_hom (h_obj Y).symm) :
  F = G :=
begin
  cases F with F_obj _ _ _, cases G with G_obj _ _ _,
  have : F_obj = G_obj, by ext X; apply h_obj,
  subst this,
  congr,
  funext X Y f,
  simpa using h_map X Y f
end

-- Using equalities between functors.

lemma congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X :=
by subst h

lemma congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f = eq_to_hom (congr_obj h X) ≫ G.map f ≫ eq_to_hom (congr_obj h Y).symm :=
by subst h; simp

end functor

@[simp] lemma eq_to_hom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
  F.map (eq_to_hom p) = eq_to_hom (congr_arg F.obj p) :=
by cases p; simp

@[simp] lemma eq_to_iso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
  F.on_iso (eq_to_iso p) = eq_to_iso (congr_arg F.obj p) :=
by ext; cases p; simp

@[simp] lemma eq_to_hom_app {F G : C ⥤ D} (h : F = G) (X : C) :
  (eq_to_hom h : F ⟹ G).app X = eq_to_hom (functor.congr_obj h X) :=
by subst h; refl

end category_theory
