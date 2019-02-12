-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.shapes.binary_products
import category_theory.limits.products

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables {C} {X Y : C}

-- FIXME can we use `def` here? with a `class` attribute?

variables (C)

@[class] def has_binary_products := has_products_of_shape two.{v} C
@[class] def has_binary_coproducts := has_coproducts_of_shape two.{v} C

variables {C}

@[class] def has_binary_product (X Y : C) := has_product.{v} (two.map X Y)
@[class] def has_binary_coproduct (X Y : C) := has_coproduct.{v} (two.map X Y)

instance has_binary_product_of_has_binary_products (X Y : C) [i : has_binary_products C] :
  has_binary_product X Y :=
i (two.map X Y)
instance has_binary_coproduct_of_has_binary_coproducts (X Y : C) [i : has_binary_coproducts C] :
  has_binary_coproduct X Y :=
i (two.map X Y)

-- These are defs because they do not necessarily give the nicest constructions.
def has_binary_products_of_has_products [i : has_products_of_shape two C] :
  has_binary_products C := i
def has_binary_product_of_has_product (X Y : C) [i : has_product.{v} (two.map X Y)] :
  has_binary_product X Y := i
def has_binary_coproducts_of_has_coproducts [i : has_coproducts_of_shape two C] :
  has_binary_coproducts C := i
def has_binary_coproduct_of_has_coproduct (X Y : C) [i : has_coproduct.{v} (two.map X Y)] :
  has_binary_coproduct X Y := i

def has_product_of_has_binary_product (X Y : C) [i : has_binary_product X Y] :
  has_product (two.map X Y) := i
def has_coproduct_of_has_binary_coproduct (X Y : C) [i : has_binary_coproduct X Y] :
  has_coproduct (two.map X Y) := i

variables (X Y)

section prod
variable [has_binary_product X Y]
local attribute [instance] has_product_of_has_binary_product has_limit_of_has_product

def prod.span : fan (two.map X Y) := has_product.fan.{v} (two.map X Y)
protected def prod : C := (prod.span.{v} X Y).X
def prod.fst : limits.prod X Y ⟶ X :=
(prod.span X Y).π.app two.left
def prod.snd : limits.prod X Y ⟶ Y :=
(prod.span X Y).π.app two.right

variables {X Y}

def prod.lift {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : P ⟶ limits.prod X Y :=
limit.lift _ (binary_fan fst snd)

@[simp] lemma prod.lift_fst {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : prod.lift fst snd ≫ prod.fst _ _ = fst :=
limit.lift_π (binary_fan fst snd) two.left
@[simp] lemma prod.lift_snd {P : C} (fst : P ⟶ X) (snd : P ⟶ Y) : prod.lift fst snd ≫ prod.snd _ _ = snd :=
limit.lift_π (binary_fan fst snd) two.right

def prod.map
  {U V : C} [has_binary_product U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  (limits.prod X Y) ⟶ (limits.prod U V) :=
pi.lift (λ b, two.cases_on b (prod.fst X Y ≫ fst) (prod.snd X Y ≫ snd))

@[simp] lemma prod.map_fst
  {U V : C} [has_binary_product U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  prod.map fst snd ≫ prod.fst U V = prod.fst X Y ≫ fst :=
by erw is_limit.fac; refl
@[simp] lemma prod.map_snd
  {U V : C} [has_binary_product U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  prod.map fst snd ≫ prod.snd U V = prod.snd X Y ≫ snd :=
by erw is_limit.fac; refl


@[extensionality] lemma prod.hom_ext
  {P : C} {g h : P ⟶ limits.prod X Y}
  (w_fst : g ≫ prod.fst X Y = h ≫ prod.fst X Y)
  (w_snd : g ≫ prod.snd X Y = h ≫ prod.snd X Y) : g = h :=
limit.hom_ext (λ j, two.cases_on j w_fst w_snd)

def prod.hom_iso {P : C} : (P ⟶ limits.prod X Y) ≅ (P ⟶ X) × (P ⟶ Y) :=
{ hom := λ g, (g ≫ prod.fst X Y, g ≫ prod.snd X Y),
  inv := λ p, prod.lift p.1 p.2 }

end prod

section sum
variable [has_binary_coproduct X Y]
local attribute [instance] has_coproduct_of_has_binary_coproduct has_colimit_of_has_coproduct

def sum.cospan : cofan (two.map X Y) := has_coproduct.cofan.{v} (two.map X Y)
protected def sum : C := (sum.cospan.{v} X Y).X
def sum.inl : X ⟶ limits.sum X Y :=
(sum.cospan X Y).ι.app two.left
def sum.inr : Y ⟶ limits.sum X Y :=
(sum.cospan X Y).ι.app two.right

variables {X Y}

def sum.desc {P : C} (left : X ⟶ P) (right : Y ⟶ P) : limits.sum X Y ⟶ P :=
colimit.desc _ (binary_cofan left right)

@[simp] lemma sum.desc_inl {P : C} (inl : X ⟶ P) (inr : Y ⟶ P) : sum.inl _ _ ≫ sum.desc inl inr = inl :=
colimit.ι_desc (binary_cofan inl inr) two.left
@[simp] lemma sum.desc_inr {P : C} (inl : X ⟶ P) (inr : Y ⟶ P) : sum.inr _ _ ≫ sum.desc inl inr = inr :=
colimit.ι_desc (binary_cofan inl inr) two.right

def sum.map
  {U V : C} [has_binary_coproduct U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  (limits.sum X Y) ⟶ (limits.sum U V) :=
sigma.desc (λ b, two.cases_on b (fst ≫ sum.inl U V) (snd ≫ sum.inr U V))

@[simp] lemma sum.map_inl
  {U V : C} [has_binary_coproduct U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  sum.inl X Y ≫ sum.map fst snd = fst ≫ sum.inl U V :=
by erw is_colimit.fac; refl
@[simp] lemma sum.map_inr
  {U V : C} [has_binary_coproduct U V] (fst : X ⟶ U) (snd : Y ⟶ V) :
  sum.inr X Y ≫ sum.map fst snd = snd ≫ sum.inr U V :=
by erw is_colimit.fac; refl

@[extensionality] lemma sum.hom_ext
  {P : C} {g h : limits.sum X Y ⟶ P}
  (w_fst : sum.inl X Y ≫ g = sum.inl X Y ≫ h)
  (w_snd : sum.inr X Y ≫ g = sum.inr X Y ≫ h) : g = h :=
colimit.hom_ext (λ j, two.cases_on j w_fst w_snd)

def sum.hom_iso {P : C} : (limits.sum X Y ⟶ P) ≅ (X ⟶ P) × (Y ⟶ P) :=
{ hom := λ g, (sum.inl X Y ≫ g, sum.inr X Y ≫ g),
  inv := λ p, sum.desc p.1 p.2 }

end sum

-- TODO many things

-- pullbacks from binary_products and equalizers
-- finite products from binary_products and terminal objects

end category_theory.limits
