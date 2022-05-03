/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.shapes.kernels
import category_theory.abelian.basic

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop` valued typeclass `simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/

noncomputable theory

open category_theory.limits

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]

section
variables [has_zero_morphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class simple (X : C) : Prop :=
(mono_is_iso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [mono f], is_iso f ↔ (f ≠ 0))

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
lemma is_iso_of_mono_of_nonzero {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : f ≠ 0) :
  is_iso f :=
(simple.mono_is_iso_iff_nonzero f).mpr w

lemma simple.of_iso {X Y : C} [simple Y] (i : X ≅ Y) : simple X :=
{ mono_is_iso_iff_nonzero := λ Z f m, begin
    resetI,
    haveI : mono (f ≫ i.hom) := mono_comp _ _,
    split,
    { introsI h w,
      haveI j : is_iso (f ≫ i.hom), apply_instance,
      rw simple.mono_is_iso_iff_nonzero at j,
      unfreezingI { subst w, },
      simpa using j, },
    { intro h,
      haveI j : is_iso (f ≫ i.hom),
      { apply is_iso_of_mono_of_nonzero,
        intro w, apply h,
        simpa using (cancel_mono i.inv).2 w, },
      rw [←category.comp_id f, ←i.hom_inv_id, ←category.assoc],
      apply_instance, },
  end }

lemma kernel_zero_of_nonzero_from_simple
  {X Y : C} [simple X] {f : X ⟶ Y} [has_kernel f] (w : f ≠ 0) :
  kernel.ι f = 0 :=
begin
  classical,
  by_contra,
  haveI := is_iso_of_mono_of_nonzero h,
  exact w (eq_zero_of_epi_kernel f),
end

lemma mono_to_simple_zero_of_not_iso
  {X Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : is_iso f → false) : f = 0 :=
begin
  classical,
  by_contra,
  exact w (is_iso_of_mono_of_nonzero h)
end

lemma id_nonzero (X : C) [simple.{v} X] : 𝟙 X ≠ 0 :=
(simple.mono_is_iso_iff_nonzero (𝟙 X)).mp (by apply_instance)

instance (X : C) [simple.{v} X] : nontrivial (End X) :=
nontrivial_of_ne 1 0 (id_nonzero X)

section
variable [has_zero_object C]
open_locale zero_object

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
lemma zero_not_simple [simple (0 : C)] : false :=
(simple.mono_is_iso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by tidy⟩⟩ rfl

end
end

-- We next make the dual arguments, but for this we must be in an abelian category.
section abelian
variables [abelian C]

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
lemma simple_of_cosimple (X : C) (h : ∀ {Z : C} (f : X ⟶ Z) [epi f], is_iso f ↔ (f ≠ 0)) :
  simple X :=
⟨λ Y f I,
 begin
  classical,
  fsplit,
  { introsI,
    have hx := cokernel.π_of_epi f,
    by_contra,
    substI h,
    exact (h _).mp (cokernel.π_of_zero _ _) hx },
  { intro hf,
    suffices : epi f,
    { exactI is_iso_of_mono_of_epi _ },
    apply preadditive.epi_of_cokernel_zero,
    by_contra h',
    exact cokernel_not_iso_of_nonzero hf ((h _).mpr h') }
 end⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
lemma is_iso_of_epi_of_nonzero {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : f ≠ 0) :
  is_iso f :=
begin
  -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  haveI : mono f :=
    preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w)),
  exact is_iso_of_mono_of_epi f,
end

lemma cokernel_zero_of_nonzero_to_simple
  {X Y : C} [simple Y] {f : X ⟶ Y} (w : f ≠ 0) :
  cokernel.π f = 0 :=
begin
  classical,
  by_contradiction h,
  haveI := is_iso_of_epi_of_nonzero h,
  exact w (eq_zero_of_mono_cokernel f),
end

lemma epi_from_simple_zero_of_not_iso
  {X Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : is_iso f → false) : f = 0 :=
begin
  classical,
  by_contra,
  exact w (is_iso_of_epi_of_nonzero h),
end

end abelian

section
variables [preadditive C] [has_binary_biproducts C]

-- There are another three potential variations of this lemma,
-- but as any one suffices to prove `indecomposable_of_simple` we will not give them all.
lemma biprod.is_iso_inl_iff_is_zero (X Y : C) : is_iso (biprod.inl : X ⟶ X ⊞ Y) ↔ is_zero Y :=
begin
  rw [biprod.is_iso_inl_iff_id_eq_fst_comp_inl, ←biprod.total, add_right_eq_self],
  split,
  { intro h, replace h := h =≫ biprod.snd,
    simpa [←is_zero.iff_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h, },
  { intro h, rw is_zero.iff_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y) at h, rw [h, zero_comp], },
end

/-- Any simple object in a preadditive category is indecomposable. -/
lemma indecomposable_of_simple (X : C) [simple X] : indecomposable X :=
λ Y Z i, begin
  refine or_iff_not_imp_left.mpr (λ h, _),
  rw is_zero.iff_split_mono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z) at h,
  change biprod.inl ≠ 0 at h,
  rw ←(simple.mono_is_iso_iff_nonzero biprod.inl) at h,
  { rwa biprod.is_iso_inl_iff_is_zero at h, },
  { exact simple.of_iso i.symm, },
  { apply_instance, },
end

end

end category_theory
