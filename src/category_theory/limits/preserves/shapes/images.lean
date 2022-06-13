/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import category_theory.limits.shapes.images
import category_theory.limits.constructions.epi_mono

/-!
# Preserving images

In this file, we show that if a functor preserves span and cospan, then it preserves images.
-/


noncomputable theory

namespace category_theory

namespace preserves_image

open category_theory
open category_theory.limits

universes u₁ u₂ v₁ v₂

variables {A : Type u₁} {B : Type u₂} [category.{v₁} A] [category.{v₂} B]
variables [has_equalizers A] [has_images A]
variables [strong_epi_category B] [has_images B]
variables (L : A ⥤ B)
variables [Π {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), preserves_limit (cospan f g) L]
variables [Π {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), preserves_colimit (span f g) L]

/--
If a functor preserves span and cospan.
-/
def iso {X Y : A} (f : X ⟶ Y) : image (L.map f) ≅ L.obj (image f) :=
have aux1 : strong_epi_mono_factorisation (L.map f) :=
{ I := L.obj (limits.image f),
  m := L.map $ limits.image.ι _,
  m_mono := infer_instance,
  e := L.map $ factor_thru_image _,
  e_strong_epi := @@strong_epi_of_epi _ _ _ $
    @@category_theory.preserves_epi _ _ L _ _ _,
  fac' := by rw [←L.map_comp, limits.image.fac] },
is_image.iso_ext (image.is_image (L.map f)) aux1.to_mono_is_image

lemma factor_thru_image_comp_hom {X Y : A} (f : X ⟶ Y) :
  factor_thru_image (L.map f) ≫ (iso L f).hom =
  L.map (factor_thru_image f) :=
begin
  dunfold iso,
  erw [is_image.iso_ext_hom, is_image.fac_lift],
end

lemma hom_comp_map_image_ι {X Y : A} (f : X ⟶ Y) :
  (iso L f).hom ≫ L.map (image.ι f) = image.ι (L.map f) :=
begin
  dunfold iso,
  simp
end

lemma inv_comp_image_ι_map {X Y : A} (f : X ⟶ Y) :
  (iso L f).inv ≫ image.ι (L.map f) = L.map (image.ι f) :=
begin
  dunfold iso,
  simp,
end

end preserves_image

end category_theory
