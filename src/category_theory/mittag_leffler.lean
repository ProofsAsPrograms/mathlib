/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.fintype.basic
import category_theory.types

/-!
# Mittag Leffler

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given the functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `is_mittag_leffler` states that the functor `F : J → Type v`, satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.


## Main statements

* `is_mittag_leffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `to_eventual_ranges_surjective` shows that if `F` is Mittag-Leffler, then `F.to_eventual_ranges`
  has all morphisms `F.map f` surjective.

## Todo

* Specialize to inverse systems and fintype systems.
* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/


universes u v w


-- Two lemmas that should go into order.directed
lemma directed_on_range {α β} {r : α → α → Prop} {f : β → α} :
  directed r f ↔ directed_on r (set.range f) :=
by simp_rw [directed, directed_on, set.forall_range_iff, set.exists_range_iff]

--⟨by { rintro h _ ⟨x, rfl⟩ _ ⟨y, rfl⟩, obtain ⟨z, hx, hy⟩ := h x y, exact ⟨_, ⟨z, rfl⟩, hx, hy⟩ },
--  λ h x y, by { obtain ⟨_, ⟨z, rfl⟩, hx, hy⟩ := h _ ⟨x, rfl⟩ _ ⟨y, rfl⟩, exact ⟨z, hx, hy⟩ }⟩

private lemma directed_on.is_bot_of_is_min {J : Type u} {s : set J} [preorder J]
  (h : directed_on (≥) s) (m ∈ s) (min : ∀ (a ∈ s), a ≤ m → m ≤ a) : ∀ a ∈ s, m ≤ a :=
λ a as, let ⟨x, xs, xm, xa⟩ := h m H a as in (min x xs xm).trans xa
-- this is very similar to `is_min.is_bot`, so I changed the hypothesis `min` to match `is_min`.

namespace category_theory
namespace functor

/--
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventual_range
  {J : Type u} [category J] (F : J ⥤ Type v) (j : J) :=
⋂ (i : J) (f : i ⟶ j), set.range (F.map f)

/--
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def is_mittag_leffler
  {J : Type u} [category J] (F : J ⥤ Type v) : Prop :=
∀ (j : J), ∃ (i) (f : i ⟶ j), ∀ (k) (g : k ⟶ j), set.range (F.map f) ⊆ set.range (F.map g)
--might consider ∀ j : J, ∃ i (f : i ⟶ j), ∀ k (g : k ⟶ j) (x : F.obj i), ∃ y : F.obj k, F.map g y = F.map f x

lemma is_mittag_leffler_iff_eventual_range
  {J : Type u} [category J] (F : J ⥤ Type v) :
  F.is_mittag_leffler ↔ ∀ (j : J), ∃ (i) (f : i ⟶ j), F.eventual_range j = set.range (F.map f) :=
forall_congr $ λ j, exists₂_congr $ λ i f,
  ⟨λ h, (set.Inter₂_subset _ _).antisymm $ set.subset_Inter₂ h, λ h, h ▸ set.Inter₂_subset⟩

lemma eventual_range_eq_range_precomp
  {J : Type u} [category J] (F : J ⥤ Type v)
  {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (h : F.eventual_range k = set.range (F.map g)) :
  F.eventual_range k = set.range (F.map $ f ≫ g) :=
begin
  apply subset_antisymm,
  { apply set.Inter₂_subset, },
  { rw [h, F.map_comp], apply set.range_comp_subset_range, }
end

lemma is_mittag_leffler_of_surjective
  {J : Type u} [category J] (F : J ⥤ Type v)
  (h : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) : F.is_mittag_leffler :=
λ j, ⟨j, 𝟙 j, λ k g, by rw [map_id, types_id, set.range_id, (h k j g).range_eq]⟩

lemma _root_.category_theory.is_cofiltered.cone_over_cospan
  {J : Type u} [category J] [is_cofiltered_or_empty J] {i j j' : J} (f : j ⟶ i) (f' : j' ⟶ i) :
  ∃ (k : J) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
-- This is shorter:
let ⟨k', h, h', _⟩ := is_cofiltered_or_empty.cocone_objs j j',
    ⟨k, G, he⟩ := is_cofiltered_or_empty.cocone_maps (h ≫ f) (h' ≫ f') in
⟨k, G ≫ h, G ≫ h', by simpa only [category.assoc]⟩
-- This should surely go into category_theory.filtered; I don't understand why most results there
-- are stated with `is_cofiltered` rather than `is_cofiltered_or_empty` though. Maybe because the former is shorter?

section
variables {J : Type u} [category J] (F : J ⥤ Type v) {i j : J} (s : set (F.obj i))

lemma is_mittag_leffler_iff_subset_range_comp [is_cofiltered_or_empty J] :
  F.is_mittag_leffler ↔
  ∀ j : J, ∃ i (f : i ⟶ j), ∀ k (g : k ⟶ i), set.range (F.map f) ⊆ set.range (F.map $ g ≫ f) :=
begin
  refine forall_congr (λ j, exists₂_congr $ λ i f, ⟨λ h k g, h k _, λ h j' f', _⟩),
  obtain ⟨k, g, g', he⟩ := is_cofiltered.cone_over_cospan f f',
  refine (h k g).trans _,
  rw [he, F.map_comp],
  apply set.range_comp_subset_range,
end

lemma is_mittag_leffler.mem_image_eventual_range (h : F.is_mittag_leffler) {x}
  (hx : x ∈ F.eventual_range i) (f : j ⟶ i) : ∃ y ∈ F.eventual_range j, F.map f y = x :=
begin
  rw is_mittag_leffler_iff_eventual_range at h,
  obtain ⟨k, g, hg⟩ := h j, simp_rw hg,
  obtain ⟨x, rfl⟩ := set.mem_Inter₂.1 hx k (g ≫ f),
  refine ⟨_, ⟨x, rfl⟩, by simpa only [F.map_comp]⟩,
end

@[simps] def restrict : J ⥤ Type v :=
{ obj := λ j, ⋂ f : j ⟶ i, F.map f ⁻¹' s,
  map := λ j k g, set.maps_to.restrict (F.map g) _ _ $ λ x h, begin
    rw [set.mem_Inter] at h ⊢, intro f,
    rw [← set.mem_preimage, set.preimage_preimage],
    convert h (g ≫ f), rw F.map_comp, refl,
  end,
  map_id' := λ j, by { simp_rw F.map_id, ext, refl },
  map_comp' := λ j k l f g, by { simp_rw F.map_comp, refl } }

lemma is_mittag_leffler.restrict [is_cofiltered_or_empty J] (h : F.is_mittag_leffler) :
  (F.restrict s).is_mittag_leffler :=
(is_mittag_leffler_iff_subset_range_comp _).2 $ λ j, begin
  obtain ⟨k, g₁, f₁, -⟩ := is_cofiltered_or_empty.cocone_objs i j,
  obtain ⟨l, f₂, h₂⟩ := F.is_mittag_leffler_iff_eventual_range.1 h k,
  refine ⟨l, f₂ ≫ f₁, λ m f₃, _⟩,
  rintro _ ⟨x, rfl⟩,
  have : F.map f₂ x.1 ∈ F.eventual_range k, { rw h₂, exact ⟨_, rfl⟩ },
  obtain ⟨y, hy, h₃⟩ := h.mem_image_eventual_range F this (f₃ ≫ f₂),
  refine ⟨⟨y, set.mem_Inter.2 $ λ g₂, _⟩, _⟩,
  { obtain ⟨m, f₄, h₄⟩ := is_cofiltered_or_empty.cocone_maps g₂ ((f₃ ≫ f₂) ≫ g₁),
    obtain ⟨y, rfl⟩ := set.mem_Inter₂.1 hy m f₄,
    rw [set.mem_preimage, ← function.comp_apply (F.map _), ← types_comp, ← F.map_comp, h₄],
    simp_rw [F.map_comp, types_comp, function.comp_apply] at h₃ ⊢,
    rw [h₃, ← function.comp_apply (F.map _), ← types_comp, ← F.map_comp],
    apply set.mem_Inter.1 x.2 },
  { ext1, simp_rw [restrict_map, set.maps_to.coe_restrict_apply, subtype.coe_mk],
    rw [← category.assoc, F.map_comp, types_comp, function.comp_apply, h₃, F.map_comp], refl },
end

end

lemma range_directed_of_is_cofiltered
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (j : J) :
  directed (⊇) (λ f : Σ' i, i ⟶ j, set.range (F.map f.2)) :=
begin
  rintros ⟨i, ij⟩ ⟨k, kj⟩,
  obtain ⟨l, li, lk, e⟩ := category_theory.is_cofiltered.cone_over_cospan ij kj,
  refine ⟨⟨l, li ≫ ij⟩, _, _⟩, swap 2, rw e,
  all_goals { simp_rw F.map_comp, apply set.range_comp_subset_range, },
end

lemma is_mittag_leffler_of_exists_finite_range
  {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (set.range (F.map f)).finite) :
  F.is_mittag_leffler :=
begin
  rintro j,
-- trying to use `well_founded.has_min`
  suffices : ∃ (f : Σ' i, i ⟶ j), ∀ (f' : Σ' i, i ⟶ j),
               set.range (F.map f'.2) ≤ set.range (F.map f.2) →
                 set.range (F.map f'.2) = set.range (F.map f.2),
  { obtain ⟨⟨i, f⟩, fmin⟩ := this,
    refine ⟨i, f, λ i' f', _⟩,
    have := (directed_on_range.mp $ F.range_directed_of_is_cofiltered j).is_bot_of_is_min,
    sorry,
    refine directed_on_min (F.ranges_directed_of_is_cofiltered j) _ ⟨⟨i, f⟩,rfl⟩ _ _ ⟨⟨i',f'⟩,rfl⟩,
    simp only [set.mem_range, psigma.exists, forall_exists_index],
    rintro _ k g rfl gf,
    exact fmin ⟨k,g⟩ gf, },

  let fins := subtype { f : Σ' i, i ⟶ j | (set.range (F.map f.2)).finite },
  haveI : nonempty fins := by { obtain ⟨i,f,fin⟩ := h j, exact ⟨⟨⟨i,f⟩,fin⟩⟩, },
  let fmin := function.argmin (λ (f : fins), f.prop.to_finset.card) nat.lt_wf,
  use fmin.val,
  rintro g gf,
  cases lt_or_eq_of_le gf,
  { have gfin : (set.range (F.map g.2)).finite := fmin.prop.subset gf,
    refine ((λ (f : fins), f.prop.to_finset.card).not_lt_argmin nat.lt_wf ⟨g, gfin⟩ _).elim,
    exact finset.card_lt_card (set.finite.to_finset_ssubset.mpr h_1), },
  { assumption, },
end

/--
The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
def to_eventual_ranges
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, set.maps_to.restrict (F.map f) _ _ ( by
    { rintro x h,
      simp only [eventual_range, set.mem_Inter, set.mem_range] at h ⊢,
      rintro i' f',
      obtain ⟨l, g, g', e⟩ := category_theory.is_cofiltered.cone_over_cospan f f',
      obtain ⟨z,rfl⟩ := h l g,
      use F.map g' z,
      replace e := congr_fun (congr_arg F.map e) z,
      simp_rw functor_to_types.map_comp_apply at e,
      exact e.symm, } ),
  map_id' := by
    { rintros, ext,
      simp only [set.maps_to.coe_restrict_apply, types_id_apply, map_id], },
  map_comp' := by
    { intros, ext,
      simp only [functor.map_comp, set.maps_to.coe_restrict_apply, types_comp_apply], }, }

/--
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def to_eventual_ranges_sections_equiv
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) :
  F.to_eventual_ranges.sections ≃ F.sections :=
{ to_fun := λ ss,
    ⟨ λ j, (ss.val j).val,
      λ i j f, by simpa only [←subtype.coe_inj, subtype.coe_mk] using ss.prop f ⟩,
  inv_fun := λ s,
    ⟨ λ j,
      ⟨ s.val j, by
        { dsimp [eventual_range],
          simp only [set.mem_Inter, set.mem_range],
          exact λ i f, ⟨s.val i, s.prop f⟩, } ⟩,
      λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij)⟩,
  left_inv := by
    { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall,
                 subtype.coe_mk, subtype.coe_eta, eq_self_iff_true, implies_true_iff], },
  right_inv := by
    { simp only [function.left_inverse, function.right_inverse, eq_self_iff_true, set_coe.forall,
                 implies_true_iff, subtype.coe_mk], } }

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
lemma to_eventual_ranges_surjective
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (ml : F.is_mittag_leffler) :
  ∀ (i j : J) (f : i ⟶ j), (F.to_eventual_ranges.map f).surjective :=
begin
  rintros i j f ⟨x,hx⟩,
  rw is_mittag_leffler_iff_eventual_range at ml,
  obtain ⟨i₀,ii₀,ei₀⟩ := ml i,
  obtain ⟨j₀,jj₀,ej₀⟩ := ml j,
  obtain ⟨k,ki₀,kj₀,e⟩ := category_theory.is_cofiltered.cone_over_cospan (ii₀ ≫ f) jj₀,
  dsimp only [to_eventual_ranges],
  simp only [set_coe.exists],
  let ei := F.eventual_range_eq_range_precomp ki₀ ii₀ ei₀,
  let ej := F.eventual_range_eq_range_precomp kj₀ jj₀ ej₀,
  obtain ⟨z,rfl⟩ := ej.rec_on hx,
  use F.map (ki₀ ≫ ii₀) z,
  simp_rw [ei, set.mem_range_self, exists_true_left, ←e, functor_to_types.map_comp_apply],
  refl,
end

end functor
end category_theory
