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
# The Mittag-Leffler condition

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.is_mittag_leffler` states that the functor `F` satisfies the Mittag-Leffler
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

universes u v

-- Two lemmas that should go into order.directed
lemma directed_on_range {α β} {r : α → α → Prop} {f : β → α} :
  directed r f ↔ directed_on r (set.range f) :=
by simp_rw [directed, directed_on, set.forall_range_iff, set.exists_range_iff]

private lemma directed_on.is_bot_of_is_min {J : Type u} {s : set J} [preorder J]
  (h : directed_on (≥) s) (m ∈ s) (min : ∀ (a ∈ s), a ≤ m → m ≤ a) : ∀ a ∈ s, m ≤ a :=
λ a as, let ⟨x, xs, xm, xa⟩ := h m H a as in (min x xs xm).trans xa

namespace category_theory
namespace functor

variables {J : Type u} [category J] (F : J ⥤ Type v) {i j k : J} (s : set (F.obj i))

/- to remove -/
lemma _root_.category_theory.is_cofiltered.cone_over_cospan
  {J : Type u} [category J] [is_cofiltered_or_empty J] {i j j' : J} (f : j ⟶ i) (f' : j' ⟶ i) :
  ∃ (k : J) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
let ⟨k', h, h', _⟩ := is_cofiltered_or_empty.cocone_objs j j',
    ⟨k, G, he⟩ := is_cofiltered_or_empty.cocone_maps (h ≫ f) (h' ≫ f') in
⟨k, G ≫ h, G ≫ h', by simpa only [category.assoc]⟩

open is_cofiltered set functor_to_types

/--
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventual_range (j : J) := ⋂ i (f : i ⟶ j), range (F.map f)

lemma mem_eventual_range_iff {x : F.obj j} :
  x ∈ F.eventual_range j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) := mem_Inter₂

/--
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def is_mittag_leffler : Prop :=
∀ j : J, ∃ i (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)

lemma is_mittag_leffler_iff_eventual_range : F.is_mittag_leffler ↔
  ∀ j : J, ∃ i (f : i ⟶ j), F.eventual_range j = range (F.map f) :=
forall_congr $ λ j, exists₂_congr $ λ i f,
  ⟨λ h, (Inter₂_subset _ _).antisymm $ subset_Inter₂ h, λ h, h ▸ Inter₂_subset⟩

lemma is_mittag_leffler.subset_image_eventual_range (h : F.is_mittag_leffler) (f : j ⟶ i) :
  F.eventual_range i ⊆ F.map f '' (F.eventual_range j) :=
begin
  obtain ⟨k, g, hg⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j,
  rw hg, intros x hx,
  obtain ⟨x, rfl⟩ := F.mem_eventual_range_iff.1 hx (g ≫ f),
  refine ⟨_, ⟨x, rfl⟩, by simpa only [F.map_comp]⟩,
end

lemma eventual_range_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
  (h : F.eventual_range k = range (F.map g)) :
  F.eventual_range k = range (F.map $ f ≫ g) :=
begin
  apply subset_antisymm,
  { apply Inter₂_subset, },
  { rw [h, F.map_comp], apply range_comp_subset_range, }
end

lemma is_mittag_leffler_of_surjective
  (h : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) : F.is_mittag_leffler :=
λ j, ⟨j, 𝟙 j, λ k g, by rw [map_id, types_id, range_id, (h k j g).range_eq]⟩

@[simps] def restrict : J ⥤ Type v :=
{ obj := λ j, ⋂ f : j ⟶ i, F.map f ⁻¹' s,
  map := λ j k g, maps_to.restrict (F.map g) _ _ $ λ x h, begin
    rw [mem_Inter] at h ⊢, intro f,
    rw [← mem_preimage, preimage_preimage],
    convert h (g ≫ f), rw F.map_comp, refl,
  end,
  map_id' := λ j, by { simp_rw F.map_id, ext, refl },
  map_comp' := λ j k l f g, by { simp_rw F.map_comp, refl } }

variable [is_cofiltered_or_empty J]

lemma eventual_range_maps_to (f : j ⟶ i) :
  (F.eventual_range j).maps_to (F.map f) (F.eventual_range i) :=
λ x hx, begin
  rw mem_eventual_range_iff at hx ⊢,
  intros k f',
  obtain ⟨l, g, g', he⟩ := cone_over_cospan f f',
  obtain ⟨x, rfl⟩ := hx g,
  rw [← map_comp_apply, he, F.map_comp],
  exact ⟨_, rfl⟩,
end

lemma is_mittag_leffler.eq_image_eventual_range (h : F.is_mittag_leffler)
  (f : j ⟶ i) : F.eventual_range i = F.map f '' (F.eventual_range j) :=
(h.subset_image_eventual_range F f).antisymm $ maps_to'.1 (F.eventual_range_maps_to f)

lemma is_mittag_leffler_iff_subset_range_comp : F.is_mittag_leffler ↔
  ∀ j : J, ∃ i (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map $ g ≫ f) :=
begin
  refine forall_congr (λ j, exists₂_congr $ λ i f, ⟨λ h k g, h _, λ h j' f', _⟩),
  obtain ⟨k, g, g', he⟩ := cone_over_cospan f f',
  refine (h g).trans _,
  rw [he, F.map_comp],
  apply range_comp_subset_range,
end

lemma is_mittag_leffler.restrict (h : F.is_mittag_leffler) :
  (F.restrict s).is_mittag_leffler :=
(is_mittag_leffler_iff_subset_range_comp _).2 $ λ j, begin
  obtain ⟨j₁, g₁, f₁, -⟩ := is_cofiltered_or_empty.cocone_objs i j,
  obtain ⟨j₂, f₂, h₂⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j₁,
  refine ⟨j₂, f₂ ≫ f₁, λ j₃ f₃, _⟩,
  rintro _ ⟨⟨x, hx⟩, rfl⟩,
  have : F.map f₂ x ∈ F.eventual_range j₁, { rw h₂, exact ⟨_, rfl⟩ },
  obtain ⟨y, hy, h₃⟩ := h.subset_image_eventual_range F (f₃ ≫ f₂) this,
  refine ⟨⟨y, mem_Inter.2 $ λ g₂, _⟩, _⟩,
  { obtain ⟨j₄, f₄, h₄⟩ := is_cofiltered_or_empty.cocone_maps g₂ ((f₃ ≫ f₂) ≫ g₁),
    obtain ⟨y, rfl⟩ := F.mem_eventual_range_iff.1 hy f₄,
    rw ← map_comp_apply at h₃,
    rw [mem_preimage, ← map_comp_apply, h₄, ← category.assoc, map_comp_apply, h₃, ← map_comp_apply],
    apply mem_Inter.1 hx },
  { ext1, simp_rw [restrict_map, maps_to.coe_restrict_apply, subtype.coe_mk],
    rw [← category.assoc, map_comp_apply, h₃, map_comp_apply] },
end

lemma range_directed_of_is_cofiltered (j : J) :
  directed (⊇) (λ f : Σ' i, i ⟶ j, range (F.map f.2)) :=
begin
  rintros ⟨i, ij⟩ ⟨k, kj⟩,
  obtain ⟨l, li, lk, e⟩ := cone_over_cospan ij kj,
  refine ⟨⟨l, li ≫ ij⟩, _, _⟩, swap 2, rw e,
  all_goals { simp_rw F.map_comp, apply range_comp_subset_range, },
end

lemma is_mittag_leffler_of_exists_finite_range
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (range (F.map f)).finite) :
  F.is_mittag_leffler :=
begin
  rintro j,
-- trying to use `well_founded.has_min`
  suffices : ∃ (f : Σ' i, i ⟶ j), ∀ (f' : Σ' i, i ⟶ j),
               range (F.map f'.2) ≤ range (F.map f.2) →
                 range (F.map f'.2) = range (F.map f.2),
  { obtain ⟨⟨i, f⟩, fmin⟩ := this,
    refine ⟨i, f, λ i' f', _⟩,
    have := (directed_on_range.mp $ F.range_directed_of_is_cofiltered j).is_bot_of_is_min,
    sorry,
    refine directed_on_min (F.ranges_directed_of_is_cofiltered j) _ ⟨⟨i, f⟩,rfl⟩ _ _ ⟨⟨i',f'⟩,rfl⟩,
    simp only [mem_range, psigma.exists, forall_exists_index],
    rintro _ k g rfl gf,
    exact fmin ⟨k,g⟩ gf, },

  let fins := subtype { f : Σ' i, i ⟶ j | (range (F.map f.2)).finite },
  haveI : nonempty fins := by { obtain ⟨i,f,fin⟩ := h j, exact ⟨⟨⟨i,f⟩,fin⟩⟩, },
  let fmin := function.argmin (λ (f : fins), f.prop.to_finset.card) nat.lt_wf,
  use fmin.val,
  rintro g gf,
  cases lt_or_eq_of_le gf,
  { have gfin : (range (F.map g.2)).finite := fmin.prop.subset gf,
    refine ((λ (f : fins), f.prop.to_finset.card).not_lt_argmin nat.lt_wf ⟨g, gfin⟩ _).elim,
    exact finset.card_lt_card (set.finite.to_finset_ssubset.mpr h_1), },
  { assumption, },
end

/--
The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
def to_eventual_ranges : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, (F.eventual_range_maps_to f).restrict _ _ _,
  map_id' := λ i, by { simp_rw F.map_id, ext, refl },
  map_comp' := λ _ _ _ _ _, by { simp_rw F.map_comp, refl } }

/--
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def to_eventual_ranges_sections_equiv : F.to_eventual_ranges.sections ≃ F.sections :=
{ to_fun := λ ss, ⟨_, λ i j f, subtype.coe_inj.2 $ ss.prop f⟩,
  inv_fun := λ s, ⟨λ j, ⟨_, mem_Inter₂.2 $ λ i f, ⟨_, s.prop f⟩⟩, λ i j f, subtype.ext $ s.prop f⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl } }

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
lemma surjective_to_eventual_ranges (h : F.is_mittag_leffler) (i j : J) (f : i ⟶ j) :
  (F.to_eventual_ranges.map f).surjective :=
λ ⟨x, hx⟩, by { obtain ⟨y, hy, rfl⟩ := h.subset_image_eventual_range F f hx, exact ⟨⟨y, hy⟩, rfl⟩ }

end functor
end category_theory
