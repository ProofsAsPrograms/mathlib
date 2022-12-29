/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import combinatorics.additive.mathlib
import tactic.linarith

/-!
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`.

## Main declarations

* `finset.mul_stab`: The stabilizer of a **nonempty** finset as a finset.
* `finset.mul_kneser`: Kneser's theorem.

## References

* [Imre Ruzsa, *Sumsets and structure][ruzsa2009]
-/

open function mul_action
open_locale classical pointwise

variables {α : Type*} [comm_group α] [decidable_eq α] {s s' t t' C : finset α} {a b : α}

namespace finset

/-! ### Auxiliary results -/

@[to_additive]
lemma mul_stab_mul_ssubset_mul_stab (hs₁ : (s ∩ a • C.mul_stab).nonempty)
  (ht₁ : (t ∩ b • C.mul_stab).nonempty) (hab : ¬ (a * b) • C.mul_stab ⊆ s * t) :
  ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab ⊂ C.mul_stab :=
begin
  have hCne : C.nonempty,
  { contrapose! hab,
    simp only [not_nonempty_iff_eq_empty] at hab,
    simp only [hab, mul_stab_empty, smul_finset_empty, empty_subset] },
  obtain ⟨x, hx⟩ := hs₁,
  obtain ⟨y, hy⟩ := ht₁,
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx),
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy),
  have hsubset : ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab ⊆ C.mul_stab,
  { have hxymem : x * y ∈ s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab) := mul_mem_mul hx hy,
    apply subset_trans (mul_stab_subset_div_right hxymem),
    have : s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab) ⊆ (x * y) • C.mul_stab,
    { apply subset_trans (mul_subset_mul (inter_subset_right s _) (inter_subset_right t _)),
      rw smul_mul_smul,
      rw [← hac, ← had, smul_mul_smul, smul_assoc],
      apply smul_finset_subset_smul_finset,
      rw [← smul_smul],
      rw mul_subset_iff,
      intros x hx y hy,
      rw [smul_mul_stab hd, smul_mul_stab hc, mem_mul_stab hCne, ← smul_smul,
        (mem_mul_stab hCne).mp hy, (mem_mul_stab hCne).mp hx] },
    apply subset_trans (div_subset_div_right this) _,
    have hsing : (x * y) • C.mul_stab = {x * y} * C.mul_stab,
    { rw singleton_mul; refl},
    simp_rw [hsing, singleton_mul, div_singleton, image_image, div_eq_mul_inv, comp,
      mul_comm _ (x * y)⁻¹, ← mul_assoc, mul_assoc, inv_mul_self (x * y), one_mul_eq_id, image_id,
      subset_refl] },
  have : (a * b) • C.mul_stab = ((a * c) * (b * d)) • C.mul_stab,
  { rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_self (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mul_stab hc, smul_mul_stab hd] },
  have hsub : (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)) ⊆ (a * b) • C.mul_stab,
  { apply subset_trans (mul_subset_mul (inter_subset_right s _) (inter_subset_right t _)),
    simp only [smul_mul_smul, mul_stab_mul_mul_stab, subset_refl] },
  have hxy : x * y ∈ (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab) := mul_mem_mul hx hy,
  rw this at hsub,
  rw this at hab,
  obtain ⟨z, hz, hzst⟩ := (not_subset _ _).mp hab,
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz,
  refine (finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, _⟩,
  rw mem_mul_stab' ⟨x * y, hxy⟩,
  push_neg,
  refine ⟨(a * c * (b * d)), by convert hxy, _⟩,
  rw [smul_eq_mul, mul_comm, ← smul_eq_mul, hwz],
  exact not_mem_mono (mul_subset_mul (inter_subset_left s _) (inter_subset_left t _)) hzst
end

@[to_additive]
lemma mul_stab_union (hs₁ : (s ∩ a • C.mul_stab).nonempty) (ht₁ : (t ∩ b • C.mul_stab).nonempty)
  (hab : ¬ (a * b) • C.mul_stab ⊆ s * t)
  (hC : disjoint C ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab))) :
  (C ∪ (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab
    = ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab :=
begin
  obtain rfl | hCne := C.eq_empty_or_nonempty,
  { simp [hs₁] },
  refine ((subset_inter (mul_stab_mul_ssubset_mul_stab hs₁ ht₁ hab).subset subset.rfl).trans
    inter_mul_stab_subset_mul_stab_union).antisymm' (λ x hx, _),
  replace hx := (mem_mul_stab (nonempty.mono (subset_union_right _ _) (hs₁.mul ht₁))).mp hx,
  rw smul_finset_union at hx,
  suffices hxC : x ∈ C.mul_stab,
  { rw (mem_mul_stab hCne).mp hxC at hx,
    rw mem_mul_stab_iff_subset_smul_finset (hs₁.mul ht₁),
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge) },
  rw mem_mul_stab_iff_smul_finset_subset hCne,
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab)),
  { exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx) },
  have hUn :
    ((C.bUnion $ λ y, x • y • C.mul_stab) ∩ (s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab))).nonempty,
  { have : x • C.bUnion (λ y, y • C.mul_stab) = C.bUnion (λ y, x • y • C.mul_stab) := bUnion_image,
    simpa [←this] },
  simp_rw [bUnion_inter, bUnion_nonempty, ←smul_assoc, smul_eq_mul] at hUn,
  obtain ⟨y, hy, hyne⟩ := hUn,
  have hxyCsubC : (x * y) • C.mul_stab ⊆ x • C,
  { rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff],
    exact smul_finset_mul_stab_subset hy },
  have hxyC : disjoint ((x * y) • C.mul_stab) C,
  { convert disjoint_smul_finset_mul_stab_mul_mul_stab (λ hxyC, _),
    { exact C.mul_mul_stab.symm },
    rw mul_mul_stab at hxyC,
    exact hyne.not_disjoint (hC.mono_left $ le_iff_subset.2 hxyC) },
  have hxysub : (x * y) • C.mul_stab ⊆ s ∩ a • C.mul_stab * (t ∩ b • C.mul_stab),
  { exact hxyC.left_le_of_le_sup_left (hxyCsubC.trans $ (subset_union_left _ _).trans hx.subset') },
  suffices : (s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab) ⊂ (a * b) • C.mul_stab,
  { cases (card_le_of_subset hxysub).not_lt ((card_lt_card this).trans_eq _),
    simp_rw card_smul_finset },
  apply ssubset_of_subset_not_subset,
  { refine (mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)).trans _,
    simp only [smul_mul_smul, mul_stab_mul_mul_stab, subset_refl] },
  { contrapose! hab,
    exact hab.trans (mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) }
end

@[to_additive] lemma mul_aux1 (ih : (s' * (s' * t').mul_stab).card + (t' * (s' * t').mul_stab).card
    ≤ (s' * t').card + (s' * t').mul_stab.card)
  (hconv : (s ∩ t).card + ((s ∪ t) * C.mul_stab).card ≤ C.card + C.mul_stab.card)
  (hnotconv : (C ∪ s' * t').card + (C ∪ s' * t').mul_stab.card <
    (s ∩ t).card + ((s ∪ t) * (C ∪ s' * t').mul_stab).card)
  (hCun : (C ∪ (s' * t')).mul_stab = (s' * t').mul_stab)
  (hsub : (s' * t').mul_stab ⊆ C.mul_stab) (hdisj : disjoint C (s' * t')) :
  (((s ∪ t) * C.mul_stab).card - ((s ∪ t) * (s' * t').mul_stab).card : ℤ) <
    C.mul_stab.card - (s' * (s' * t').mul_stab).card - (t' * (s' * t').mul_stab).card :=
begin
  set H := C.mul_stab with hH,
  set H' := (s' * t').mul_stab with hH',
  set C' := C ∪ (s' * t') with hC',
  zify at hconv hnotconv ih,
  calc
    (((s ∪ t) * H).card - ((s ∪ t) * H').card : ℤ)
        < C.card + H.card - (s ∩ t).card - (C'.card + H'.card - (s ∩ t).card) : begin
            rw ← hCun,
            linarith [hconv, hnotconv]
          end
    ... = H.card - (s' * t').card - H'.card : begin
            rw [card_union_eq hdisj, int.coe_nat_add],
            abel
          end
    ... ≤ H.card - (s' * H').card - (t' * H').card : by linarith [ih]
end

@[to_additive]
lemma disjoint_smul_mul_stab (hst : s ⊆ t) (has : ¬ a • s.mul_stab ⊆ t) :
  disjoint s (a • s.mul_stab) :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  suffices : disjoint (a • s.mul_stab) (s * s.mul_stab),
  { simpa [mul_comm, disjoint.comm, mul_stab_mul] },
  { apply disjoint_smul_finset_mul_stab_mul_mul_stab,
    rw [mul_comm, mul_stab_mul],
    contrapose! has,
    exact subset_trans has hst }
end

@[to_additive]
lemma disjoint_mul_sub_card_le {a : α} (b : α) {s t C : finset α} (has : a ∈ s)
  (hsC : disjoint t (a • C.mul_stab))
  (hst : ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab ⊆ C.mul_stab) :
  (C.mul_stab.card : ℤ) -
  (s ∩ (a • C.mul_stab) * ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab).card ≤
  ((s ∪ t) * C.mul_stab).card -
  ((s ∪ t) * ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab).card :=
begin
  obtain rfl | hC := C.eq_empty_or_nonempty,
  { simp },
calc
  (C.mul_stab.card : ℤ) -
  (s ∩ (a • C.mul_stab) * ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab).card =
    ((a • C.mul_stab) \
    (s ∩ (a • C.mul_stab) * ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab)).card :
    begin
    rw [card_sdiff (subset_trans (mul_subset_mul_left hst)
      (subset_trans (mul_subset_mul_right (inter_subset_right s _)) _)), card_smul_finset,
      int.coe_nat_sub],
    { apply le_trans (card_le_of_subset (mul_subset_mul_left hst)),
      apply le_trans (card_le_of_subset inter_mul_subset)
        (le_of_le_of_eq (card_le_of_subset (inter_subset_right _ _)) _),
      rw [smul_mul_assoc, mul_stab_mul_mul_stab, card_smul_finset] },
    { simp only [smul_mul_assoc, mul_stab_mul_mul_stab, subset.refl] },
    end
  ... ≤ ((s ∪ t) * C.mul_stab).card -
    ((s ∪ t) * ((s ∩ a • C.mul_stab) * (t ∩ b • C.mul_stab)).mul_stab).card :
  begin
    rw ← int.coe_nat_sub (card_le_of_subset (mul_subset_mul_left hst)),
    rw ← card_sdiff (mul_subset_mul_left hst),
    norm_cast,
    apply card_le_of_subset,
    intros x hx,
    refine mem_sdiff.mpr ⟨_, _⟩,
    { apply (smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1) },
    have hx' := (mem_sdiff.mp hx).2,
    contrapose! hx',
    obtain ⟨y, d, hyst, hd, hxyd⟩ := mem_mul.mp hx',
    obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1,
    rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd,
    have hyC : y ∈ a • C.mul_stab,
    { rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mul_stab_mul_mul_stab],
      apply mul_mem_mul hc ((mem_mul_stab hC).mpr (inv_smul_eq_iff.mpr _)),
      exact eq.symm ((mem_mul_stab hC).mp (hst hd)) },
    replace hyst : y ∈ s,
    { apply or_iff_not_imp_right.mp (mem_union.mp hyst),
      contrapose! hsC,
      exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩ },
    rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd,
    rw ← hxyd,
    exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd
  end
end

@[to_additive] private lemma card_mul_add_card_lt (hC : C.nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
  (hCst : C ⊆ s * t) (hCst' : disjoint C (s' * t')) :
  (s' * t').card + s'.card < (s * t).card + s.card :=
add_lt_add_of_lt_of_le (by { rw [←tsub_pos_iff_lt, ←card_sdiff (mul_subset_mul hs ht), card_pos],
  exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩) }) $ card_le_of_subset hs

/-! ### Kneser's theorem -/

/-- **Kneser's multiplication theorem**: A bound on the size of `s * t` in terms of its stabilizer.
-/
@[to_additive "**Kneser's addition theorem**: A bound on the size of `s + t` in terms of its
stabilizer."]
lemma mul_kneser (s t : finset α) :
  (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card ≤
    (s * t).card + (s * t).mul_stab.card :=
begin
  -- We're doing induction on `(s * t).card + s.card` generalizing the group. This is a bit tricky
  -- in Lean.
  set n := (s * t).card + s.card with hn,
  clear_value n,
  unfreezingI { induction n using nat.strong_induction_on with n ih generalizing α },
  subst hn,
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp },
  classical,
  obtain hstab | hstab := ne_or_eq (s * t).mul_stab 1,
  sorry { have image_coe_mul :
      ((s * t).image coe : finset (α ⧸ stabilizer α (s * t))) = s.image coe * t.image coe,
    { exact image_mul (quotient_group.mk' _ : α →* α ⧸ stabilizer α (s * t)) },
    suffices hineq : (s * t).mul_stab.card * ((s.image coe : finset (α ⧸ stabilizer α (s * t))).card
      + (t.image coe : finset (α ⧸ stabilizer α (s * t))).card - 1) ≤ (s * t).card,
    -- now to prove that `(s * (s * t).mul_stab).card = (s * t).mul_stab * (s.image coe).card` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
    { rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mul_card_image_coe',
        card_mul_card_image_coe'] at hineq,
      convert hineq using 1,
      exact add_comm _ _ },
    refine (mul_le_mul_left' _ _).trans_eq (card_mul_card_eq_mul_stab_card_mul_coe s t).symm,
    simpa only [←image_coe_mul, mul_stab_image_coe_quotient (hs.mul ht), mul_one, tsub_le_iff_right,
      card_one] using ih _ _ (s.image coe : finset (α ⧸ stabilizer α (s * t))) (t.image coe) rfl,
    rw [←image_coe_mul, card_mul_card_eq_mul_stab_card_mul_coe],
    exact add_lt_add_of_lt_of_le (lt_mul_left ((hs.mul ht).image _).card_pos $
      finset.one_lt_card.mpr ((hs.mul ht).mul_stab_nontrivial.2 hstab)) card_image_le },
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ⊢ ih,
  replace ih := λ s' t' h, @ih _ h α _ _ s' t' rfl,
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  { rw [card_singleton, card_singleton_mul, add_comm] },
  have : b / a ∉ t.mul_stab,
  { refine λ h, hab (eq.symm (eq_of_div_eq_one _)),
    replace h := subset_mul_stab_mul_right hs h,
    rw [hstab, mem_one] at h,
    exact h },
  simp only [mem_mul_stab' ht, smul_eq_mul, not_forall, exists_prop] at this,
  obtain ⟨c, hc, hbac⟩ := this,
  set t' := (a / c) • t with ht',
  clear_value t',
  rw ←inv_smul_eq_iff at ht',
  subst ht',
  rename t' t,
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel'] at hc,
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ←mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac,
  rw smul_finset_nonempty at ht,
  simp only [mul_smul_comm, smul_mul_assoc, mul_stab_smul, card_smul_finset] at *,
  have hst : (s ∩ t).nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩,
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left _ _, (not_subset _ _).2 ⟨_, hb, λ h, hbac $ inter_subset_right _ _ h⟩⟩,
  clear_dependent a b,
  set convergent : set (finset α) :=
    {C | C ⊆ s * t ∧ (s ∩ t).card + ((s ∪ t) * C.mul_stab).card ≤ C.card + C.mul_stab.card},
  have convergent_nonempty : convergent.nonempty,
  sorry { refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_right (card_le_of_subset $
      subset_mul_left _ $ one_mem_mul_stab.2 $ hst.mul $ hs.mono $ subset_union_left _ _) _).trans $
      ih (s ∩ t) (s ∪ t) _⟩,
    exact add_lt_add_of_le_of_lt (card_le_of_subset inter_mul_union_subset) (card_lt_card hsts) },
  let C := argmin_on (λ C : finset α, C.mul_stab.card) is_well_founded.wf _ convergent_nonempty,
  set H := C.mul_stab with hH,
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argmin_on_mem _ _ _ _,
  have hCmin : ∀ D : finset α, D.mul_stab ⊂ H → ¬ D ∈ convergent :=
    λ D hDH hD, (card_lt_card hDH).not_le $ argmin_on_le (λ D : finset α, D.mul_stab.card) _ _ hD,
  clear_value C,
  clear convergent_nonempty,
  obtain rfl | hC := C.eq_empty_or_nonempty,
  { simpa [hst.ne_empty, hH] using hCcard },
  -- If the stabilizer of `C` is trivial, then
  -- `s.card + t.card - 1 = (s ∩ t).card + (s ∪ t).card - 1.card = ≤ C.card ≤ (s * t).card`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mul_stab.2 hC),
  { simp only [hH, hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard,
    exact hCcard.trans (add_le_add_right (card_le_of_subset hCst) _) },
  exfalso,
  have : ¬ s * t * H ⊆ s * t,
  { rw [mul_subset_left_iff (hs.mul ht), hstab, ←coe_subset, coe_one],
    exact hCstab.not_subset_singleton },
  simp_rw [mul_subset_iff_left, not_forall, mem_mul] at this,
  obtain ⟨_, ⟨a, b, ha, hb, rfl⟩, hab⟩ := this,
  set s₁ := s ∩ a • H with hs₁,
  set s₂ := s ∩ b • H with hs₂,
  set t₁ := t ∩ b • H with ht₁,
  set t₂ := t ∩ a • H with ht₂,
  have hs₁s : s₁ ⊆ s := inter_subset_left _ _,
  have hs₂s : s₂ ⊆ s := inter_subset_left _ _,
  have ht₁t : t₁ ⊆ t := inter_subset_left _ _,
  have ht₂t : t₂ ⊆ t := inter_subset_left _ _,
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mul_stab.2 hC, mul_one _⟩⟩,
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mul_stab.2 hC, mul_one _⟩⟩,
  have hs₁ne : s₁.nonempty := ⟨_, has₁⟩,
  have ht₁ne : t₁.nonempty := ⟨_, hbt₁⟩,
  set C₁ := C ∪ (s₁ * t₁) with hC₁,
  set C₂ := C ∪ (s₂ * t₂) with hC₂,
  set H₁ := (s₁ * t₁).mul_stab with hH₁,
  set H₂ := (s₂ * t₂).mul_stab with hH₂,
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t),
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t),
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H,
  { rw [hH, ← mul_stab_mul_mul_stab C, ← smul_mul_smul],
    apply mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _) },
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H,
  { rw [hH, ← mul_stab_mul_mul_stab C, ← smul_mul_smul, mul_comm s₂ t₂],
    apply mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _) },
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mul_stab hCst hab),
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mul_stab hCst hab),
  have hst₁ : (s₁ * t₁).card + s₁.card < (s * t).card + s.card :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁,
  have hst₂ : (s₂ * t₂).card + s₂.card < (s * t).card + s.card :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂,
  have hC₁stab : C₁.mul_stab = H₁ := mul_stab_union hs₁ne ht₁ne hab hCst₁,
  have hH₁H : H₁ ⊂ H := mul_stab_mul_ssubset_mul_stab hs₁ne ht₁ne hab,
  have mul_aux₁ := mul_aux1 (ih _ _ hst₁) hCcard (not_le.1 $ λ h, hCmin _
      (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hH₁H.subset hCst₁,
  obtain ht₂eq | ht₂ne := t₂.eq_empty_or_nonempty,
  { have mul_aux₁_contr := disjoint_mul_sub_card_le b (hs₁s has₁)
      (disjoint_iff_inter_eq_empty.mpr ht₂eq) (subset_of_ssubset hH₁H),
    linarith [mul_aux₁, mul_aux₁_contr, int.coe_nat_nonneg ((t₁ * (s₁ * t₁).mul_stab)).card] },
  obtain hs₂eq | hs₂ne := s₂.eq_empty_or_nonempty,
  { have mul_aux₂_contr := disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.mpr hs₂eq) _,
    { simp only [union_comm t s, mul_comm t₁ s₁] at mul_aux₂_contr,
      linarith [mul_aux₁, mul_aux₂_contr, int.coe_nat_nonneg ((s₁ * (s₁ * t₁).mul_stab)).card] },
    { rw [mul_comm],
      exact subset_of_ssubset hH₁H } },
  have hC₂stab : C₂.mul_stab = H₂ := mul_stab_union hs₂ne ht₂ne (by rwa mul_comm) hCst₂,
  have hH₂H : H₂ ⊂ H := mul_stab_mul_ssubset_mul_stab hs₂ne ht₂ne (by rwa mul_comm),
  have mul_aux₂ := mul_aux1 (ih _ _ hst₂) hCcard (not_le.1 $ λ h, hCmin _ (hC₂stab.trans_ssubset hH₂H)
    ⟨hC₂st, h⟩) hC₂stab hH₂H.subset hCst₂,
  sorry
end

end finset