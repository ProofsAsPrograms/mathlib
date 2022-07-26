/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.ne_zero
import group_theory.group_action.quotient
import ring_theory.int.basic

/-!
# `zmod n` and quotient groups / rings

This file relates `zmod n` to the quotient group
`quotient_add_group.quotient (add_subgroup.zmultiples n)` and to the quotient ring
`(ideal.span {n}).quotient`.

## Main definitions

 - `zmod.quotient_zmultiples_nat_equiv_zmod` and `zmod.quotient_zmultiples_equiv_zmod`:
   `zmod n` is the group quotient of `ℤ` by `n ℤ := add_subgroup.zmultiples (n)`,
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.quotient_span_nat_equiv_zmod` and `zmod.quotient_span_equiv_zmod`:
   `zmod n` is the ring quotient of `ℤ` by `n ℤ : ideal.span {n}`
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.lift n f` is the map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group, quotient ring, ideal quotient
-/

open quotient_add_group
open zmod

variables (n : ℕ) {A R : Type*} [add_group A] [ring R]

namespace int

/-- `ℤ` modulo multiples of `n : ℕ` is `zmod n`. -/
def quotient_zmultiples_nat_equiv_zmod :
  ℤ ⧸ add_subgroup.zmultiples (n : ℤ) ≃+ zmod n :=
(equiv_quotient_of_eq (zmod.ker_int_cast_add_hom _)).symm.trans $
quotient_ker_equiv_of_right_inverse (int.cast_add_hom (zmod n)) coe int_cast_zmod_cast

/-- `ℤ` modulo multiples of `a : ℤ` is `zmod a.nat_abs`. -/
def quotient_zmultiples_equiv_zmod (a : ℤ) :
  ℤ ⧸ add_subgroup.zmultiples a ≃+ zmod a.nat_abs :=
(equiv_quotient_of_eq (zmultiples_nat_abs a)).symm.trans
  (quotient_zmultiples_nat_equiv_zmod a.nat_abs)

/-- `ℤ` modulo the ideal generated by `n : ℕ` is `zmod n`. -/
def quotient_span_nat_equiv_zmod :
  ℤ ⧸ ideal.span {↑n} ≃+* zmod n :=
(ideal.quot_equiv_of_eq (zmod.ker_int_cast_ring_hom _)).symm.trans $
  ring_hom.quotient_ker_equiv_of_right_inverse $
  show function.right_inverse coe (int.cast_ring_hom (zmod n)),
  from int_cast_zmod_cast

/-- `ℤ` modulo the ideal generated by `a : ℤ` is `zmod a.nat_abs`. -/
def quotient_span_equiv_zmod (a : ℤ) :
  ℤ ⧸ ideal.span ({a} : set ℤ) ≃+* zmod a.nat_abs :=
(ideal.quot_equiv_of_eq (span_nat_abs a)).symm.trans
  (quotient_span_nat_equiv_zmod a.nat_abs)

end int

namespace add_action

open add_subgroup add_monoid_hom add_equiv function

variables {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β)

/-- The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def zmultiples_quotient_stabilizer_equiv :
  zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ zmod (minimal_period ((+ᵥ) a) b) :=
(of_bijective (map _ (stabilizer (zmultiples a) b)
  (zmultiples_hom (zmultiples a) ⟨a, mem_zmultiples a⟩) (by
  { rw [zmultiples_le, mem_comap, mem_stabilizer_iff,
        zmultiples_hom_apply, coe_nat_zsmul, ←vadd_iterate],
    exact is_periodic_pt_minimal_period ((+ᵥ) a) b })) ⟨by
  { rw [←ker_eq_bot_iff, eq_bot_iff],
    refine λ q, induction_on' q (λ n hn, _),
    rw [mem_bot, eq_zero_iff, int.mem_zmultiples_iff, ←zsmul_vadd_eq_iff_minimal_period_dvd],
    exact (eq_zero_iff _).mp hn },
  λ q, induction_on' q (λ ⟨_, n, rfl⟩, ⟨n, rfl⟩)⟩).symm.trans
  (int.quotient_zmultiples_nat_equiv_zmod (minimal_period ((+ᵥ) a) b))

lemma zmultiples_quotient_stabilizer_equiv_symm_apply (n : zmod (minimal_period ((+ᵥ) a) b)) :
  (zmultiples_quotient_stabilizer_equiv a b).symm n =
    (n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
rfl

end add_action

namespace mul_action

open add_action subgroup add_subgroup function

variables {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)

local attribute [semireducible] mul_opposite

/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((•) a) b`. -/
noncomputable def zpowers_quotient_stabilizer_equiv :
  zpowers a ⧸ stabilizer (zpowers a) b ≃* multiplicative (zmod (minimal_period ((•) a) b)) :=
let f := zmultiples_quotient_stabilizer_equiv (additive.of_mul a) b in
⟨f.to_fun, f.inv_fun, f.left_inv, f.right_inv, f.map_add'⟩

lemma zpowers_quotient_stabilizer_equiv_symm_apply (n : zmod (minimal_period ((•) a) b)) :
  (zpowers_quotient_stabilizer_equiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (n : ℤ) :=
rfl

/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimal_period ((•) a) b`. -/
noncomputable def orbit_zpowers_equiv : orbit (zpowers a) b ≃ zmod (minimal_period ((•) a) b) :=
(orbit_equiv_quotient_stabilizer _ b).trans (zpowers_quotient_stabilizer_equiv a b).to_equiv

/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def _root_.add_action.orbit_zmultiples_equiv
  {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β) :
  add_action.orbit (zmultiples a) b ≃ zmod (minimal_period ((+ᵥ) a) b) :=
(add_action.orbit_equiv_quotient_stabilizer (zmultiples a) b).trans
  (zmultiples_quotient_stabilizer_equiv a b).to_equiv

attribute [to_additive orbit_zmultiples_equiv] orbit_zpowers_equiv

@[to_additive orbit_zmultiples_equiv_symm_apply]
lemma orbit_zpowers_equiv_symm_apply (k : zmod (minimal_period ((•) a) b)) :
  (orbit_zpowers_equiv a b).symm k =
    (⟨a, mem_zpowers a⟩ : zpowers a) ^ (k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
rfl

lemma orbit_zpowers_equiv_symm_apply' (k : ℤ) :
  (orbit_zpowers_equiv a b).symm k =
    (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ :=
begin
  rw [orbit_zpowers_equiv_symm_apply, zmod.coe_int_cast],
  exact subtype.ext (zpow_smul_mod_minimal_period _ _ k),
end

lemma _root_.add_action.orbit_zmultiples_equiv_symm_apply'
  {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β) (k : ℤ) :
  (add_action.orbit_zmultiples_equiv a b).symm k =
    (k • (⟨a, mem_zmultiples a⟩ : zmultiples a)) +ᵥ ⟨b, add_action.mem_orbit_self b⟩ :=
begin
  rw [add_action.orbit_zmultiples_equiv_symm_apply, zmod.coe_int_cast],
  exact subtype.ext (zsmul_vadd_mod_minimal_period _ _ k),
end

attribute [to_additive orbit_zmultiples_equiv_symm_apply'] orbit_zpowers_equiv_symm_apply'

@[to_additive] lemma minimal_period_eq_card [fintype (orbit (zpowers a) b)] :
  minimal_period ((•) a) b = fintype.card (orbit (zpowers a) b) :=
by rw [←fintype.of_equiv_card (orbit_zpowers_equiv a b), zmod.card]

@[to_additive] instance minimal_period_pos [fintype $ orbit (zpowers a) b] :
  ne_zero $ minimal_period ((•) a) b :=
⟨begin
  haveI : nonempty (orbit (zpowers a) b) := (orbit_nonempty b).to_subtype,
  rw minimal_period_eq_card,
  exact fintype.card_ne_zero,
end⟩

end mul_action
