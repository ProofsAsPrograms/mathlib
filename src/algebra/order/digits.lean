/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.int.log
import data.nat.digits

/-!
# Digits of a linearly ordered (semi)field

## Main definitions

* `order.digits b r`: the digits of `r` in base `b`, indexed by their power of `b`; the digit at
  position 0 is the one to the left of the decimal point.

-/

variables {R : Type*} [linear_ordered_semifield R] [floor_semiring R]

namespace order

/-- `order.digits b r` enumerates the base-`b` digits of a element `r`-/
def digits (b : ℕ) (r : R) (z : ℤ) : ℕ := ⌊r/b^z⌋₊ % b

lemma digits_lt {b : ℕ} (hb : 0 < b) (r : R) (z : ℤ) : digits b r z < b := nat.mod_lt _ hb

@[simp] lemma digits_zero (b : ℕ) : digits b (0 : R) = 0 :=
begin
  ext z,
  rw [digits, zero_div, nat.floor_zero, nat.zero_mod, pi.zero_apply],
end

/-- All the digits of greater powers than `int.log b r` are zero -/
lemma digits_eq_zero_of_log_lt {b : ℕ} {r : R} (z : ℤ) (hz : int.log b r < z) :
  digits b r z = 0 :=
begin
  rw digits,
  cases lt_or_le 1 b with hb hb,
  { have hb' : (1 : R) < b := nat.one_lt_cast.mpr hb,
    convert nat.zero_mod _,
    rw nat.floor_eq_zero,
    cases lt_or_le 0 r with hr hr,
    { rw ←int.lt_zpow_iff_log_lt hb hr at hz,
      rw div_lt_one (zpow_pos_of_pos (zero_lt_one.trans hb') _),
      exact hz, },
    { refine lt_of_le_of_lt _ zero_lt_one,
      apply div_nonpos_of_nonpos_of_nonneg hr (zpow_nonneg (zero_le_one.trans hb'.le) _) } },
  { obtain rfl | hb := hb.eq_or_lt,
    { simp },
    { rw nat.lt_one_iff at hb,
      subst hb,
      rw int.log_of_left_le_one zero_le_one at hz,
      simp [zero_zpow _ hz.ne'] } }
end

@[simp] lemma digits_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) : digits b (b ^ z : R) = pi.single z 1 :=
begin
  have hb' : (b : R) ≠ 0 :=  by exact_mod_cast (zero_le_one.trans_lt hb).ne',
  ext z₂,
  rw [digits, div_eq_mul_inv, ←zpow_neg, ←zpow_add₀ hb', ←sub_eq_add_neg],
  obtain rfl | hz := decidable.eq_or_ne z z₂,
  { rw [pi.single_eq_same, sub_self, zpow_zero, nat.floor_one, nat.mod_eq_of_lt hb], },
  rw [pi.single_eq_of_ne' hz],
  rw ←sub_ne_zero at hz,
  revert hz,
  generalize : z - z₂ = dz,
  intro hz,
  obtain ⟨n, rfl | rfl⟩ := int.eq_coe_or_neg dz,
  { rw [int.coe_nat_ne_zero] at hz,
    rw [zpow_coe_nat, ←nat.cast_pow, nat.floor_coe],
    exact nat.mod_eq_zero_of_dvd (dvd_pow_self _ hz) },
  { rw [neg_ne_zero, int.coe_nat_ne_zero] at hz,
    rw [zpow_neg],
    convert nat.zero_mod _,
    rw [zpow_coe_nat, nat.floor_eq_zero],
    apply inv_lt_one _,
    apply one_lt_pow; assumption_mod_cast },
end

@[simp] lemma digits_one {b : ℕ} (hb : 1 < b) : digits b (1 : R) = pi.single 0 1 :=
begin
  rw ←zpow_zero (b : R),
  exact digits_zpow hb _,
end

/-- The digit at `int.log b r` is not zero -/
lemma digits_log {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
  digits b r (int.log b r) ≠ 0 :=
begin
  rw [digits],
  suffices : 1 ≤ r / (↑b ^ int.log b r) ∧ r / (↑b ^ int.log b r) < b,
  { rw ←nat.floor_lt' at this,
    { rw nat.mod_eq_of_lt this.2,
      rw [ne.def, nat.floor_eq_zero, not_lt],
      exact this.1 },
    exact (zero_lt_one.trans hb).ne' },
  have hb' : (1 : R) < b := nat.one_lt_cast.mpr hb,
  have hb'' := zpow_pos_of_pos (zero_lt_one.trans hb') (int.log b r),
  split,
  { rw [one_le_div hb''],
    exact int.zpow_log_le_self hb hr, },
  { rw [div_lt_iff' hb'', ←zpow_add_one₀ (zero_lt_one.trans hb').ne'],
    exact int.lt_zpow_succ_log_self hb r }
end

end order
