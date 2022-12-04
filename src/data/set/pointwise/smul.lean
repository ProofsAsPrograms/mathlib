/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module.basic
import data.list.of_fn
import data.set.pairwise
import data.set.pointwise.basic

/-!
# Algebraic structure of pointwise operations

This file provides lemmas for pointwise operations on `set` in monoids, groups, modules, and shows
that `set α` is a semigroup/monoid/... if `α` is.

## Main declarations

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

Given that `set α` is a monoid when `α` is, `n • s`, where `n : ℕ`, is ambiguous between pointwise
scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while the
latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].
-/

/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/
library_note "pointwise nat action"

open function
open_locale pointwise

variables {F α β γ : Type*}

namespace set

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `set`. See
note [pointwise nat action].-/
protected def has_nsmul [has_zero α] [has_add α] : has_smul ℕ (set α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (set α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_smul ℤ (set α) := ⟨zsmul_rec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive] protected def has_zpow [has_one α] [has_mul α] [has_inv α] : has_pow (set α) ℤ :=
⟨λ s n, zpow_rec n s⟩

localized "attribute [instance] set.has_nsmul set.has_npow set.has_zsmul set.has_zpow" in pointwise

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, image2_assoc mul_assoc,
  ..set.has_mul }

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (set α) :=
{ mul_comm := λ s t, image2_comm mul_comm
  ..set.semigroup }

section mul_one_class
variables [mul_one_class α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class : mul_one_class (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.has_one, ..set.has_mul }

localized "attribute [instance] set.mul_one_class set.add_zero_class set.semigroup set.add_semigroup
  set.comm_semigroup set.add_comm_semigroup" in pointwise

@[to_additive] lemma subset_mul_left (s : set α) {t : set α} (ht : (1 : α) ∈ t) : s ⊆ s * t :=
λ x hx, ⟨x, 1, hx, ht, mul_one _⟩

@[to_additive] lemma subset_mul_right {s : set α} (t : set α) (hs : (1 : α) ∈ s) : t ⊆ s * t :=
λ x hx, ⟨1, x, hs, hx, one_mul _⟩

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singleton_monoid_hom : α →* set α := { ..singleton_mul_hom, ..singleton_one_hom }

@[simp, to_additive] lemma coe_singleton_monoid_hom :
  (singleton_monoid_hom : α → set α) = singleton := rfl
@[simp, to_additive] lemma singleton_monoid_hom_apply (a : α) : singleton_monoid_hom a = {a} := rfl

end mul_one_class

section monoid
variables [monoid α] {s t : set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : monoid (set α) := { ..set.semigroup, ..set.mul_one_class, ..set.has_npow }

localized "attribute [instance] set.monoid set.add_monoid" in pointwise

@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
| 0 := by { rw pow_zero, exact one_mem_one }
| (n + 1) := by { rw pow_succ, exact mul_mem_mul ha (pow_mem_pow _) }

@[to_additive] lemma pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
| 0 := by { rw pow_zero, exact subset.rfl }
| (n + 1) := by { rw pow_succ, exact mul_subset_mul hst (pow_subset_pow _) }

@[to_additive] lemma pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
begin
  refine nat.le_induction _ (λ n h ih, _) _,
  { exact subset.rfl },
  { rw pow_succ,
    exact ih.trans (subset_mul_right _ hs) }
end

@[to_additive] lemma mem_prod_list_of_fn {a : α} {s : fin n → set α} :
  a ∈ (list.of_fn s).prod ↔ ∃ f : (Π i : fin n, s i), (list.of_fn (λ i, (f i : α))).prod = a :=
begin
  induction n with n ih generalizing a,
  { simp_rw [list.of_fn_zero, list.prod_nil, fin.exists_fin_zero_pi, eq_comm, set.mem_one] },
  { simp_rw [list.of_fn_succ, list.prod_cons, fin.exists_fin_succ_pi, fin.cons_zero, fin.cons_succ,
      mem_mul, @ih, exists_and_distrib_left, exists_exists_eq_and, set_coe.exists, subtype.coe_mk,
      exists_prop] }
end

@[to_additive] lemma mem_list_prod {l : list (set α)} {a : α} :
  a ∈ l.prod ↔ ∃ l' : list (Σ s : set α, ↥s),
    list.prod (l'.map (λ x, (sigma.snd x : α))) = a ∧ l'.map sigma.fst = l :=
begin
  induction l using list.of_fn_rec with n f,
  simp_rw [list.exists_iff_exists_tuple, list.map_of_fn, list.of_fn_inj', and.left_comm,
    exists_and_distrib_left, exists_eq_left, heq_iff_eq, function.comp, mem_prod_list_of_fn],
  split,
  { rintros ⟨fi, rfl⟩,  exact ⟨λ i, ⟨_, fi i⟩, rfl, rfl⟩, },
  { rintros ⟨fi, rfl, rfl⟩, exact ⟨λ i, _, rfl⟩, },
end

@[to_additive] lemma mem_pow {a : α} {n : ℕ} :
  a ∈ s ^ n ↔ ∃ f : fin n → s, (list.of_fn (λ i, (f i : α))).prod = a :=
by rw [←mem_prod_list_of_fn, list.of_fn_const, list.prod_repeat]

@[simp, to_additive] lemma empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

@[to_additive] lemma mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩

@[to_additive] lemma univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩

@[simp, to_additive] lemma univ_mul_univ : (univ : set α) * univ = univ :=
mul_univ_of_one_mem $ mem_univ _

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp] lemma nsmul_univ {α : Type*} [add_monoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : set α) = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, one_nsmul _
| (n + 2) := λ _, by { rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ] }

@[simp, to_additive nsmul_univ] lemma univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : set α) ^ n = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, pow_one _
| (n + 2) := λ _, by { rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ] }

@[to_additive] protected lemma _root_.is_unit.set : is_unit a → is_unit ({a} : set α) :=
is_unit.map (singleton_monoid_hom : α →* set α)

end monoid

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
{ ..set.monoid, ..set.comm_semigroup }

localized "attribute [instance] set.comm_monoid set.add_comm_monoid" in pointwise

open_locale pointwise

section division_monoid
variables [division_monoid α] {s t : set α}

@[to_additive] protected lemma mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 :=
begin
  refine ⟨λ h, _, _⟩,
  { have hst : (s * t).nonempty := h.symm.subst one_nonempty,
    obtain ⟨a, ha⟩ := hst.of_image2_left,
    obtain ⟨b, hb⟩ := hst.of_image2_right,
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) :=
      λ a b ha hb, (h.subset $ mem_image2_of_mem ha hb),
    refine ⟨a, b, _, _, H ha hb⟩; refine eq_singleton_iff_unique_mem.2 ⟨‹_›, λ x hx, _⟩,
    { exact (eq_inv_of_mul_eq_one_left $ H hx hb).trans (inv_eq_of_mul_eq_one_left $ H ha hb) },
    { exact (eq_inv_of_mul_eq_one_right $ H ha hx).trans (inv_eq_of_mul_eq_one_right $ H ha hb) } },
  { rintro ⟨b, c, rfl, rfl, h⟩,
    rw [singleton_mul_singleton, h, singleton_one] }
end

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`set α` is a subtraction monoid under pointwise operations if `α` is."]
protected def division_monoid : division_monoid (set α) :=
{ mul_inv_rev := λ s t, by { simp_rw ←image_inv, exact image_image2_antidistrib mul_inv_rev },
  inv_eq_of_mul := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := set.mul_eq_one_iff.1 h,
    rw [inv_singleton, inv_eq_of_mul_eq_one_right hab],
  end,
  div_eq_mul_inv := λ s t,
    by { rw [←image_id (s / t), ←image_inv], exact image_image2_distrib_right div_eq_mul_inv },
  ..set.monoid, ..set.has_involutive_inv, ..set.has_div, ..set.has_zpow }

@[simp, to_additive] lemma is_unit_iff : is_unit s ↔ ∃ a, s = {a} ∧ is_unit a :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    obtain ⟨a, b, ha, hb, h⟩ := set.mul_eq_one_iff.1 u.mul_inv,
    refine ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩,
    rw [←singleton_mul_singleton, ←ha, ←hb],
    exact u.inv_mul },
  { rintro ⟨a, rfl, ha⟩,
    exact ha.set }
end

end division_monoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_comm_monoid "`set α` is a commutative subtraction monoid under pointwise
operations if `α` is."]
protected def division_comm_monoid [division_comm_monoid α] : division_comm_monoid (set α) :=
{ ..set.division_monoid, ..set.comm_semigroup }

/-- `set α` has distributive negation if `α` has. -/
protected def has_distrib_neg [has_mul α] [has_distrib_neg α] : has_distrib_neg (set α) :=
{ neg_mul := λ _ _, by { simp_rw ←image_neg, exact image2_image_left_comm neg_mul },
  mul_neg := λ _ _, by { simp_rw ←image_neg, exact image_image2_right_comm mul_neg },
  ..set.has_involutive_neg }

localized "attribute [instance] set.division_monoid set.subtraction_monoid set.division_comm_monoid
  set.subtraction_comm_monoid set.has_distrib_neg" in pointwise

section distrib
variables [distrib α] (s t u : set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

end distrib

section mul_zero_class
variables [mul_zero_class α] {s t : set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/

lemma mul_zero_subset (s : set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
lemma zero_mul_subset (s : set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [mem_mul] using hs

end mul_zero_class

section group
variables [group α] {s t : set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/

@[simp, to_additive] lemma one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬ disjoint s t :=
by simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, set.nonempty]

@[to_additive] lemma not_one_mem_div_iff : (1 : α) ∉ s / t ↔ disjoint s t :=
one_mem_div_iff.not_left

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] disjoint.one_not_mem_div_set

@[to_additive] lemma nonempty.one_mem_div (h : s.nonempty) : (1 : α) ∈ s / s :=
let ⟨a, ha⟩ := h in mem_div.2 ⟨a, a, ha, ha, div_self' _⟩

@[to_additive] lemma is_unit_singleton (a : α) : is_unit ({a} : set α) := (group.is_unit a).set

@[simp, to_additive] lemma is_unit_iff_singleton : is_unit s ↔ ∃ a, s = {a} :=
by simp only [is_unit_iff, group.is_unit, and_true]

@[simp, to_additive] lemma image_mul_left : ((*) a) '' t = ((*) a⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive] lemma image_mul_right : (* b) '' t = (* b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive] lemma image_mul_left' : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp
@[to_additive] lemma image_mul_right' : (* b⁻¹) '' t = (* b) ⁻¹' t := by simp

@[simp, to_additive] lemma preimage_mul_left_singleton : ((*) a) ⁻¹' {b} = {a⁻¹ * b} :=
by rw [← image_mul_left', image_singleton]

@[simp, to_additive] lemma preimage_mul_right_singleton : (* a) ⁻¹' {b} = {b * a⁻¹} :=
by rw [← image_mul_right', image_singleton]

@[simp, to_additive] lemma preimage_mul_left_one : ((*) a) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive] lemma preimage_mul_right_one : (* b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive] lemma preimage_mul_left_one' : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp
@[to_additive] lemma preimage_mul_right_one' : (* b⁻¹) ⁻¹' 1 = {b} := by simp

@[simp, to_additive] lemma mul_univ (hs : s.nonempty) : s * (univ : set α) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩

@[simp, to_additive] lemma univ_mul (ht : t.nonempty) : (univ : set α) * t = univ :=
let ⟨a, ha⟩ := ht in eq_univ_of_forall $ λ b, ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩

end group

section group_with_zero
variables [group_with_zero α] {s t : set α}

lemma div_zero_subset (s : set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
lemma zero_div_subset (s : set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]

lemma nonempty.div_zero (hs : s.nonempty) : s / 0 = 0 :=
s.div_zero_subset.antisymm $ by simpa [mem_div] using hs

lemma nonempty.zero_div (hs : s.nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm $ by simpa [mem_div] using hs

end group_with_zero

section has_mul
variables [has_mul α] [has_mul β] [mul_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_mul : m '' (s * t) = m '' s * m '' t := image_image2_distrib $ map_mul m

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm ⟩ }

end has_mul

section group
variables [group α] [division_monoid β] [monoid_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_div : m '' (s / t) = m '' s / m '' t := image_image2_distrib $ map_div m

@[to_additive]
lemma preimage_div_preimage_subset {s t : set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm ⟩ }

end group

open_locale pointwise

/-! ### Translation/scaling of sets -/

section smul
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[to_additive]
lemma smul_set_inter [group α] [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
(image_inter $ mul_action.injective a).symm

lemma smul_set_inter₀ [group_with_zero α] [mul_action α β] {s t : set β} (ha : a ≠ 0) :
  a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

@[simp, to_additive]
lemma smul_set_univ [group α] [mul_action α β] {a : α} : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[simp, to_additive]
lemma smul_univ [group α] [mul_action α β] {s : set α} (hs : s.nonempty) :
  s • (univ : set β) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩

@[to_additive]
instance smul_comm_class_set [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (set γ) :=
⟨λ _ _, commute.set_image $ smul_comm _ _⟩

@[to_additive]
instance smul_comm_class_set' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α (set β) (set γ) :=
⟨λ _ _ _, image_image2_distrib_right $ smul_comm _⟩

@[to_additive]
instance smul_comm_class_set'' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) β (set γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) (set β) (set γ) :=
⟨λ _ _ _, image2_left_comm smul_comm⟩

@[to_additive]
instance is_scalar_tower [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (set γ) :=
{ smul_assoc := λ a b T, by simp only [←image_smul, image_image, smul_assoc] }

@[to_additive]
instance is_scalar_tower' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (set β) (set γ) :=
⟨λ _ _ _, image2_image_left_comm $ smul_assoc _⟩

@[to_additive]
instance is_scalar_tower'' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (set α) (set β) (set γ) :=
{ smul_assoc := λ T T' T'', image2_assoc smul_assoc }

instance is_central_scalar [has_smul α β] [has_smul αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (set β) :=
⟨λ a S, congr_arg (λ f, f '' S) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `set α` on `set β`"]
protected def mul_action [monoid α] [mul_action α β] : mul_action (set α) (set β) :=
{ mul_smul := λ _ _ _, image2_assoc mul_smul,
  one_smul := λ s, image2_singleton_left.trans $ by simp_rw [one_smul, image_id'] }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action
on `set β`."]
protected def mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, one_smul, image_id'] } }

localized "attribute [instance] set.mul_action_set set.add_action_set
  set.mul_action set.add_action" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distrib_mul_action_set [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (set β) :=
{ smul_add := λ _ _ _, image_image2_distrib $ smul_add _,
  smul_zero := λ _, image_singleton.trans $ by rw [smul_zero, singleton_zero] }

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_set [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (set β) :=
{ smul_mul := λ _ _ _, image_image2_distrib $ smul_mul' _,
  smul_one := λ _, image_singleton.trans $ by rw [smul_one, singleton_one] }

localized "attribute [instance] set.distrib_mul_action_set set.mul_distrib_mul_action_set"
  in pointwise

instance [has_zero α] [has_zero β] [has_smul α β] [no_zero_smul_divisors α β] :
  no_zero_smul_divisors (set α) (set β) :=
⟨λ s t h, begin
  by_contra' H,
  have hst : (s • t).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_smul_left.subset_zero_iff, ←hst.of_smul_right.subset_zero_iff, not_subset,
    mem_zero] at H,
  obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ h.subset $ smul_mem_smul hs ht).elim ha hb,
end⟩

instance no_zero_smul_divisors_set [has_zero α] [has_zero β] [has_smul α β]
  [no_zero_smul_divisors α β] : no_zero_smul_divisors α (set β) :=
⟨λ a s h, begin
  by_contra' H,
  have hst : (a • s).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_image.subset_zero_iff, not_subset, mem_zero] at H,
  obtain ⟨ha, b, ht, hb⟩ := H,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ h.subset $ smul_mem_smul_set ht).elim ha hb,
end⟩

instance [has_zero α] [has_mul α] [no_zero_divisors α] : no_zero_divisors (set α) :=
⟨λ s t h, eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end smul

open_locale pointwise

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β] {s : set α} {t : set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/

lemma smul_zero_subset (s : set α) : s • (0 : set β) ⊆ 0 := by simp [subset_def, mem_smul]
lemma zero_smul_subset (t : set β) : (0 : set α) • t ⊆ 0 := by simp [subset_def, mem_smul]

lemma nonempty.smul_zero (hs : s.nonempty) : s • (0 : set β) = 0 :=
s.smul_zero_subset.antisymm $ by simpa [mem_smul] using hs

lemma nonempty.zero_smul (ht : t.nonempty) : (0 : set α) • t = 0 :=
t.zero_smul_subset.antisymm $ by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_set {s : set β} (h : s.nonempty) : (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

lemma zero_smul_set_subset (s : set β) : (0 : α) • s ⊆ 0 :=
image_subset_iff.2 $ λ x _, zero_smul α x

lemma subsingleton_zero_smul_set (s : set β) : ((0 : α) • s).subsingleton :=
subsingleton_singleton.anti $ zero_smul_set_subset s

lemma zero_mem_smul_set {t : set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
⟨0, h, smul_zero _⟩

variables [no_zero_smul_divisors α β] {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
begin
  split,
  { rintro ⟨a, b, ha, hb, h⟩,
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h,
    { exact or.inl ⟨ha, b, hb⟩ },
    { exact or.inr ⟨hb, a, ha⟩ } },
  { rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩),
    { exact ⟨0, b, hs, hb, zero_smul _ _⟩ },
    { exact ⟨a, 0, ha, ht, smul_zero _⟩ } }
end

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
begin
  refine ⟨_, zero_mem_smul_set⟩,
  rintro ⟨b, hb, h⟩,
  rwa (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha at hb,
end

end smul_with_zero

section left_cancel_semigroup
variables [left_cancel_semigroup α] {s t : set α}

@[to_additive] lemma pairwise_disjoint_smul_iff :
  s.pairwise_disjoint (• t) ↔ (s ×ˢ t).inj_on (λ p, p.1 * p.2) :=
pairwise_disjoint_image_right_iff $ λ _ _, mul_right_injective _

end left_cancel_semigroup

section group
variables [group α] [mul_action α β] {s t A B : set β} {a : α} {x : β}

@[simp, to_additive]
lemma smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s := (mul_action.injective _).mem_set_image

@[to_additive]
lemma mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show x ∈ mul_action.to_perm a '' A ↔ _, from mem_image_equiv

@[to_additive]
lemma mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
lemma preimage_smul (a : α) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
((mul_action.to_perm a).symm.image_eq_preimage _).symm

@[to_additive]
lemma preimage_smul_inv (a : α) (t : set β) : (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul (to_units a)⁻¹ t

@[simp, to_additive]
lemma set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
image_subset_image_iff $ mul_action.injective _

@[to_additive]
lemma set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
(image_subset_iff).trans $ iff_of_eq $ congr_arg _ $
  preimage_equiv_eq_image_symm _ $ mul_action.to_perm _

@[to_additive]
lemma subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
iff.symm $ (image_subset_iff).trans $ iff.symm $ iff_of_eq $ congr_arg _ $
  image_equiv_eq_preimage_symm _ $ mul_action.to_perm _

@[to_additive]
lemma smul_inter_ne_empty_iff {s t : set α} {x : α} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x :=
begin
  rw ne_empty_iff_nonempty,
  split,
  { rintros ⟨a, h, ha⟩,
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h,
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩, },
  { rintros ⟨a, b, ⟨ha, hb⟩, rfl⟩,
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩, },
end

@[to_additive]
lemma smul_inter_ne_empty_iff' {s t : set α} {x : α} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x :=
by simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]

@[to_additive]
lemma op_smul_inter_ne_empty_iff {s t : set α} {x : αᵐᵒᵖ} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = mul_opposite.unop x :=
begin
  rw ne_empty_iff_nonempty,
  split,
  { rintros ⟨a, h, ha⟩,
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h,
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩, },
  { rintros ⟨a, b, ⟨ha, hb⟩, H⟩,
    have : mul_opposite.op (a⁻¹ * b) = x := congr_arg mul_opposite.op H,
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩, },
end

@[simp, to_additive] lemma Union_inv_smul :
  (⋃ (g : α), g⁻¹ • s) = (⋃ (g : α), g • s) :=
function.surjective.supr_congr _ inv_surjective $ λ g, rfl

@[to_additive]
lemma Union_smul_eq_set_of_exists {s : set β} :
  (⋃ (g : α), g • s) = {a | ∃ (g : α), g • a ∈ s} :=
by simp_rw [← Union_set_of, ← Union_inv_smul, ← preimage_smul, preimage]

end group

section group_with_zero
variables [group_with_zero α] [mul_action α β] {s : set α} {a : α}

@[simp] lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : set β)
  (x : β) : a • x ∈ a • A ↔ x ∈ A :=
show units.mk0 a ha • _ ∈ _ ↔ _, from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show _ ∈ units.mk0 a ha • _ ↔ _, from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_set_iff

lemma preimage_smul₀ (ha : a ≠ 0) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
preimage_smul (units.mk0 a ha) t

lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : set β) :
  (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul ((units.mk0 a ha)⁻¹) t

@[simp] lemma set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} :
  a • A ⊆ a • B ↔ A ⊆ B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_set_smul_iff

lemma set_smul_subset_iff₀ (ha : a ≠ 0) {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_iff

lemma subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_set_smul_iff

lemma smul_univ₀ (hs : ¬ s ⊆ 0) : s • (univ : set β) = univ :=
let ⟨a, ha, ha₀⟩ := not_subset.1 hs in eq_univ_of_forall $ λ b,
  ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul₀ ha _⟩

end group_with_zero

section monoid
variables [monoid α] [add_group β] [distrib_mul_action α β] (a : α) (s : set α) (t : set β)

@[simp] lemma smul_set_neg : a • -t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, smul_neg]

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by { simp_rw ←image_neg, exact image_image2_right_comm smul_neg }

end monoid

section ring
variables [ring α] [add_comm_group β] [module α β] (a : α) (s : set α) (t : set β)

@[simp] lemma neg_smul_set : -a • t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] protected lemma neg_smul : -s • t = -(s • t) :=
by { simp_rw ←image_neg, exact image2_image_left_comm neg_smul }

end ring

end set
