/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.monoid_algebra.basic

/-!  #  Degree of an `add_monoid_algebra`

Let `R` be a semiring and let `A` be a `semilattice_sup`.

For an element `f : add_monoid_algebra R A`, this file defines
* `add_monoid_algebra.degree`: the degree taking values in `with_bot A`,
* `add_monoid_algebra.trailing_degree`: the trailing degree taking values in `with_top A`.
If the grading type `A` is a linearly ordered additive monoid, then this notions of degree
coincide with the standard one:
* the degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the trailing degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

Currently, the only results are
* `degree_mul_le` -- the degree of a product is at most the sum of the degrees,
*  `le_trailing_degree_mul` -- the trailing degree of a product is at least the sum of the
  trailing degrees.
-/

namespace add_monoid_algebra
open_locale classical

variables {R A B : Type*} [semiring R]

section degree
variables [semilattice_sup B] [order_bot B]

/--  Let `R` be a semiring, let `A` be a `semilattice_sup`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The degree of `f` takes values in `with_bot A` and
it is the supremum of the support of `f` or `⊥`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the maximum of
the exponents. -/
def degree (D : A → B) (f : add_monoid_algebra R A) : B :=
f.support.sup D

variables [has_add A]
variables [has_add B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]

lemma sup_support_mul_le (D : A → B) (Dm : ∀ {a b}, D (a + b) ≤ D a + D b)
  (f g : add_monoid_algebra R A) :
  (f * g).support.sup D ≤ f.support.sup D + g.support.sup D :=
begin
  refine (finset.sup_le (λ d ds, _)),
  obtain ⟨a, af, b, bg, rfl⟩ : ∃ a, a ∈ f.support ∧ ∃ b, b ∈ g.support ∧ d = a + b,
  { simpa only [finset.mem_bUnion, finset.mem_singleton, exists_prop] using f.support_mul g ds },
  refine Dm.trans (add_le_add _ _);
  exact finset.le_sup ‹_›,
end

end degree

section trailing_degree
variables [semilattice_inf B] [order_top B]

/--  Let `R` be a semiring, let `A` be a `semilattice_inf`, and let `f : R[A]` be an
an element of `add_monoid_algebra R A`.  The trailing degree of `f` takes values in `with_top A`
and it is the infimum of the support of `f` or `⊤`, depending on whether `f` is non-zero or not.

If `A` has a linear order, then this notion coincides with the usual one, using the minimum of
the exponents. -/
def trailing_degree (D : A → B) (f : add_monoid_algebra R A) : B :=
f.support.inf D

variables [has_add A]
variables [has_add B] [covariant_class B B (+) (≤)] [covariant_class B B (function.swap (+)) (≤)]

lemma trailing_degree_mul_le (D : A → B) (Dm : ∀ {a b}, D a + D b ≤ D (a + b))
  (f g : add_monoid_algebra R A) :
  f.trailing_degree D + g.trailing_degree D ≤ (f * g).trailing_degree D :=
@degree_mul_le _ Aᵒᵈ Bᵒᵈ _ _ _ _ _ _ _ _ (λ a b, Dm) _ _

end trailing_degree

/-  This section is here only to show the relationship to the "standard" degree. -/
section old_degrees

section degree

variables [semilattice_sup A]

/--  The old degree. -/
def old_degree (f : add_monoid_algebra R A) : with_bot A :=
f.support.sup coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
variables (f g : add_monoid_algebra R A)

example : f.degree (coe : A → with_bot A) = f.old_degree :=
rfl

example : (f * g).old_degree ≤ f.old_degree + g.old_degree :=
degree_mul_le (coe : A → with_bot A) (λ a b, (with_bot.coe_add _ _).le) f g

end degree

section trailing_degree

variables [semilattice_inf A]

/--  The old trailing degree. -/
def old_trailing_degree (f : add_monoid_algebra R A) : with_top A :=
f.support.inf coe

variables [add_monoid A] [covariant_class A A (+) (≤)] [covariant_class A A (function.swap (+)) (≤)]
  (f g : add_monoid_algebra R A)

example : f.trailing_degree (coe : A → with_bot A) = f.old_trailing_degree :=
rfl

example : f.old_trailing_degree + g.old_trailing_degree ≤ (f * g).old_trailing_degree :=
trailing_degree_mul_le _ (λ a b, (with_bot.coe_add _ _).le) f g

end trailing_degree

end old_degrees

end add_monoid_algebra
