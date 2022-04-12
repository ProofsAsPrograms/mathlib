/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map
import data.polynomial.denoms_clearable

/-!  # Laurent polynomials -/

open_locale polynomial big_operators
open polynomial add_monoid_algebra multiplicative
noncomputable theory

variables {R N Z : Type*}

section monoid_algebra_homs
open finsupp

namespace monoid_algebra

section semiring
variables (R) [semiring R] [monoid N] [monoid Z]

/--  A monoid homomorphism `f : N →* Z` extends to a monoid homomorphism `N →* monoid_algebra R Z`,
mapping `n : N` to `finsupp.single (f x) 1`. -/
def single_one_right_hom (f : N →* Z) : N →* monoid_algebra R Z :=
by refine ⟨λ x, single (f x) 1, _, _⟩; simp ; refl

@[simp] lemma single_one_right_hom_apply (f : N →* Z) (n : N) :
  single_one_right_hom R f n = single (f n) 1 := rfl

/--  A multiplicative homomorphism `f : N →* Z` between two monoids induces a `k`-algebra
homomorphism `monoid_hom_lift f : monoid_algebra R N →+* monoid_algebra R Z`. -/
def monoid_hom_lift (f : N →* Z) : monoid_algebra R N →+* monoid_algebra R Z :=
lift_nc_ring_hom single_one_ring_hom (single_one_right_hom R f) $ λ r n,
show (single 1 r * (single (f n) 1) : monoid_algebra R Z) =
  (single (f n) 1 : monoid_algebra R Z) * (single 1 r),
by simp only [single_mul_single, mul_one, one_mul]

end semiring

section comm_semiring
variables [comm_semiring R] [monoid N] [monoid Z]

/--  A multiplicative homomorphism `f : N →* Z` between two monoids induces an `R`-algebra
homomorphism `full_lift f : monoid_algebra R N →ₐ[R] monoid_algebra R Z`. -/
def full_lift (f : N →* Z) : monoid_algebra R N →ₐ[R] monoid_algebra R Z :=
lift _ _ (monoid_algebra R Z) (single_one_right_hom _ f)

end comm_semiring

end monoid_algebra

namespace add_monoid_algebra
section semiring
variables (R) [semiring R] [add_monoid N] [add_monoid Z]

/--  An additive homomorphism `f : N →+ Z` extends to a multiplicative homomorphism
`multiplicative N →* monoid_algebra R Z`, mapping `n : N` to `finsupp.single (f x) 1`. -/
def single_one_right_add_hom (f : N →+ Z) :
  multiplicative N →* monoid_algebra R (multiplicative Z) :=
monoid_algebra.single_one_right_hom _ f.to_multiplicative

@[simp] lemma single_one_right_add_hom_apply (f : N →+ Z) (n : N) :
  single_one_right_add_hom R f n = single (f n) 1 := rfl

--  `by convert monoid_algebra.monoid_hom_lift R f.to_multiplicative` appears to be the same
--  mathematical definition, but is harder to use.
/--  An additive homomorphism `f : N →+ Z` induces a `k`-algebra homomorphism
`add_monoid_hom_lift f : add_monoid_algebra R N →+* add_monoid_algebra R Z`. -/
def add_monoid_hom_lift (f : N →+ Z) : add_monoid_algebra R N →+* add_monoid_algebra R Z :=
begin
  -- using `refine` times out.  Substituting the first `exact` into `_` yields a type mismatch.
  apply lift_nc_ring_hom _ (single_one_right_add_hom R f) (λ r n, _),
  { exact monoid_algebra.single_one_ring_hom },
  { show (single 1 r * single (f n) 1 : monoid_algebra R (multiplicative Z)) =
      single (f n) 1 * single 1 r,
    simp only [monoid_algebra.single_mul_single, one_mul, mul_one] }
end

end semiring

section comm_semiring
variables [comm_semiring R] [add_monoid N] [add_monoid Z]

/--  An additive homomorphism `f : N →+ Z` induces an `R`-algebra homomorphism
`add_full_lift f : add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z`. -/
def add_full_lift (f : N →+ Z) : add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z :=
lift R N (add_monoid_algebra R Z) (single_one_right_add_hom _ f)

@[simp]
lemma add_full_lift_single (f : N →+ Z) (n : N) (r : R) :
  add_full_lift f (single n r) = single (f n) r :=
begin
  simp only [add_full_lift, lift_single, single_one_right_add_hom_apply, smul_single', mul_one],
  refl,
end

end comm_semiring



/-
variables [comm_semiring R] [add_monoid Z] [add_monoid N] (f : N →+ Z)

/--  An additive homomorphism `f : N →+ Z` between two additive monoids induces an `R`-algebra
homomorphism `full_lift f : add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z`. -/
def add_full_lift (f : N →+ Z) :
  add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z :=
begin
  refine add_monoid_algebra.lift R N (monoid_algebra R (multiplicative Z)) _,
  refine ⟨λ x, finsupp.single (of_add (f (to_add x))) 1, _, _⟩,
  { rw [to_add_one, _root_.map_zero, of_add_zero],
    refl },
  { exact λ x y, by simp only [single_mul_single, mul_one, to_add_mul, _root_.map_add, of_add_add]},
end

@[simp]
lemma add_full_lift_single (n : N) (r : R) :
  add_full_lift f (finsupp.single n r) = finsupp.single (f n) r :=
begin
  simp only [add_full_lift, add_monoid_algebra.lift_single, monoid_hom.coe_mk, to_add_of_add,
    finsupp.smul_single', mul_one],
  congr,
end
-/

end add_monoid_algebra

end monoid_algebra_homs

/--  The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials.
 -/
abbreviation laurent_polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℤ

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

/--  The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_polynomial {R : Type*} [comm_semiring R] :
  R[X] →ₐ[R] R[T;T⁻¹] :=
begin
  refine alg_hom.comp _ (to_finsupp_iso_alg R).to_alg_hom,
  exact (add_monoid_algebra.add_full_lift (nat.cast_add_monoid_hom ℤ)),
end

namespace laurent_polynomial

section comm_semiring
variables [comm_semiring R]

/--  The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
{ to_fun    := finsupp.single 0,
  map_one'  := rfl,
  map_mul'  := λ x y, by simp only [add_monoid_algebra.single_mul_single, add_zero],
  map_zero' := finsupp.single_zero,
  map_add'  := λ x y, finsupp.single_add }

/--  The variable of the ring of Laurent polynomials. -/
def T' : R[T;T⁻¹] := finsupp.single 1 1

/--  The function `n ↦ T ^ n`, implemented as sequence `ℤ ↦ R[T;T⁻¹]`. -/
def T (n : ℤ) : R[T;T⁻¹] := finsupp.single n 1

@[simp]
lemma T_zero : (T 0 : R[T;T⁻¹]) = 1 := rfl

lemma T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n :=
by {convert add_monoid_algebra.single_mul_single.symm, simp [T] }

/--  `T_add_rev` is the `simp`-normal form of `T_add`. -/
@[simp]
lemma T_add_rev (m n : ℤ) : (T m * T n : R[T;T⁻¹]) = T (m + n) :=
(T_add _ _).symm

lemma is_unit_T (n : ℤ) : is_unit (T n : R[T;T⁻¹]) :=
is_unit_of_mul_eq_one _ (T (- n)) (by simp)

lemma is_left_regular_T (n : ℤ) : is_left_regular (T n : R[T;T⁻¹]) :=
is_left_regular_of_mul_eq_one (by simp : T (-n) * T n = 1)

lemma mul_T_injective (n : ℤ) : function.injective ((*) (T n) : R[T;T⁻¹] → R[T;T⁻¹]) :=
is_left_regular_T _

@[simp]
lemma T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) :=
by { convert add_monoid_algebra.single_pow n, simp [T] }

-- `by simp [polynomial.to_laurent_polynomial]` proves the lemma.
-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
lemma full_lift_monomial (n : ℕ) (r : R) :
  (monomial n r : R[X]).to_laurent_polynomial = finsupp.single n r :=
by {simp [polynomial.to_laurent_polynomial], }

--by simp only [polynomial.to_laurent_polynomial, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp,
--    alg_equiv.coe_alg_hom, function.comp_app, to_finsupp_iso_alg_apply, ring_equiv.to_fun_eq_coe,
--    to_finsupp_iso_apply, to_finsupp_monomial, add_monoid_algebra.add_full_lift_single, nat.coe_cast_add_monoid_hom,
--    int.nat_cast_eq_coe_nat], }

@[simp]
lemma full_lift_one_zero : (finsupp.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

@[simp]
lemma full_lift_C (r : R) :
  (polynomial.C r).to_laurent_polynomial = C r :=
full_lift_monomial 0 r

--  without the empty type annotation `(_ : _)`, the proof times out.
@[simp] lemma full_lift_one : (polynomial.to_laurent_polynomial : R[X] → R[T;T⁻¹]) 1 = 1 :=
(full_lift_C (1 : R) : _)

@[simp]
lemma full_lift_X :
  (X : R[X]).to_laurent_polynomial = T 1 :=
full_lift_monomial 1 1

@[simp]
lemma full_lift_X_pow (n : ℕ) :
  (X ^ n : R[X]).to_laurent_polynomial = T n :=
by simp only [map_pow, full_lift_X, T_pow, mul_one]

@[simp]
lemma full_lift_C_mul_X_pow (n : ℕ) (r : R) :
  (polynomial.C r * X ^ n).to_laurent_polynomial = C r * T n :=
by simp only [_root_.map_mul, full_lift_C, full_lift_X_pow]

@[simp]
lemma single_eq_C_mul_T (r : R) (n : ℤ) :
  (finsupp.single n r : R[T;T⁻¹]) = (C r * T n : R[T;T⁻¹]) :=
by convert add_monoid_algebra.single_mul_single.symm; simp

lemma commute_T (n : ℤ) (f : R[T;T⁻¹]) : commute (T n) f :=
begin
  exact commute.all (T n) f,
end


@[simp]
lemma T_neg_one_mul (f : R[T;T⁻¹]) : T (- 1) * f = f * T (- 1) :=
begin

end


@[simp]
lemma T_mul (f : R[T;T⁻¹]) (m : ℤ) : T m * f = f * T m :=
begin
  unfold T,
  rw [
    ← add_monoid_algebra.single_pow m, single_one_comm],
  simp,
  rw [single_eq_C_mul_T, _root_.map_one, one_mul],

  squeeze_simp {single_pass := tt},
end

@[simp]
lemma mul_T_T (m n : ℤ) : (T m * T n : R[T;T⁻¹]) = T (m + n) :=
(T_add _ _).symm



instance : module R[X] R[T;T⁻¹] :=
{ smul := λ f l, f.to_laurent_polynomial * l,
  one_smul := λ f, by simp only [full_lift_one, one_mul],
  mul_smul := λ f g l, by simp only [mul_assoc, _root_.map_mul],
  smul_add := λ f x y, by simp only [mul_add],
  smul_zero := λ f, by simp only [mul_zero],
  add_smul := λ f g x, by simp only [add_mul, _root_.map_add],
  zero_smul := λ f, by simp only [_root_.map_zero, zero_mul] }

@[elab_as_eliminator] protected lemma induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_C : ∀a, M (C a))
  (h_add : ∀{p q}, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (finsupp.single n a) → M (finsupp.single (n+1) a))
  (h_monomial_Z : ∀(n : ℕ) (a : R), M (finsupp.single (- n) a) → M (finsupp.single (-n-1) a)) :
  M p :=
begin
  have A : ∀(n:ℤ) (a), M (finsupp.single n a),
  { assume n a,
    apply n.induction_on,
    { exact h_C a },
    { exact λ m, h_monomial m a },
    { exact λ (m : ℕ), h_monomial_Z m a } },
  have B : ∀ (s : finset ℤ), M (s.sum (λ (n : ℤ), C (p.to_fun n) * (finsupp.single n 1))),
  { apply finset.induction,
    { convert h_C 0, simp only [finset.sum_empty, _root_.map_zero] },
    { assume n s ns ih, rw finset.sum_insert ns,
    { apply h_add  _ ih,
      convert A n (p.to_fun n),
      rw [C, ring_hom.coe_mk],
      simp_rw [add_monoid_algebra.single_mul_single, zero_add, mul_one] } } },
     convert B p.support,
     rw [C, ring_hom.coe_mk],
     simp_rw [add_monoid_algebra.single_mul_single, zero_add, mul_one],
     ext a,
     suffices : p a = ite (a ∈ p.support) (p.to_fun a) 0,
     { simpa only [finset.sum_apply', finsupp.single_apply, finset.sum_ite_eq'] },
     split_ifs with h h,
     { refl },
     { exact finsupp.not_mem_support_iff.mp h }
end


/--
To prove something about Laurent polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℤ) (a : R), M (finsupp.single n a)) :
  M p :=
begin
  refine p.induction_on (h_monomial 0) h_add _ _;
  exact λ n f Mf, h_monomial _ f
end

instance : algebra R[X] R[T;T⁻¹] :=
{ commutes' := λ f l, by simp [mul_comm],
  smul_def' := λ f l, rfl,
  .. (add_full_lift (nat.cast_add_monoid_hom ℤ)).to_ring_hom.comp (to_finsupp_iso R).to_ring_hom }

lemma exists_X_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), f * T' ^ n = f'.to_laurent_polynomial :=
begin
  apply f.induction_on' _ (λ n a, _); clear f,
  { rintros f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩,
    by_cases h : m ≤ n;
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩;
    rw [add_mul, _root_.map_add, _root_.map_mul, ← hf, _root_.map_mul, ← hg, mul_assoc,
      full_lift_X_pow, pow_add, full_lift_X_pow, mul_assoc, ← pow_add T' n, add_comm n, pow_add] },
  { cases n with n n,
    { exact ⟨0, polynomial.C a * X ^ n, by simp⟩ },
    { refine ⟨n + 1, polynomial.C a, _⟩,
      rw [full_lift_C, T', add_monoid_algebra.single_pow, add_monoid_algebra.single_mul_single],
      simp [-neg_add_rev, int.neg_succ_of_nat_eq, neg_add_self, C, ring_hom.coe_mk] } }
end

/--  This version of `exists_X_pow'` can be called as `rcases f.exists_X_pow' with ⟨n, f', rfl⟩`. -/
lemma exists_X_pow' (f : R[T;T⁻¹]) : ∃ (n : ℤ) (f' : R[X]),
  f = f'.to_laurent_polynomial * finsupp.single n 1 :=
begin
  rcases f.exists_X_pow with ⟨n, f', hf⟩,
  refine ⟨(- n), f', _⟩,
  rw [← hf, mul_assoc, T', add_monoid_algebra.single_pow, add_monoid_algebra.single_mul_single],
  simp,
end

/--  Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on ~~Laurent~~ polynomials;
* `Q (f * T)` implies `Q f`;

is true on all Laurent polynomials. -/
lemma proprop (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
  (PQ : ∀ (f : R[X]), Q f.to_laurent_polynomial)
  (Tn : ∀ f, Q (f * T') → Q f) :
  Q f :=
begin
  rcases f.exists_X_pow' with ⟨n, f', rfl⟩,
  cases n with n n,
  { convert PQ (f' * X ^ n),
    simp },
  { rw int.neg_succ_of_nat_eq,
    induction n with n hn,
    { refine Tn _ _,
      convert PQ f',
      rw mul_assoc,
      convert mul_one _,
      rw [T', add_monoid_algebra.single_mul_single],
      simp only [int.coe_nat_zero, zero_add, add_left_neg, mul_one, full_lift_one_zero] },
    { suffices : Q (polynomial.to_laurent_polynomial f' *
        (finsupp.single (-(↑(n.succ))) 1) * finsupp.single (-1) 1),
      { rwa [mul_assoc, add_monoid_algebra.single_mul_single, mul_one] at this },
      refine Tn _ _,
      rwa [mul_assoc, T', add_monoid_algebra.single_mul_single, mul_assoc,
        add_monoid_algebra.single_mul_single, mul_one, mul_one] } }
end

end comm_semiring

end laurent_polynomial
