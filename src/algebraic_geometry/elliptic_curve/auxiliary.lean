/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import linear_algebra.free_module.ideal_quotient
import ring_theory.principal_ideal_domain
import data.polynomial.field_division
import ring_theory.adjoin_root
import ring_theory.norm
import linear_algebra.free_module.strong_rank_condition

/-! Auxiliary results to show the degree of the norm of an element of an algebra over
  a polynomial ring is equal to the dimension of the quotient by its span.
  TODO: This file should be removed eventually and the results should go into appropriate places. -/

open_locale polynomial direct_sum big_operators
open finite_dimensional ideal

noncomputable theory

section ring

variables (R : Type*) {M : Type*} [ring R] [add_comm_group M]
  [module R M] [no_zero_smul_divisors R M] {x : M}

/-- The linear isomorphism $R \to R \cdot x$ given by $r \mapsto r \cdot x$,
  if `M` is a torsion-free `R`-module and `x ≠ 0`. -/
def linear_equiv.span_singleton (h : x ≠ 0) : R ≃ₗ[R] submodule.span R ({x} : set M) :=
linear_equiv.of_bijective (linear_map.id.smul_right ⟨x, submodule.mem_span_singleton_self x⟩) $
  ⟨λ r r' he, smul_left_injective R h (subtype.ext_iff.1 he), λ y,
    by { simp_rw subtype.ext_iff, exact submodule.mem_span_singleton.1 y.2 }⟩

lemma linear_equiv.span_singleton_symm_apply_smul (h : x ≠ 0) (y : submodule.span R ({x} : set M)) :
  (linear_equiv.span_singleton R h).symm y • x = y :=
subtype.ext_iff.1 $ (linear_equiv.span_singleton R h).apply_symm_apply _

end ring

section comm_ring

variables {R S ι : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  [is_domain R] [is_principal_ideal_ring R] [is_domain S] [fintype ι] (b : basis ι R S)
  {I : ideal S} (hI : I ≠ ⊥)

/-- For a non-zero element `f` in an algebra `S` over a principal idela domain `R` that is finite
  and free as an `R`-module,
  -/
lemma associated_norm_prod_smith {f : S} (hf : f ≠ 0) :
  associated (algebra.norm R f) (∏ i, smith_coeffs b _ (span_singleton_eq_bot.not.2 hf) i) :=
begin
  have hI := span_singleton_eq_bot.not.2 hf,
  let b' := ring_basis b (span {f}) hI,
  classical, rw [← matrix.det_diagonal, ← linear_map.det_to_lin b'],
  let e := (b'.equiv ((span {f}).self_basis b hI) $ equiv.refl _).trans
    ((linear_equiv.span_singleton S hf).symm.restrict_scalars R),
  refine (linear_map.associated_det_of_eq_comp e _ _ _).symm,
  dsimp only [e, linear_equiv.trans_apply],
  simp_rw [← linear_equiv.coe_to_linear_map, ← linear_map.comp_apply, ← linear_map.ext_iff],
  refine b'.ext (λ i, _),
  simp_rw [linear_map.comp_apply, linear_equiv.coe_to_linear_map, matrix.to_lin_apply,
    basis.repr_self, finsupp.single_eq_pi_single, matrix.diagonal_mul_vec_single, pi.single_apply,
    ite_smul, zero_smul, finset.sum_ite_eq', mul_one, if_pos (finset.mem_univ _), b'.equiv_apply],
  change _ = f * _,
  rw [mul_comm, ← smul_eq_mul, linear_equiv.restrict_scalars_apply,
    linear_equiv.span_singleton_symm_apply_smul, self_basis_def],
  refl,
end

end comm_ring

section scalar_tower

variables (F : Type*) {R S ι : Type*} [comm_ring F] [comm_ring R] [comm_ring S]
  [algebra F R] [algebra R S] [is_domain R] [is_principal_ideal_ring R] [is_domain S]
  [fintype ι] (b : basis ι R S) {I : ideal S} (hI : I ≠ ⊥)

instance : Π i, module F (R ⧸ span ({I.smith_coeffs b hI i} : set R)) := λ i, by apply_instance

variables [algebra F S] [is_scalar_tower F R S]

/-- Decompose $S/I$ as a direct sum of cyclic $R$-modules. -/
def quotient_equiv_direct_sum :
  (S ⧸ I) ≃ₗ[F] ⨁ i, R ⧸ span ({I.smith_coeffs b hI i} : set R) :=
begin
  apply ((I.quotient_equiv_pi_span b _).restrict_scalars F).trans
    (direct_sum.linear_equiv_fun_on_fintype _ _ _).symm,
  exact linear_map.is_scalar_tower.compatible_smul,
  -- why doesn't it automatically apply?
  -- even after `change linear_map.compatible_smul _ (Π i, R ⧸ span _) F R`
end

lemma finrank_quotient_eq_sum [nontrivial F]
  [∀ i, module.free F (R ⧸ span ({I.smith_coeffs b hI i} : set R))]
  [∀ i, module.finite F (R ⧸ span ({I.smith_coeffs b hI i} : set R))] :
  finrank F (S ⧸ I) = ∑ i, finrank F (R ⧸ span ({I.smith_coeffs b hI i} : set R)) :=
begin
  rw (linear_equiv.finrank_eq $ quotient_equiv_direct_sum F b hI),
  -- slow, and dot notation doesn't work
  rw module.free.finrank_direct_sum,
end

end scalar_tower

section polynomial_field

variables {F S ι : Type*} [field F] [comm_ring S] [algebra F[X] S] [is_domain S]
  [finite ι] (b : basis ι F[X] S) --[module.free F[X] S] [module.finite F[X] S]
  {I : ideal S} (hI : I ≠ ⊥)

instance (i : ι) : finite_dimensional F (F[X] ⧸ span ({I.smith_coeffs b hI i} : set F[X])) :=
(adjoin_root.power_basis $ I.smith_coeffs_ne_zero b hI i).finite_dimensional

open polynomial
include b

/-- If `S` is an `F[X]`-module, the `F`-dimension of $S/\langle f \rangle$ is
  the degree of the norm of `f`. -/
lemma finrank_quotient_span_eq_nat_degree_norm [algebra F S] [is_scalar_tower F F[X] S] {f : S}
  (hf : f ≠ 0) : finrank F (S ⧸ span ({f} : set S)) = (algebra.norm F[X] f).nat_degree :=
begin
  have hI := span_singleton_eq_bot.not.2 hf,
  haveI := fintype.of_finite ι,
  rw [nat_degree_eq_of_degree_eq (degree_eq_degree_of_associated $ associated_norm_prod_smith b hf),
      nat_degree_prod _ _ (λ i _, smith_coeffs_ne_zero b _ hI i), finrank_quotient_eq_sum F b hI],
  -- finrank_quotient_eq_sum slow
  congr' with i,
  exact (adjoin_root.power_basis $ smith_coeffs_ne_zero b _ hI i).finrank,
end

end polynomial_field