/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.l1_space
import measure_theory.function.strongly_measurable.inner

/-! # `Lp` spaces of functions into inner product spaces -/

noncomputable theory
open topological_space measure_theory filter
open_locale nnreal ennreal big_operators topological_space measure_theory

variables {α 𝕜 E : Type*} {m : measurable_space α} {p : ℝ≥0∞} {μ : measure α}
variables [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

namespace measure_theory

section
variables {f : α → 𝕜}

lemma mem_ℒp.re (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.re (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.re (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_re_le_norm (f x), },
  exact hf.of_le_mul hf.1.re (eventually_of_forall this),
end

lemma mem_ℒp.im (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.im (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.im (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_im_le_norm (f x), },
  exact hf.of_le_mul hf.1.im (eventually_of_forall this),
end

lemma mem_ℒp.of_real {f : α → ℝ} (hf : mem_ℒp f p μ) : mem_ℒp (λ x, (f x : 𝕜)) p μ :=
(@is_R_or_C.of_real_clm 𝕜 _).comp_mem_ℒp' hf

lemma mem_ℒp_re_im_iff {f : α → 𝕜} :
  mem_ℒp (λ x, is_R_or_C.re (f x)) p μ ∧ mem_ℒp (λ x, is_R_or_C.im (f x)) p μ ↔
  mem_ℒp f p μ :=
begin
  refine ⟨_, λ hf, ⟨hf.re, hf.im⟩⟩,
  rintro ⟨hre, him⟩,
  convert hre.of_real.add (him.of_real.const_mul is_R_or_C.I),
  { ext1 x,
    rw [pi.add_apply, mul_comm, is_R_or_C.re_add_im] },
  all_goals { apply_instance }
end

lemma integrable.of_real {f : α → ℝ} (hf : integrable f μ) :
  integrable (λ x, (f x : 𝕜)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.of_real }

lemma integrable.re_im_iff :
  integrable (λ x, is_R_or_C.re (f x)) μ ∧ integrable (λ x, is_R_or_C.im (f x)) μ ↔
  integrable f μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable, exact mem_ℒp_re_im_iff }

lemma integrable.re (hf : integrable f μ) : integrable (λ x, is_R_or_C.re (f x)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.re, }

lemma integrable.im (hf : integrable f μ) : integrable (λ x, is_R_or_C.im (f x)) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.im, }

end

lemma mem_ℒp.const_inner (c : E) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ a, ⟪c, f a⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner ae_strongly_measurable_const hf.1)
  (eventually_of_forall (λ x, norm_inner_le_norm _ _))

lemma mem_ℒp.inner_const {f : α → E} (hf : mem_ℒp f p μ) (c : E) :
  mem_ℒp (λ a, ⟪f a, c⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner hf.1 ae_strongly_measurable_const)
  (eventually_of_forall (λ x, by { rw mul_comm, exact norm_inner_le_norm _ _, }))

section inner_product
variables {f : α → E}

lemma integrable.const_inner (c : E) (hf : integrable f μ) : integrable (λ x, ⟪c, f x⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.const_inner c, }

lemma integrable.inner_const (hf : integrable f μ) (c : E) : integrable (λ x, ⟪f x, c⟫) μ :=
by { rw ← mem_ℒp_one_iff_integrable at hf ⊢, exact hf.inner_const c, }

end inner_product

end measure_theory
