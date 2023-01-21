import analysis.inner_product_space.basic
import measure_theory.integral.set_integral

namespace measure_theory

variables {α : Type*} [measurable_space α]

variables {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜]

variables {E : Type*} [inner_product_space 𝕜 E] [complete_space E] [normed_space ℝ E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

lemma integral_inner {f : α → E} (hf : integrable f μ) (c : E) :
  ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
((@innerSL 𝕜 E _ _ c).restrict_scalars ℝ).integral_comp_comm hf

lemma integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E) (hf : integrable f μ)
  (hf_int : ∀ (c : E), ∫ x, ⟪c, f x⟫ ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }

end measure_theory
