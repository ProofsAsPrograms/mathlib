/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import measure_theory.function.lp_space.basic
import topology.continuous_function.compact

/-! # Continuous functions in `Lp` -/

noncomputable theory
open topological_space measure_theory filter
open_locale nnreal ennreal big_operators topological_space measure_theory

variables {α E F G : Type*} {m m0 : measurable_space α} {p : ℝ≥0∞} {q : ℝ} {μ ν : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]

open_locale bounded_continuous_function
open bounded_continuous_function

section

variables [topological_space α] [borel_space α] [second_countable_topology_either α E]
variables (E p μ)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
def measure_theory.Lp.bounded_continuous_function : add_subgroup (Lp E p μ) :=
add_subgroup.add_subgroup_of
  ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E)).range
  (Lp E p μ)

variables {E p μ}

/-- By definition, the elements of `Lp.bounded_continuous_function E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
lemma measure_theory.Lp.mem_bounded_continuous_function_iff {f : (Lp E p μ)} :
  f ∈ measure_theory.Lp.bounded_continuous_function E p μ
    ↔ ∃ f₀ : (α →ᵇ E), f₀.to_continuous_map.to_ae_eq_fun μ = (f : α →ₘ[μ] E) :=
add_subgroup.mem_add_subgroup_of

namespace bounded_continuous_function

variables [is_finite_measure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
lemma mem_Lp (f : α →ᵇ E) :
  f.to_continuous_map.to_ae_eq_fun μ ∈ Lp E p μ :=
begin
  refine Lp.mem_Lp_of_ae_bound (‖f‖) _,
  filter_upwards [f.to_continuous_map.coe_fn_to_ae_eq_fun μ] with x _,
  convert f.norm_coe_le_norm x
end

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
lemma Lp_norm_le (f : α →ᵇ E) :
  ‖(⟨f.to_continuous_map.to_ae_eq_fun μ, mem_Lp f⟩ : Lp E p μ)‖
  ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * ‖f‖ :=
begin
  apply Lp.norm_le_of_ae_bound (norm_nonneg f),
  { refine (f.to_continuous_map.coe_fn_to_ae_eq_fun μ).mono _,
    intros x hx,
    convert f.norm_coe_le_norm x },
  { apply_instance }
end

variables (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def to_Lp_hom [fact (1 ≤ p)] : normed_add_group_hom (α →ᵇ E) (Lp E p μ) :=
{ bound' := ⟨_, Lp_norm_le⟩,
  .. add_monoid_hom.cod_restrict
      ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
      (Lp E p μ)
      mem_Lp }

lemma range_to_Lp_hom [fact (1 ≤ p)] :
  ((to_Lp_hom p μ).range : add_subgroup (Lp E p μ))
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  symmetry,
  convert add_monoid_hom.add_subgroup_of_range_eq_of_le
    ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
    (by { rintros - ⟨f, rfl⟩, exact mem_Lp f } : _ ≤ Lp E p μ),
end

variables (𝕜 : Type*) [fact (1 ≤ p)]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (α →ᵇ E) →L[𝕜] (Lp E p μ) :=
linear_map.mk_continuous
  (linear_map.cod_restrict
    (Lp.Lp_submodule E p μ 𝕜)
    ((continuous_map.to_ae_eq_fun_linear_map μ).comp (to_continuous_map_linear_map α E 𝕜))
    mem_Lp)
  _
  Lp_norm_le

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f := ae_eq_fun.coe_fn_mk f _

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  ((linear_map.range (to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)).to_add_subgroup)
    = measure_theory.Lp.bounded_continuous_function E p μ :=
range_to_Lp_hom p μ

variables {p}

lemma to_Lp_norm_le [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]:
  ‖(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
linear_map.mk_continuous_norm_le _ ((measure_univ_nnreal μ) ^ (p.to_real)⁻¹).coe_nonneg _

lemma to_Lp_inj {f g : α →ᵇ E} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
begin
  refine ⟨λ h, _, by tauto⟩,
  rw [←fun_like.coe_fn_eq, ←(map_continuous f).ae_eq_iff_eq μ (map_continuous g)],
  refine (coe_fn_to_Lp p μ 𝕜 f).symm.trans (eventually_eq.trans _ $ coe_fn_to_Lp p μ 𝕜 g),
  rw h,
end

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ)) := λ f g hfg, (to_Lp_inj μ).mp hfg

end bounded_continuous_function

namespace continuous_map

variables [compact_space α] [is_finite_measure μ]
variables (𝕜 : Type*) (p μ) [fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `bounded_continuous_function.to_Lp` along the isometry. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  C(α, E) →L[𝕜] (Lp E p μ) :=
(bounded_continuous_function.to_Lp p μ 𝕜).comp
  (linear_isometry_bounded_of_compact α E 𝕜).to_linear_isometry.to_continuous_linear_map

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (linear_map.range (to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)).to_add_subgroup
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  refine set_like.ext' _,
  have := (linear_isometry_bounded_of_compact α E 𝕜).surjective,
  convert function.surjective.range_comp this (bounded_continuous_function.to_Lp p μ 𝕜),
  rw ←bounded_continuous_function.range_to_Lp p μ,
  refl,
end

variables {p}

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α,  E)) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk f _

lemma to_Lp_def [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  to_Lp p μ 𝕜 f
  = bounded_continuous_function.to_Lp p μ 𝕜 (linear_isometry_bounded_of_compact α E 𝕜 f) :=
rfl

@[simp] lemma to_Lp_comp_to_continuous_map [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f.to_continuous_map
  = bounded_continuous_function.to_Lp p μ 𝕜 f :=
rfl

@[simp] lemma coe_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  (to_Lp p μ 𝕜 f : α →ₘ[μ] E) = f.to_ae_eq_fun μ :=
rfl

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ)) :=
(bounded_continuous_function.to_Lp_injective _).comp
  (linear_isometry_bounded_of_compact α E 𝕜).injective

lemma to_Lp_inj {f g : C(α, E)} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
(to_Lp_injective μ).eq_iff

variables {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.  -/
lemma has_sum_of_has_sum_Lp {β : Type*} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E]
  {g : β → C(α, E)} {f : C(α, E)} (hg : summable g)
  (hg2 : has_sum (to_Lp p μ 𝕜 ∘ g) (to_Lp p μ 𝕜 f)) : has_sum g f :=
begin
  convert summable.has_sum hg,
  exact to_Lp_injective μ (hg2.unique ((to_Lp p μ 𝕜).has_sum $ summable.has_sum hg)),
end

variables (μ) [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_norm_eq_to_Lp_norm_coe :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖
  = ‖(bounded_continuous_function.to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ :=
continuous_linear_map.op_norm_comp_linear_isometry_equiv _ _

/-- Bound for the operator norm of `continuous_map.to_Lp`. -/
lemma to_Lp_norm_le :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
by { rw to_Lp_norm_eq_to_Lp_norm_coe, exact bounded_continuous_function.to_Lp_norm_le μ }

end continuous_map

end
