import probability.density
import probability.moments
import analysis.special_functions.gaussian
import measure_theory.integral.set_to_l1
import analysis.normed_space.bounded_linear_maps
import topology.sequences

import algebra.order.ring
import data.complex.exponential
import topology.algebra.module.basic

import measure_theory.integral.integrable_on
import measure_theory.integral.bochner
import order.filter.indicator_function
import topology.metric_space.thickened_indicator



import measure_theory.covering.besicovitch_vector_space
import measure_theory.measure.haar_lebesgue
import analysis.normed_space.pointwise
import measure_theory.covering.differentiation
import measure_theory.constructions.polish
import measure_theory.integral.integral_eq_improper
import analysis.special_functions.integrals
import measure_theory.group.integration

import measure_theory.integral.integral_eq_improper
import analysis.special_functions.integrals



#check real.exp_pos
#check measure_theory.integral_image_eq_integral_abs_det_fderiv_smul
#check measurable_set.univ
#check measure_theory.integral_image_eq_integral_abs_det_fderiv_smul
#check real.coe_to_nnreal
#check set.inter_comm
#check function.const
#check measure_theory.measure.map_apply_of_ae_measurable

---#check probability_theory.moment,

/-
We would like to define the Gaussian measure on ℝ.
There are two ways of doing this.

(1). Given `E` a topological vector space equipped with the measure `μ`, we say `f : E → ℝ` is the
  standard Gaussian random variable with respect to `μ` if
  ```
    μ.with_density f = (volume : measure ℝ).with_density (λ x, √(2π)⁻¹ exp (-x² / 2)).
  ```
  Then, we say `μ` is a Gaussian measure if for all `l : E →L[ℝ] ℝ`, there exists some `m s : ℝ`
  such that `l = sf + m` where `f` is the standard Gaussian.

(2). Define the Gaussian measure on ℝ directly by saying `μ : measure ℝ` is a Gaussian measure
  if there exists `m s : ℝ` such that
  ```
    μ = if s ≠ 0 then (volume : measure ℝ).with_density
      (λ x, √(2πs²)⁻¹ exp (-(x - m)² / 2s²)) else δ(m)
  ```
  Then, we say a measure `μ` on the topological vector space `E` is Gaussian if for all
  `l : E →L[ℝ] ℝ`, `μ.map l` is a Gaussian measure on `ℝ`.

The first definition has the advantage of not having a if then else definition while it is
easier to work with the second definition as we have the density readily. We will use the
second definition.
-/



open measure_theory filter real

lemma real.neg_volume_eq : (volume : measure ℝ).map (has_neg.neg) = volume :=
begin
  ext1 s hs,
  rw [measure.map_apply measurable_neg hs, set.neg_preimage, measure.add_haar_preimage_neg],
end

lemma integral_eq_zero_of_eq_neg {f : ℝ → ℝ} (hf : ∀ x, f x = -f (-x)) :
  ∫ x, f x = 0 :=
begin
  by_cases hfint : integrable f,
  swap, { exact integral_undef hfint },
  rw [← integral_univ, ← @set.Iio_union_Ici _ _ (0 : ℝ),
    integral_union _ measurable_set_Ici hfint.integrable_on hfint.integrable_on,
    add_comm, add_eq_zero_iff_eq_neg, ← integral_neg],
  have : ∫ x in set.Iio 0, -f x = ∫ x in set.Ici 0, -f (-x),
  { change _ = ∫ x in set.Ici 0, (-f) (-x),
    rw [(by simp : set.Ici (0 : ℝ) = has_neg.neg ⁻¹' (set.Iic 0)),
      ← set_integral_map measurable_set_Iic];
    try { rw real.neg_volume_eq },
    { exact set_integral_congr_set_ae Iio_ae_eq_Iic },
    { exact hfint.1.neg },
    { exact ae_measurable_id'.neg },
    all_goals { apply_instance } },
  { rw this,
    congr,
    exact funext hf },
  { rintro r ⟨hlt, hge⟩,
    exact (lt_of_lt_of_le hlt hge).ne rfl }
end

example : ∫ (x : ℝ), x * exp (-x ^ 2) = 0 :=
begin
  refine integral_eq_zero_of_eq_neg (λ x, _),
  simp only [neg_sq, neg_mul, neg_neg],
end

open_locale nnreal ennreal probability_theory measure_theory real

namespace measure_theory

open real

noncomputable def gaussian_density (m s : ℝ) : ℝ → ℝ≥0∞ :=
λ x, ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)

/-- We say a real measure is Gaussian if there exists some `m s : ℝ` such that the Radon-Nikodym
derivative of `μ` with respect to the Lebesgue integral is the Gaussian density with mean `m` and
standard deviation `s`. -/
def measure.real_gaussian (μ : measure ℝ) (m s : ℝ) : Prop :=
if s ≠ 0 then μ = volume.with_density (gaussian_density m s) else μ = measure.dirac m

open probability_theory measure

variables {μ : measure ℝ} {m s : ℝ}


lemma mulone_eq (g : ℝ → ℝ) (f : ℝ → ℝ): ∫ (x : ℝ) in set.univ, g (f x)
= ∫ (x : ℝ) in set.univ, 1 • g (f x) :=
begin
simp,
end





lemma onenng : 0 ≤ 1 := zero_le 1

lemma detid_eq_one : |(continuous_linear_map.id ℝ ℝ).det| = 1 :=
begin
have h_deteq : (continuous_linear_map.id ℝ ℝ).det = linear_map.det (linear_map.id),
  refl,
rw h_deteq,
simp,
end

lemma integ_smul_eq_mul (f : ℝ → ℝ) (g : ℝ → ℝ): ∫ (x : ℝ) in set.univ, 1 • g (f x)
 = ∫ (x : ℝ) in set.univ, |(continuous_linear_map.id ℝ ℝ).det| • g (f x) :=
begin
rw detid_eq_one,
simp,
end

-- change of variables
lemma change_of_vr_gaussian /-(μ : measure ℝ)-/:
   ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) = ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)):=
begin
    let g : ℝ → ℝ := λ (x:ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
    let f : ℝ → ℝ := λ (x:ℝ), x-m,
    have h_set_eq : set.univ = f '' set.univ,
      {ext e,
      split,
      {intro h1,
      use (e+m),
      split,
      simp,
      simp_rw [f],
      simp},
      {intro h2,
      simp}},

    have h_integ_eq : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2))
     = ∫ (x : ℝ) in set.univ, g (x-m) ,
      {simp_rw [g],
        simp},

    rw h_integ_eq,

    have h_integ_eq2 : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))
     = ∫ (x : ℝ) in set.univ, g x ,
      {simp_rw [g],
        simp},

    rw h_integ_eq2,
    nth_rewrite 1 [h_set_eq],

    have h_comp_eq : ∀ (x:ℝ), g (x-m) = g (f x),
      {intro x,
      simp},

    simp_rw [h_comp_eq],
    let f_deriv : ℝ →L[ℝ] ℝ := continuous_linear_map.id ℝ ℝ,
    let f': ℝ → (ℝ →L[ℝ] ℝ) := λ x, continuous_linear_map.id ℝ ℝ,

    rw mulone_eq g f,
    rw integ_smul_eq_mul f g,

    have h_use_f'_tosubst : ∫ (x : ℝ) in set.univ, |(continuous_linear_map.id ℝ ℝ).det| • g (f x)
     = ∫ (x : ℝ) in set.univ, |(f' x).det| • g (f x),
     {refl},

    rw h_use_f'_tosubst,

    have hf : set.inj_on f set.univ,
      refine set.injective_iff_inj_on_univ.mp _,
      unfold function.injective,
      intros a1 a2,
      simp_rw[f],
      simp,

    have hf' : ∀ (x : ℝ), x ∈ set.univ → has_fderiv_within_at f (f' x) set.univ x,
      {intros x hx,
      refine has_fderiv_within_at.sub_const _ m,
      exact has_fderiv_within_at_id x set.univ},
      {rw ← integral_image_eq_integral_abs_det_fderiv_smul ℙ measurable_set.univ hf' hf g},

end


-- 0 < s^2
lemma s_sq_pos (s : ℝ) (hs : s ≠ 0): 0 < s^2 :=
begin
  exact (sq_pos_iff s).mpr hs,
end

-- 0 < 2*s^2
lemma s_sq_pos_2 (s : ℝ) (hs : s ≠ 0): 0 < 2*s^2 :=
begin
  simp,
  exact s_sq_pos s hs,
end

-- nonegative x with sqrt equals to 0 is equal to zero
lemma pos_sqrt_zero_eq_zero : ∀ (x:ℝ), x ≥ 0 → sqrt x = 0 → x = 0 :=
begin
  intros x hx h,
  rw ← sq_sqrt hx,
  simp,
  exact h,
end

-- 0 < 2*π*s^2
lemma s_sq_pos_2_pi (s : ℝ) (hs : s ≠ 0): 0 < 2*π*s^2 :=
begin
  ring_nf,
  simp [s_sq_pos_2 s hs],
  exact pi_pos,
end

-- commutativity inside the integral
lemma comm_in_integ (f : ℝ → ℝ) (c : ℝ):
    ∫ x : ℝ, (f x) * c ∂ℙ = ∫ x : ℝ, c * f x :=
begin
simp_rw [mul_comm],
end

-- to remove the certain bracket of (2 • π) • s ^ 2
--change it into 2 • π • s ^ 2
lemma smul_no_bracket (s : ℝ): (2 • π) • s ^ 2 = 2 • π • s ^ 2 :=
begin
simp,
exact mul_assoc 2 π (s^2),
end

lemma change_onemul_to_smul (f:ℝ → ℝ): ∫ (x : ℝ), f x * (sqrt (2 * π * s ^ 2))⁻¹
 = ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹:=
begin
simp_rw[← smul_eq_mul],
end


lemma like_gaussian_eval (s:ℝ) (hs : s≠0): ∫ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)) = sqrt (2 * π * s ^ 2) :=
begin
  have h : s * s⁻¹ = 1,
    finish,
  have h_inveq : (2*s^2)⁻¹ = (s ^ 2)⁻¹ * 2⁻¹,
    ring_nf,
    simp,
    ring,
  rw ← h_inveq,
  simp_rw [← neg_mul],
  rw integral_gaussian (2*s^2)⁻¹,
  ring_nf,
  simp,
end

lemma sqrt_not_zero (s:ℝ) (hs : s≠0): sqrt (2*π*s^2) ≠ 0:=
begin
  have h_conpos : ∀ (x:ℝ), x ≥ 0 → x ≠ 0 → sqrt x ≠ 0 ,
    intros x hx h,
    exact mt (pos_sqrt_zero_eq_zero x hx) h,

  apply h_conpos,
  exact le_of_lt (s_sq_pos_2_pi s hs),
  exact ne_of_gt (s_sq_pos_2_pi s hs),

end

lemma mul_inv_eq_one (a:ℝ) (ha: a≠0): a * a⁻¹ = 1:=
begin
finish,
end

---important result below

lemma is_probability_measure_real_gaussian (hμ : μ.real_gaussian m s) :
  is_probability_measure μ :=
begin
  rw real_gaussian at hμ,
  split_ifs at hμ,
 {
    unfold gaussian_density at hμ,
    refine {measure_univ := _},
    rw hμ,
    simp only [mul_inv_rev, neg_mul, with_density_apply, measurable_set.univ, restrict_univ],
    rw ← measure_theory.of_real_integral_eq_lintegral_of_real,

    {rw change_of_vr_gaussian,
     let f : ℝ → ℝ := λ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
     have h_changeform : ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))
    = ∫ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * f x,
      refl,
    rw h_changeform,
    rw ← comm_in_integ f (sqrt (2 * π * s ^ 2))⁻¹,
    rw change_onemul_to_smul f,
    have h_integral_smul_const_special : ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹ ∂ℙ
    = (∫ (x : ℝ), f x ∂ℙ) • (sqrt (2 * π * s ^ 2))⁻¹,
      {
        exact integral_smul_const f (sqrt (2 * π * s ^ 2))⁻¹,
      },
    rw h_integral_smul_const_special,
    simp_rw [f],
    rw like_gaussian_eval s h,
    simp [h],
    have h_sqrt_not_zero : sqrt (2*π*s^2) ≠ 0,
      {exact sqrt_not_zero s h},

    rw mul_inv_eq_one (sqrt (2*π*s^2)) h_sqrt_not_zero,
    simp,
    ---exact μ,
    },
    {
      rw integrable, fconstructor,
      {
        measurability,
      },
      {
        refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)))).mp
  _,
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ (sqrt (2 * π * s ^ 2))⁻¹,

        have neg_h_inveq : -(2*s^2)⁻¹ = -(s ^ 2)⁻¹ * 2⁻¹,
        { simp [mul_comm] },

        have hb : 0 < (2*s^2)⁻¹ := inv_pos.mpr (s_sq_pos_2 s h),

        have h_gaussexp : integrable (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * a ^ 2)) ℙ,
          rw ← neg_h_inveq,
          exact integrable_exp_neg_mul_sq hb,

        have h_eqfunc : (λ (a : ℝ), exp (-(s ^ 2)⁻¹ * 2⁻¹ * (a - m)^ 2)) = (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * (a - m) ^ 2)))  ,
          ext x,
          simp,

        rw ← h_eqfunc,
        exact measure_theory.integrable.comp_sub_right h_gaussexp m,
      }
    },
    {refine filter.eventually_of_forall _,

      have h_exppos : 0 < (2 * s ^ 2) * π,
        exact mul_pos (s_sq_pos_2 s h) pi_pos,

      have h_sqrt_pos :  0 < sqrt(2 * s ^ 2 * π),
        exact sqrt_pos.mpr h_exppos,

      have  h_const_pos :  0 < (sqrt(2 * s ^ 2 * π))⁻¹,
        exact inv_pos.mpr h_sqrt_pos,
      have h_mulpi_eq : 2 * s ^ 2 * π = 2 * π * s ^ 2,
        ring,

      rw h_mulpi_eq at h_const_pos,
      intro x,
      have h_compexp_pos : 0 < exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)),
        exact real.exp_pos (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)),
      simp,
      rw  le_iff_lt_or_eq,
      left,
      exact mul_pos h_const_pos h_compexp_pos,
    }
  },

   -- the lemma `integral_gaussian` is useful!
  { refine {measure_univ := _},
  rw hμ,
  simp
  },
end





lemma gaussian_density_ennreal (hs : s ≠ 0) : ∀ (x:ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)≥ 0 :=
begin
  intro x,
  simp,
  have h_exp_pos :  exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) > 0 := (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)).exp_pos,
  have h_invsqrt_pos : (sqrt (2 * π * s ^ 2))⁻¹ > 0,
    {simp,
    exact s_sq_pos_2_pi s hs},
  have h_prod_of_poses_pos : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) > 0 := mul_pos h_invsqrt_pos h_exp_pos,
  exact le_of_lt h_prod_of_poses_pos,
end

lemma eq_integ_in_univ : ∫ (x : ℝ), id x ∂μ =  ∫ (x : ℝ) in set.univ, id x ∂μ :=
begin
  simp,
end

lemma univ_eq_nneg_union_neg : set.univ = {x:ℝ|0≤x} ∪ {x:ℝ|x<0}:=
begin
ext x,
split,
{intro hx,
simp,
exact le_or_lt 0 x},
{intro hx,
simp},
end


---define the equivalent gaussian density mapping ℝ → ℝ≥0 instead
---of ℝ → ℝ≥0∞;
---we do this for later using integral_with_density_eq_integral_smul
noncomputable def gaussian_density_to_nnreal (m s : ℝ) : ℝ → ℝ≥0 :=
λ x, ennreal.to_nnreal (ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2))

lemma eqform_of_gauden_to_nnreal : ∀ (x:ℝ), gaussian_density m s x = gaussian_density_to_nnreal m s x:=
---λ x, ennreal.to_nnreal (ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)):=
begin
  unfold gaussian_density,
  unfold gaussian_density_to_nnreal,
  simp,
end

lemma eqform_of_gauden_mea : measurable (gaussian_density_to_nnreal m s):=
begin
  unfold gaussian_density_to_nnreal,
  measurability,
end



lemma simple_thing (x:ℝ) (hx : 0 ≤ x): x = ((ennreal.of_real x).to_nnreal):=
begin
  unfold ennreal.of_real,
  simp [hx],
end

lemma not_that_simple_thing (hs : s ≠ 0): ∀ (x:ℝ),
  (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x
  = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal • x :=
begin
  intro x,
  rw smul_eq_mul,
  have h_smul_eq_mul : (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal • x
   = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal * x,
   {exact rfl},

  rw h_smul_eq_mul,

  have h_exprepos : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) ≥ 0,
    {exact gaussian_density_ennreal hs x},

  have h_no_smul_eq : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)
    = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal,
    {exact simple_thing ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) h_exprepos},

  by_cases (x=0),
  rw h,
  simp,
  have h_nonneg_smul_nneg_eq : ∀ (a b : ℝ), a = b ↔ a * x = b * x,
    {intros a b,
    split,
    intro h1,
    simp,
    left,
    exact h1,
    intro h2,
    simp [h] at h2,
    exact h2},
  rw ← mul_assoc (sqrt (2 * π * s ^ 2))⁻¹  (exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) x,
  rw ← h_nonneg_smul_nneg_eq ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal,
  exact h_no_smul_eq,
end

lemma simp_inv (a b : ℝ) (hb : b ≠ 0): a = a * b * b⁻¹ :=
begin
  have h_mulassoc : a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc a b b⁻¹,
  rw h_mulassoc,
  simp [hb],
end

lemma twos_neq_zero (hs : s ≠ 0) : sqrt (2 * s^2) ≠ 0 :=
begin
  have h_conpos : ∀ (x:ℝ), x ≥ 0 → x ≠ 0 → sqrt x ≠ 0 ,
    intros x hx h,
    exact mt (pos_sqrt_zero_eq_zero x hx) h,

  apply h_conpos,
  simp,
  exact sq_nonneg s,
  simp,
  exact hs,
end

--sqrt (2 * s ^ 2 * π) ≠ 0
lemma two_pi_neq_zero (hs : s ≠ 0) : sqrt (2 * s ^ 2 * π) ≠ 0 :=
begin
  have h_conpos : ∀ (x:ℝ), x ≥ 0 → x ≠ 0 → sqrt x ≠ 0 ,
    intros x hx h,
    exact mt (pos_sqrt_zero_eq_zero x hx) h,

  apply h_conpos,
  simp,
  --s_sq_pos_2_pi
  rw mul_assoc,
  rw mul_comm (s^2) π,
  rw ← mul_assoc,
  apply has_lt.lt.le,
  exact s_sq_pos_2_pi s hs,
  simp,
  apply not_or,
  exact hs,
  exact  real.pi_ne_zero,
end


lemma simplify_sqrt_and_square_in_exp (hs : s≠0) : ∀ (x:ℝ),
exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) =
exp (-((sqrt (2 * s ^ 2))⁻¹ * (x - m)) ^ 2):=
begin
  intro x,
  simp,
  have h_squarenn : 0 ≤ s^2 := sq_nonneg s,

  have h1 : sqrt (s ^ 2) ^ 2 = s ^ 2,
    {simp [h_squarenn]},

  have h2 : (sqrt 2)⁻¹ ^ 2 = 2⁻¹,
    {
      simp,
    },

  have h3 : ((sqrt (s ^ 2))⁻¹ * (sqrt 2)⁻¹ * (x - m)) ^ 2 =
  ((sqrt (s ^ 2))⁻¹ ^ 2) * ((sqrt 2)⁻¹ ^ 2) * (x - m) ^ 2,
    {ring_nf},

  rw h3,

  have h_eliminate_sqrt_s: (sqrt (s ^ 2))⁻¹ ^ 2 = (s^2)⁻¹,
    {
      simp [h1],
    },
  simp [h_eliminate_sqrt_s, h2],

end


lemma simplify_sqrt_and_square_out_exp (hs : s≠0) : ∀ (x:ℝ),
(sqrt (2 * s ^ 2) * ((sqrt (2 * s ^ 2))⁻¹ * (x - m)) + m) = x :=
begin
  intro x,
  rw ← mul_assoc (sqrt (2 * s ^ 2)) (sqrt (2 * s ^ 2))⁻¹  (x - m),
  have h1 : sqrt (2 * s ^ 2) ≠ 0 := twos_neq_zero hs,
  have h2 : ∀ (x:ℝ), x≠0 → x * x⁻¹ = 1,
    {intros x hx,
    finish},
  have h2 : (sqrt (2 * s ^ 2)) * (sqrt (2 * s ^ 2))⁻¹ = 1 := h2 (sqrt (2 * s ^ 2)) h1,
  rw h2,
  simp,

end




lemma simplify_left_for_change_of_vr (hs : s≠0): ∀ (x:ℝ), /-(sqrt (2 * s ^ 2))⁻¹ *--/ (exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) * x)
= (exp (-((sqrt (2 * s ^ 2))⁻¹ * (x - m)) ^ 2) * (sqrt (2 * s ^ 2) * ((sqrt (2 * s ^ 2))⁻¹ * (x - m)) + m)) :=
begin
  intro x,
  ---simp,
  simp_rw [← simplify_sqrt_and_square_in_exp hs],
  simp_rw [simplify_sqrt_and_square_out_exp hs],

end

lemma simplify_right_for_change_of_vr (hs : s≠0): ∀ (x:ℝ),
(sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2) =
exp (-x ^ 2) * (sqrt 2 * sqrt (s ^ 2) * x + m) :=
begin
  intro x,
  simp [mul_comm, hs],
end


lemma equiv_change (func1 func2 : ℝ → ℝ) (c : ℝ) (hc : c≠0):
  ∫ (x : ℝ) in set.univ, c⁻¹ * func1 x  = ∫ (x : ℝ) in set.univ, func2 x
  →  ∫ (x : ℝ) in set.univ, func1 x  = ∫ (x : ℝ) in set.univ, (func2 x) • c :=
begin
  have h_no_univ1 : ∫ (x : ℝ) in set.univ, c⁻¹ * func1 x = ∫ (x : ℝ), c⁻¹ * func1 x,
  {simp},
  have h_no_univ2 : ∫ (x : ℝ) in set.univ, func2 x = ∫ (x : ℝ), func2 x,
  {simp},
  have h_no_univ3 : ∫ (x : ℝ) in set.univ, func1 x = ∫ (x : ℝ), func1 x,
  {simp},
  have h_no_univ4 : ∫ (x : ℝ) in set.univ, func2 x • c = ∫ (x : ℝ), func2 x • c,
  {simp},
  rw [h_no_univ1, h_no_univ2, h_no_univ3, h_no_univ4],


  {intro h1,
  rw ← comm_in_integ func1 c⁻¹ at h1,
  simp_rw [← smul_eq_mul] at h1,
  rw integral_smul_const func1  c⁻¹ at h1,
  have h_mulc2sides : ((∫ (x : ℝ), func1 x) • c⁻¹) • c = (∫ (x : ℝ), func2 x) • c,
    {simp [h1],},

  have h_cancel_cinvc : ((∫ (x : ℝ), func1 x) • c⁻¹) • c = ∫ (x : ℝ), func1 x,
    {
      simp [mul_assoc (∫ (x : ℝ), func1 x) c⁻¹ c],
      finish,
    },
  rw h_cancel_cinvc at h_mulc2sides,
  rw integral_smul_const func2 c,
  assumption,
  },


end


lemma rw_for_change (s : ℝ) (g : ℝ → ℝ ): ∫ (x : ℝ) in set.univ, g x * (sqrt 2 * sqrt (s ^ 2))
 = ∫ (x : ℝ) in set.univ, g x • (sqrt 2 * sqrt (s ^ 2)) :=
begin
  simp,
end

---rewrite the form of integration in change_of_vr_momentone_gaussian to apply rw_for_change
lemma eq_form_of_comp (f : ℝ → ℝ) (g : ℝ → ℝ) : ∫ (x : ℝ) in set.univ, g (f x)
 = ∫ (x : ℝ) in set.univ, (g ∘ f) x :=
begin
  simp,
end

lemma eq_form_of_comp_back (f : ℝ → ℝ) (g : ℝ → ℝ) : ∫ (x : ℝ) in set.univ, (sqrt 2 * sqrt (s ^ 2))⁻¹ * (g ∘ f) x
 =  ∫ (x : ℝ) in set.univ, (sqrt 2 * sqrt (s ^ 2))⁻¹ * g (f x) :=
begin
  simp,
end


lemma sqrt_split_nonzero (hs : s ≠ 0) : sqrt 2 * sqrt (s ^ 2) ≠ 0 :=
begin
  rw real.sqrt_sq_eq_abs,
  simp [hs],
end

lemma det_constmulid_eq_const : | (((sqrt 2 * sqrt (s ^ 2))⁻¹) • continuous_linear_map.id ℝ ℝ).det| = ((sqrt 2 * sqrt (s ^ 2))⁻¹) :=
begin
  have h_detid_eq_one : |(continuous_linear_map.id ℝ ℝ).det| = 1 := detid_eq_one,
  have h_deteq : (((sqrt 2 * sqrt (s ^ 2))⁻¹) • continuous_linear_map.id ℝ ℝ).det = linear_map.det (((sqrt 2 * sqrt (s ^ 2))⁻¹) • linear_map.id),
    refl,
  rw h_deteq,
  simp [h_detid_eq_one, sqrt_sq_eq_abs],
end

lemma mul_const_eq_mul_det (f g : ℝ → ℝ) : ∫ (x : ℝ) in set.univ, (sqrt 2 * sqrt (s ^ 2))⁻¹ * g (f x)
 = ∫ (x : ℝ) in set.univ, | (((sqrt 2 * sqrt (s ^ 2))⁻¹) • continuous_linear_map.id ℝ ℝ).det| * g (f x):=
begin
simp_rw det_constmulid_eq_const,
end


lemma sqrt_s_square_nonzero (hs : s≠0) : sqrt (s^2) ≠ 0 :=
begin
  rw real.sqrt_sq_eq_abs,
  simp [hs],
end


variables {E F : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
[normed_add_comm_group F] [normed_space ℝ F]

lemma has_deriv_invariant_under_mul (func : E → E) (func' : E → (E →L[ℝ] E)) (x : E)
(h_deriv : has_fderiv_within_at func (func' x) set.univ x) (c:ℝ):
has_fderiv_within_at (c•func) (c•func' x) set.univ x:=
begin
---simp at *,
exact has_fderiv_within_at.const_smul h_deriv c,
---exact has_fderiv_within_at.const_mul h_deriv c,
end


lemma exchange_2sides (a b : E): a=b ↔ b=a :=
begin
  tauto,
end

---lemma set_eq (hs : s≠0): set.univ = λ (x:ℝ), ((sqrt (2 * s ^ 2))⁻¹) * (x-m):=
lemma change_of_vr_momentone_gaussian (hs: s≠0):
∫ (x : ℝ), exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x
 = ∫ (x : ℝ), ((sqrt (2 * s ^ 2))* x + m) * exp (- x ^ 2) * (sqrt (2*s^2)):=
begin
  let g : ℝ → ℝ := λ (x:ℝ), exp (- x ^ 2) * ((sqrt (2 * s ^ 2))*x + m),
  let f : ℝ → ℝ := λ (x:ℝ), (sqrt (2 * s ^ 2))⁻¹ * (x-m),

  have h_set_eq : set.univ = f '' set.univ,
    {ext e,
    split,
    {intro h1,
    use (sqrt (2 * s ^ 2))*e+m,
    split,
    {simp},
    {simp_rw [f],
    ---simp,
    ring_nf,
    rw ← simp_inv e (sqrt (2 * s ^ 2)) (twos_neq_zero hs),
    },
    },
    {intro h2,
    simp}},
  simp,

  have h_integ_eq_form1 : ∫ (x : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)) * x
   = ∫ (x : ℝ) in set.univ, g ( (sqrt (2 * s ^ 2))⁻¹ * (x-m)) ,
    {
      simp_rw [g],
      simp_rw [← simplify_left_for_change_of_vr hs],
      simp,
    },
  rw h_integ_eq_form1,

  have h_integ_eq_form2 : ∫ (x : ℝ), (sqrt 2 * sqrt (s ^ 2) * x + m) * exp (-x ^ 2) * (sqrt 2 * sqrt (s ^ 2))
   = ∫ (x : ℝ) in set.univ, (g x) * (sqrt 2 * sqrt (s ^ 2)),
   {
    simp_rw [g],
    simp,
    simp_rw [simplify_right_for_change_of_vr hs],
   },

  rw h_integ_eq_form2,

  rw rw_for_change s g,

  have h_intermsof_gf : ∫ (x : ℝ) in set.univ, g ((sqrt (2 * s ^ 2))⁻¹ * (x - m))
   = ∫ (x : ℝ) in set.univ, g (f x),
  {simp_rw [f],},

  rw h_intermsof_gf,
  rw eq_form_of_comp f g,
  apply equiv_change (g ∘ f) g (sqrt 2 * sqrt (s ^ 2)) (sqrt_split_nonzero hs),
  rw eq_form_of_comp_back f g,
  ---

  let f': ℝ → (ℝ →L[ℝ] ℝ) := λ x, ((sqrt 2 * sqrt (s ^ 2))⁻¹ • continuous_linear_map.id ℝ ℝ),
  rw mul_const_eq_mul_det f g,

  /-have h_subst_f' : ∀ (x:ℝ), |(f' x).det| =  (sqrt 2 * sqrt (s ^ 2))⁻¹,
    {intro x,
    simp_rw [f'],
    exact det_constmulid_eq_const,},-/

  have h_subst_f'_integ :  ∫ (x : ℝ) in set.univ, |(f' x).det| * g (f x)
  = ∫ (x : ℝ) in set.univ, |((sqrt 2 * sqrt (s ^ 2))⁻¹ • continuous_linear_map.id ℝ ℝ).det| * g (f x),
    {simp_rw [f'],},

  have h_change_one_smul_to_mul : ∫ (x : ℝ) in set.univ, |(f' x).det| * g (f x)
  = ∫ (x : ℝ) in set.univ, |(f' x).det| • g (f x),
    {simp,},

  rw [← h_subst_f'_integ, h_change_one_smul_to_mul],
  nth_rewrite 1 h_set_eq,

  have hf : set.inj_on f set.univ,
      {refine set.injective_iff_inj_on_univ.mp _,
      unfold function.injective,
      intros a1 a2,
      simp_rw[f],
      simp [sqrt_s_square_nonzero hs],},
  let f_pre : ℝ → ℝ := λ (x:ℝ), x-m,
  let f'_pre : ℝ → (ℝ →L[ℝ] ℝ) := λ x, continuous_linear_map.id ℝ ℝ,

  have h_f_eq_fpre_smul_const : f = ((sqrt 2 * sqrt (s ^ 2))⁻¹) • f_pre,
    {ext x,
    simp,},

  have h_f'_eq_f'pre_smul_const : f' = ((sqrt 2 * sqrt (s ^ 2))⁻¹) • f'_pre,
    {ext x,
    simp,},

  ---We've proved f = const • f_pre and f' = const • f'_pre.
  ---and we have has_fderiv_within_at f_pre (f'_pre x) set.univ x,
  ---which is proved in change_of_vr_gaussian hf'.
  ---Copy that but rename as hf'_pre here.
  ---Apply lemma has_deriv_invariant_under_mul to the hf', we exact hf'_pre
  have hf'_pre : ∀ (x : ℝ), x ∈ set.univ → has_fderiv_within_at f_pre (f'_pre x) set.univ x,
      {intros x hx,
      refine has_fderiv_within_at.sub_const _ m,
      exact has_fderiv_within_at_id x set.univ},

  have hf' : ∀ (x : ℝ), x ∈ (set.univ : set ℝ) → has_fderiv_within_at f (f' x) set.univ x,
    {intros x hx,
    rw [h_f_eq_fpre_smul_const, h_f'_eq_f'pre_smul_const],
    specialize hf'_pre x hx,
    ---refine has_fderiv_at.const_smul hf'_pre (sqrt 2 * sqrt (s ^ 2))⁻¹,

    exact has_deriv_invariant_under_mul f_pre f'_pre x hf'_pre (sqrt 2 * sqrt (s ^ 2))⁻¹,
    },

  have h_f_eq_lambdaf : f = λ (x:ℝ), f x,
    {
      simp,    },
  rw ← integral_image_eq_integral_abs_det_fderiv_smul,-- volume measurable_set.univ hf' hf g,
  exact measurable_set.univ,
  rw ← h_f_eq_lambdaf,
  { intros x hx, convert hf' x _,
  simp, },
  exact hf,
end



lemma ez_cal: (λ(x : ℝ),(sqrt (2 * s ^ 2) * x + m) * exp (-x ^ 2)) =  (λ(x : ℝ),(sqrt (2 * s ^ 2) * x * exp(-x^2)) +  (m * exp(-x^2))) :=
begin
  ext x,
  rw right_distrib,

end


lemma h_depart: (∫ (x : ℝ), (sqrt (2 * s ^ 2) * x + m) * exp (-x ^ 2)) = (∫ (x : ℝ), sqrt (2 * s ^ 2) * x * exp(-x^2) ) + (∫ (x : ℝ), m * exp(-x^2)) :=
begin
  rw ez_cal,
  let f : ℝ → ℝ := λ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2),

  have h_changeform1 :∫ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2) + m * exp (-x ^ 2) = ∫ (x : ℝ), f x + m * exp (-x ^ 2),
  {
    simp_rw[f],
  },
  rw h_changeform1,

  have h_changeform2 :(∫ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2)) = (∫ (x : ℝ), f x),
  {
    simp_rw[f],
  },
  rw h_changeform2,
  let  g: ℝ → ℝ := λ (x : ℝ), m * exp (-x ^ 2),

  have h_changeform3 :∫ (x : ℝ), f x + m * exp (-x ^ 2) = ∫ (x : ℝ), f x + g x,
  {
     simp_rw[g],
    },
  rw h_changeform3,

  have h_changeform4 :∫ (x : ℝ), m * exp (-x ^ 2) = ∫ (x : ℝ), g x,
  {
     simp_rw[g],
    },
  rw h_changeform4,
  have hf : measure_theory.integrable f ℙ,
  {
      rw integrable, fconstructor,
      {measurability,},
      {
        refine (has_finite_integral_norm_iff f).mp _,
        simp_rw[f],
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        have h₁: (λ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2)) = (λ (x : ℝ), sqrt (2 * s ^ 2) * (x * exp (-x ^ 2))),
          {
            ext x,
            rw mul_assoc,
          },
        rw h₁,
        refine integrable.const_mul _ (sqrt(2 * s ^ 2)),
        have hb: (0 : ℝ )<1,
          {simp,},
        have hs: (-1 : ℝ) < 1,
          {simp,},
        have h₂: (λ (x : ℝ), x * exp (-x ^ 2)) = (λ (x : ℝ), x^1 * exp ((-1) *x ^ 2)),
          {simp,},
        rw h₂,
        let k := @integrable_rpow_mul_exp_neg_mul_sq 1 hb 1 hs,
        norm_num,
        norm_num at k,
        exact k,
      },
    },
  have hg : measure_theory.integrable g ℙ,
    {
      rw integrable, fconstructor,
      {measurability},
      {
        simp_rw[g],
        have hb: (0 : ℝ )<1,
          {simp,},
        refine (has_finite_integral_norm_iff g).mp _,
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ m,
        have h₁ : (λ (a : ℝ), exp (-a ^ 2)) = (λ (a : ℝ), exp ((-1)*a ^ 2)),
          {simp,},
        rw h₁,
        exact integrable_exp_neg_mul_sq hb,
      },
    },
  rw measure_theory.integral_add hf hg,
end

lemma change_onemul_to_smul_k (f:ℝ → ℝ): ∫ (x : ℝ), f x * sqrt (2 * s ^ 2)
 = ∫ (x : ℝ), f x • sqrt (2 * s ^ 2):=
begin
simp_rw[← smul_eq_mul],
end




lemma change_onemul_to_smul_t (f:ℝ → ℝ): ∫ (x : ℝ), f x * m
 = ∫ (x : ℝ), f x • m:=
begin
simp_rw[← smul_eq_mul],
end

lemma change_onemul_to_smul_f2 (f:ℝ → ℝ): ∫ (x : ℝ), f x * sqrt (2 * s ^ 2)
 = ∫ (x : ℝ), f x • sqrt (2 * s ^ 2):=
begin
simp_rw[← smul_eq_mul],
end

---Thanks JasonKy. The following evaluation of the integration is from him.
lemma real.neg_volume_eq : (volume : measure ℝ).map (has_neg.neg) = volume :=
begin
  ext1 s hs,
  rw [measure.map_apply measurable_neg hs, set.neg_preimage, measure.add_haar_preimage_neg],
end

lemma integral_eq_zero_of_eq_neg {f : ℝ → ℝ} (hf : ∀ x, f x = -f (-x)) :
  ∫ x, f x = 0 :=
begin
  by_cases hfint : integrable f,
  swap, { exact integral_undef hfint },
  rw [← integral_univ, ← @set.Iio_union_Ici _ _ (0 : ℝ),
    integral_union _ measurable_set_Ici hfint.integrable_on hfint.integrable_on,
    add_comm, add_eq_zero_iff_eq_neg, ← integral_neg],
  have : ∫ x in set.Iio 0, -f x = ∫ x in set.Ici 0, -f (-x),
  { change _ = ∫ x in set.Ici 0, (-f) (-x),
    rw [(by simp : set.Ici (0 : ℝ) = has_neg.neg ⁻¹' (set.Iic 0)),
      ← set_integral_map measurable_set_Iic];
    try { rw real.neg_volume_eq },
    { exact set_integral_congr_set_ae Iio_ae_eq_Iic },
    { exact hfint.1.neg },
    { exact ae_measurable_id'.neg },
    all_goals { apply_instance } },
  { rw this,
    congr,
    exact funext hf },
  { rintro r ⟨hlt, hge⟩,
    exact (lt_of_lt_of_le hlt hge).ne rfl }
end

example : ∫ x, x * exp (-x ^ 2) = 0 :=
begin
  refine integral_eq_zero_of_eq_neg (λ x, _),
  simp only [neg_sq, neg_mul, neg_neg],

end--lemma eqform_of_gauden_to_nnreal_mea : measurable

lemma sqrt_cal_for_last_part(hs : s ≠ 0): sqrt π * m * (sqrt 2 * sqrt (s ^ 2)) * (sqrt (2 * π * s ^ 2))⁻¹ = m :=
begin
  rw mul_comm (sqrt π) m,
  have h₁: sqrt π * (sqrt 2 * sqrt (s ^ 2)) = sqrt (2 * π * s ^ 2),
    {
      rw[←real.sqrt_mul],
      {
        rw[←real.sqrt_mul],
        have h₂: π * (2 * s ^ 2) = 2 * π * s ^ 2,
          {
            rw mul_comm,
            ring,
          },
        rw h₂,
        apply has_lt.lt.le,
        exact pi_pos,
      },
      {
        simp,
      },
    },
  --rw ← h₁,
  rw [mul_assoc m, h₁],
  ring_nf,
  have h2 : ∀ (x:ℝ), x≠0 →  x⁻¹ * x = 1,
    {intros x hx,
    finish},
  have h3 : (sqrt (2 * s ^ 2 * π))⁻¹ * sqrt (2 * s ^ 2 * π) = 1,
    {
      rw h2,
      exact two_pi_neq_zero hs,
    },
  rw h3,
  simp,

end

lemma moment_one_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  μ[id] = m :=
begin
  have h_is_prob_mea : is_probability_measure μ,
  {exact is_probability_measure_real_gaussian hμ},
  rw real_gaussian at hμ,
  split_ifs at hμ,
  rw hμ,
  have h_lambdaform : gaussian_density m s = λ x, (gaussian_density_to_nnreal m s) x,
    {ext x,
    unfold gaussian_density,
    unfold gaussian_density_to_nnreal,
    simp},
  rw h_lambdaform,
  rw integral_with_density_eq_integral_smul eqform_of_gauden_mea id,
  unfold gaussian_density_to_nnreal,
  ---simp [gaussian_density_ennreal, hs],
  have h_eliminate_ennreal_nnreal :
  ∫ (a : ℝ), (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2))).to_nnreal • a
  = ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a,
  {
    simp_rw [← not_that_simple_thing hs],

  },
  simp_rw [id],
  rw h_eliminate_ennreal_nnreal,
  --dsimp at *,

  let f : ℝ → ℝ := λ (a : ℝ), exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a,
  have h_changeform : ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (a - m) ^ 2) • a =
  ∫ (a : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * f a,
  {
    simp_rw[f],
  },
  rw h_changeform,
  rw ← comm_in_integ f (sqrt (2 * π * s ^ 2))⁻¹,
  rw change_onemul_to_smul f,
  have h_integral_smul_const_special : ∫ (x : ℝ), f x • (sqrt (2 * π * s ^ 2))⁻¹ ∂ℙ
    = (∫ (x : ℝ), f x ∂ℙ) • (sqrt (2 * π * s ^ 2))⁻¹,
      {
        exact integral_smul_const f (sqrt (2 * π * s ^ 2))⁻¹,
      },
  rw h_integral_smul_const_special,
  simp_rw[f],
  --rw smul_eq_mul,
  /-have h_rw_to_use_change_of_vr : ∫ (x : ℝ), exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x
   = ∫ (x : ℝ), exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) • x * (sqrt (2*s^2))⁻¹,
    {
      sorry
    },-/
  rw change_of_vr_momentone_gaussian hs,
  let f2 : ℝ → ℝ := λ (x:ℝ), (sqrt (2 * s ^ 2) * x + m) * exp (-x ^ 2),
  have h_changeform_3halves : ∫ (x : ℝ), (f2 x) * sqrt (2 * s ^ 2)
  = ∫ (x : ℝ), (sqrt (2 * s ^ 2) * x + m) * exp (-x ^ 2) * sqrt (2 * s ^ 2),
    {
      simp_rw [f2],
    },
  rw ← h_changeform_3halves,
  rw change_onemul_to_smul_f2 f2,


  have h_integral_smul_const_moveout : ∫ (x : ℝ), f2 x • sqrt (2 * s ^ 2) ∂ℙ
    = (∫ (x : ℝ), f2 x ∂ℙ) • sqrt (2 * s ^ 2),
      {
        exact integral_smul_const f2 (sqrt (2 * s ^ 2)),
      },
  rw h_integral_smul_const_moveout,

  rw h_depart,

  -- move the constant of the first integral out
  let k : ℝ → ℝ := λ (x : ℝ), x * exp (-x ^ 2),
  have h_changeform2 : (∫ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2)) = (∫ (x : ℝ), sqrt (2 * s ^ 2) * k x),
    {
      simp_rw[k],
      have  remove_bracket : (λ (x : ℝ), sqrt (2 * s ^ 2) * x * exp (-x ^ 2)) = (λ (x : ℝ), sqrt (2 * s ^ 2) * (x * exp (-x ^ 2))),
        {
          ext x,
          rw mul_assoc,
        },
      rw remove_bracket,
    },
  rw h_changeform2,
  rw ← comm_in_integ k (sqrt (2 * s ^ 2)),
  rw change_onemul_to_smul_k k,
  have h_integral_smul_const_move_out : ∫ (x : ℝ), k x • sqrt (2 * s ^ 2) ∂ℙ
    = (∫ (x : ℝ), k x ∂ℙ) • sqrt (2 * s ^ 2),
      {
        exact integral_smul_const k (sqrt (2 * s ^ 2)),
      },
  rw h_integral_smul_const_move_out,

  -- move the constant of the second integral out
  let t : ℝ → ℝ := λ (x : ℝ), exp (-x ^ 2),
  have h_changeform3 : (∫ (x : ℝ), m * exp (-x ^ 2)) = (∫ (x : ℝ), m * t x),
    {
      simp_rw[t],
    },
  rw h_changeform3,
  rw ← comm_in_integ t m,
  rw change_onemul_to_smul_t t,
  have h_integral_smul_const_move_out2 : ∫ (x : ℝ), t x • m ∂ℙ
    = (∫ (x : ℝ), t x ∂ℙ) • m,
      {
        exact integral_smul_const t m,
      },
  rw h_integral_smul_const_move_out2,
  simp_rw[t],
  have ez_change_form : (λ (x : ℝ), exp (-x ^ 2)) = (λ (x : ℝ), exp ((-1)*x ^ 2)),
    {
      ext x,
      simp,
    },
  rw ez_change_form,
  rw integral_gaussian 1,
  simp,
  simp_rw[k],
  have from_JasonKY : ∫ (x : ℝ), x * exp (-x ^ 2) = 0,
    {
      refine integral_eq_zero_of_eq_neg (λ x, _),
      simp only [neg_sq, neg_mul, neg_neg],
    },
  simp_rw [from_JasonKY],
  rw zero_mul,
  rw zero_add,
  rw sqrt_cal_for_last_part hs,
end




---From here to the end of lemma absolutely_continuous_real_gaussian,
---the content are all about proving absolutely_continuous_real_gaussian.
---The part before lemma absolutely_continuous_real_gaussian is from proving
---the set {x : ℝ | gaussian_density m s ≠ 0} is set.univ. We do this
---because, once this part is done, we can immediately use measurable_set.univ
---to use the result measure_inter_add_diff.


lemma union_comm (S : set ℝ) : {x : ℝ | ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) ≠ 0} ∩ S
 = S ∩ {x : ℝ | ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) ≠ 0} :=
begin
  exact set.inter_comm {x : ℝ | ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) ≠ 0} S,
end

lemma inv_sqrt_2pis2_pos (hs : s≠0) : 0 < (sqrt (2 * π * s ^ 2))⁻¹ :=
begin
  simp,
  exact s_sq_pos_2_pi s hs,
end

lemma funcpos_anywhere (hs : s≠0) : ∀ (x:ℝ), 0 < ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)):=
begin
  intro x,
  simp [inv_sqrt_2pis2_pos hs],
  exact (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)).exp_pos,
end


lemma t_eq_set_of_posval (hs : s≠0) :
{x : ℝ | ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) ≠ 0}
 = {x : ℝ | 0 < ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))}:=
begin
  ext x,
  simp [funcpos_anywhere hs],
end


lemma t_eq_setuniv (hs : s≠0) : (set.univ : set ℝ) =
{x : ℝ | 0 < ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))}:=
begin
  ext x,
  simp [funcpos_anywhere hs x],
  simp [inv_sqrt_2pis2_pos hs],
  exact (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)).exp_pos,
end

---The third important result
-- easy direction
lemma absolutely_continuous_real_gaussian (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  μ ≪ volume :=
begin


  unfold measure.absolutely_continuous,
  unfold real_gaussian at hμ,
  intros S hPs,
  split_ifs at hμ,
  unfold gaussian_density at hμ,
  rw hμ,
  rw measure_theory.with_density_apply_eq_zero,
  {
    rw union_comm S,
    rw t_eq_set_of_posval hs,
    rw ← t_eq_setuniv hs,

    have h_inter_smaller_measure : ℙ (S ∩ set.univ) ≤ ℙ (S),
      {
        rw ← measure_inter_add_diff S measurable_set.univ,
        simp,
      },
    simp [hPs, h_inter_smaller_measure],

  },
  {measurability},


end





---From here, the content below until the end of lemma real_gaussian_absolutely_continuous
---is all about proof of lemma real_gaussian_absolutely_continuous. From here to the next
---long comment or begining of lemma funcpos_anywhere2, the conent is for proving
---ℙ = μ.with_density ((gaussian_density m s)⁻¹), or, in math language,
---Radon Nikodym derivative of Lebesgue measure ℙ with respect to gaussian measure μ
---is 1/(gaussian_density m s). We can just call this hℙ as counterpart of hμ.

---The meaning of such work is get the counterpart of hμ in  μ ≪ volume
---for proving volume ≪ μ. With this assumption, we can proving volume ≪ μ
---in a way similar to proof of μ ≪ volume, while replacing hμ by hℙ.


lemma gaussian_measurable (hs : s≠0) : measurable (gaussian_density m s):=
begin
  unfold gaussian_density,
  measurability,
end

lemma inv_gaussian_measurable (hs : s≠0) : measurable (λ (x:ℝ), ((gaussian_density m s) x)⁻¹):=
begin
  unfold gaussian_density,
  measurability,
end

lemma gaussian_pos (hs : s≠0): ∀ (x:ℝ), 0 < (gaussian_density m s) x:=
begin
  unfold gaussian_density,
  exact funcpos_anywhere hs,


end

lemma gaussian_nzero (hs : s≠0) : ∀ (x:ℝ), (gaussian_density m s) x ≠ 0 :=
begin
  intro x,
  exact ne_of_gt (gaussian_pos hs x),
end


lemma gau_eq_gautonnreal : gaussian_density m s = λ (x:ℝ), (gaussian_density_to_nnreal m s) x :=
begin
  ext x,
  unfold gaussian_density,
  unfold gaussian_density_to_nnreal,
  simp,
end


lemma lambdaform_with_tonnreal (hs : s ≠ 0) : gaussian_density m s = λ x, (gaussian_density_to_nnreal m s) x:=
begin
  ext x,
  unfold gaussian_density,
  unfold gaussian_density_to_nnreal,
  simp,
end


lemma eliminate_ofreal_tonnreal1 (hs : s ≠ 0): ∀ (x:ℝ),
  (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)
  = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal :=
begin
  intro x,
  have h_exprepos1: 0 ≤ (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2),
    {exact gaussian_density_ennreal hs x},
  have h_no_smul_eq : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)
    = (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal,
    {exact simple_thing ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) h_exprepos1,},
  rw ← h_no_smul_eq,
end


lemma eliminate_ofreal_tonnreal2 (hs : s ≠ 0): ∀ (x:ℝ),
  (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) * ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))⁻¹
  = ((ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal)
  * ((ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))).to_nnreal)⁻¹:=
begin
  intro x,
  rw eliminate_ofreal_tonnreal1 hs x,
  simp,
end


lemma ennreal_prod_eq_prod_ennreal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ennreal.of_real (a*b) = (ennreal.of_real a) * (ennreal.of_real b):=
begin
  have ha2 : 0 ≤ a := le_of_lt ha,
  have hb2 : 0 ≤ b := le_of_lt hb,

  simp_rw ennreal.of_real_mul ha2,
end


lemma inv_ennreal_eq_ennreal_inv (a : ℝ) (ha : 0 < a) : ennreal.of_real (a⁻¹) = (ennreal.of_real a)⁻¹ :=
begin
  simp_rw [ennreal.of_real_inv_of_pos ha],

end


lemma gaussian_without_ennreal_pos (hs : s≠0) : ∀ (x:ℝ),
 0 < (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2):=
begin
  intro x,
  simp [inv_sqrt_2pis2_pos hs],
  exact (-((s ^ 2)⁻¹ * 2⁻¹ * (x - m) ^ 2)).exp_pos,
end


lemma gaussian_without_ennreal_nzero (hs : s≠0) : ∀ (x:ℝ),
(sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) ≠ 0:=
begin
  intro x,
  have h_pos: 0 < (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) := gaussian_without_ennreal_pos hs x,
  exact ne_of_gt h_pos,
end


lemma in_one_ennreal (hs : s ≠ 0) : ∀ (x:ℝ),
ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))
* (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)))⁻¹
 = ennreal.of_real ( ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))
 * ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))⁻¹) :=
begin
  intro x,
  rw [ennreal.of_real_inv_of_pos (gaussian_without_ennreal_pos hs x)],
  have h : 0 ≤ ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) := le_of_lt (gaussian_without_ennreal_pos hs x),
  rw ennreal.of_real_mul h,
end


lemma in_one_ennreal_under_linteg (hs : s≠0) (S : set ℝ) (hS : measurable_set S):
∫⁻ (x : ℝ) in S, ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) * (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)))⁻¹
= ∫⁻ (x : ℝ) in S, ennreal.of_real ( ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) * ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))⁻¹) :=
begin
  simp_rw [in_one_ennreal hs],
end


lemma inside_ennreal_eq_one (hs : s ≠ 0) : ∀ (x:ℝ),
(sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)
* ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))⁻¹ = 1 :=
begin
  intro x,
  have h : (sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2) ≠ 0:=
    gaussian_without_ennreal_nzero hs x,
  rw mul_inv_eq_one ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)) h,
end


lemma rn_deriv_inv (hs : s ≠ 0) (hμ : μ.real_gaussian m s) : volume = μ.with_density (λ (x:ℝ), ((gaussian_density m s) x)⁻¹) :=
begin
  unfold real_gaussian at hμ,
  simp [hs] at hμ,
  rw hμ,
  ext1 S hS,
  rw with_density_apply (λ (x:ℝ), ((gaussian_density m s) x)⁻¹) hS,
  simp [with_density_apply (gaussian_density m s) hS],
  rw set_lintegral_with_density_eq_set_lintegral_mul ℙ (gaussian_measurable hs) (inv_gaussian_measurable hs) hS,
  simp,
  let f : ℝ → ℝ≥0∞ := λ (x:ℝ), 1,

  unfold gaussian_density,
  rw in_one_ennreal_under_linteg hs S hS,
  simp_rw [inside_ennreal_eq_one hs],
  have h_const_func : ∀ (x:ℝ), f x = ennreal.of_real 1,
    {
      intro x,
      simp,
    },
  have h_rw_linteg_about_func : (∫⁻ (x : ℝ) in S, (f x) ) = ∫⁻ (x : ℝ) in S, ennreal.of_real 1 ,
    {
      simp_rw [f],
      simp,
    },
  rw ← h_rw_linteg_about_func,
  simp,

end


---From here to lemma real_gaussian_absolutely_continuous, this part aims
---aims to show the set {x : ℝ | 0 < (gaussian_density m s x)⁻¹} equal
---to the set.univ, so that we can use the result measure_inter_add_diff
---in proof of lemma real_gaussian_absolutely_continuous like what we've
---done in the third important result.
lemma funcpos_anywhere2 (hs : s≠0) : ∀ (x:ℝ), 0 < (ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2)))⁻¹:=
begin
  have h_func_pos :  ∀ (x:ℝ), 0 < ennreal.of_real ((sqrt (2 * π * s ^ 2))⁻¹ * exp (-(2 * s ^ 2)⁻¹ * (x - m) ^ 2))
  := funcpos_anywhere hs,
  intro x,
  specialize h_func_pos x,
  simp [h_func_pos],
end


lemma t_eq_set_of_posval2 (hs : s≠0) :
{x : ℝ | (gaussian_density m s x)⁻¹ ≠ 0} = {x : ℝ | 0 < (gaussian_density m s x)⁻¹} :=
begin
  unfold gaussian_density,
  ext x,
  simp [funcpos_anywhere hs],
end

lemma t_eq_setuniv2 (hs : s≠0) : (set.univ : set ℝ) = {x : ℝ | 0 < (gaussian_density m s x)⁻¹}:=
begin
  unfold gaussian_density,
  ext x,
  simp [funcpos_anywhere2 hs x],
end
----

---The fourth important result
lemma real_gaussian_absolutely_continuous (hs : s ≠ 0) (hμ : μ.real_gaussian m s) :
  volume ≪ μ :=
begin
  -- Hint: first show/find in mathlib that for positive `f`, `∫ x in s, f x ∂μ = 0 ↔ μ s = 0`
  -- Do it on paper first!
  let f : ℝ → ℝ≥0 := λ (x:ℝ), 1,

  intros S hS,
  have hℙ : volume = μ.with_density (λ (x:ℝ), ((gaussian_density m s) x)⁻¹) := rn_deriv_inv hs hμ,
  rw hℙ,
  rw measure_theory.with_density_apply_eq_zero,
  {
  rw set.inter_comm {x : ℝ | (gaussian_density m s x)⁻¹ ≠ 0} S,
  rw [t_eq_set_of_posval2 hs, ← t_eq_setuniv2 hs],
  have h_inter_smaller_measure : μ (S ∩ set.univ) ≤ μ (S),
    {
    rw ← measure_inter_add_diff S measurable_set.univ,
    simp,
    },
    simp [hS, h_inter_smaller_measure],
  },
  {unfold gaussian_density,
  measurability},
end

section gaussian_rv

/- ### Transformation of Gaussian random variables -/
#where
variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

/-- A real-valued random variable is a Gaussian if its push-forward measure is a Gaussian measure
on ℝ. -/
def gaussian_rv (f : Ω → ℝ) (m s : ℝ) : Prop := (volume.map f).real_gaussian m s

def std_gaussian_rv (f : Ω → ℝ) : Prop := gaussian_rv f 0 1

variables {f g : Ω → ℝ} {m₁ s₁ m₂ s₂ : ℝ}


lemma ae_measurable1:
ae_measurable (λ (x:ℝ), x+m) (volume.with_density (λ (x : ℝ), ennreal.of_real ((sqrt (2 * π * 1 ^ 2))⁻¹ * exp (-(2 * 1 ^ 2)⁻¹ * (x - 0) ^ 2)))):=
begin
  let μ : measure ℝ := volume.with_density (λ (x : ℝ), ennreal.of_real ((sqrt (2 * π * 1 ^ 2))⁻¹ * exp (-(2 * 1 ^ 2)⁻¹ * (x - 0) ^ 2))),
  have h1 : ae_measurable (λ (x:ℝ), x+m) μ
  ↔ ae_measurable (λ (x:ℝ), x+m) (volume.with_density (λ (x : ℝ), ennreal.of_real ((sqrt (2 * π * 1 ^ 2))⁻¹ * exp (-(2 * 1 ^ 2)⁻¹ * (x - 0) ^ 2)))),
    {
      simp_rw [μ],
    },
  rw ← h1,
  measurability,
end

lemma mulone_eq_S (g : ℝ → ℝ) (f : ℝ → ℝ) (S : set ℝ):
 ∫ (x : ℝ) in S, g (f x) = ∫ (x : ℝ) in S, 1 • g (f x) :=
begin
simp,
end

lemma S_is_im (S : set ℝ) : {x : ℝ | x + m ∈ S} = (λ (x:ℝ), x-m) '' S :=
begin
  ext e,
  split,
  {intro h1,
  use (e+m),
  split,
  exact h1,
  simp,},
  {intro h2,
  simp at h2,
  simp [h2],
  cases h2 with x h3,
  cases h3 with h4 h5,
  rw ← h5,
  simp [h4]},
end

lemma integ_smul_eq_mul_S (f : ℝ → ℝ) (g : ℝ → ℝ) (S : set ℝ):
∫ (x : ℝ) in S, 1 • g (f x)
= ∫ (x : ℝ) in S, |(continuous_linear_map.id ℝ ℝ).det| • g (f x) :=
begin
rw detid_eq_one,
simp,
end

lemma change_of_vr_gaussian_with_var_one (S : set ℝ) (hS : measurable_set S):
 ∫ (x : ℝ) in {x : ℝ | x + m ∈ S}, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)) =
∫ (x : ℝ) in S, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * (x-m) ^ 2)):=
begin
  let h : ℝ → ℝ := λ x, x-m,
  let g : ℝ → ℝ := λ x, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)),
  rw S_is_im S,
  simp_rw [← h],
  simp_rw [← g],
  have h_eq_integ : ∫ (x : ℝ) in S, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * (x - m) ^ 2))
   = ∫ (x : ℝ) in S, g (h x),
    {
      simp_rw [g],
    },
  rw h_eq_integ,
  let h': ℝ → (ℝ →L[ℝ] ℝ) := λ x, continuous_linear_map.id ℝ ℝ,
  rw mulone_eq_S g h S,
  rw integ_smul_eq_mul_S h g S,
  have h_use_f'_tosubst : ∫ (x : ℝ) in set.univ, |(continuous_linear_map.id ℝ ℝ).det| • g (h x)
    = ∫ (x : ℝ) in set.univ, |(h' x).det| • g (h x),
    {refl},

--     rw h_use_f'_tosubst,
  have h_h : set.inj_on h S,
    {refine set.inj_on_of_injective _ S,
      ---refine set.injective_iff_inj_on_univ.mp _,
    unfold function.injective,
    intros a1 a2,
    simp_rw[h],
    simp,},

  have h_h' : ∀ (x : ℝ), x ∈ S → has_fderiv_within_at h (h' x) S x,
    {intros x hx,
    refine has_fderiv_within_at.sub_const _ m,
    exact has_fderiv_within_at_id x S},

  rw ← integral_image_eq_integral_abs_det_fderiv_smul ℙ hS h_h' h_h g,

end


--The fifth important lemma

lemma std_gaussian_rv_add_const (hf : std_gaussian_rv f) (hfmeas : measurable f) (m : ℝ) :
  gaussian_rv (f + λ x, m) m 1 :=
begin
  unfold std_gaussian_rv at hf,
  unfold gaussian_rv at *,
  unfold real_gaussian at *,
  simp at *,
  unfold gaussian_density at *,
  let h : ℝ → ℝ := λ x, x + m,
  have h_f_plus_const_eq_comb : (f + λ x, m) = h ∘ f,
    {
      ext x,
      simp,
    },
  rw h_f_plus_const_eq_comb,
  have h_hmeas : measurable h,
    {measurability},
  rw ← measure.map_map h_hmeas hfmeas,
  rw hf,
  ext1 S hS,
  have h_preim_of_S_eq_Sminusm : (h ⁻¹' S) = {x : ℝ | x + m ∈ S},
    {
      ext x,
      simp,
    },
  simp_rw[h],
  rw measure_theory.measure.map_apply_of_ae_measurable ae_measurable1 hS,
  simp,
  rw h_preim_of_S_eq_Sminusm,
  rw measure_theory.with_density_apply,
  rw measure_theory.with_density_apply,
  {
    rw ← measure_theory.of_real_integral_eq_lintegral_of_real,
    rw ← measure_theory.of_real_integral_eq_lintegral_of_real,

    {
      simp_rw [change_of_vr_gaussian_with_var_one S hS],
    },

    {
      {
      rw integrable, fconstructor,
      {
        measurability,
      },
      {
        refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * (x - m) ^ 2)))).mp
  _,
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ ((sqrt π)⁻¹ * (sqrt 2)⁻¹),
        refine measure_theory.integrable_on.integrable _,
        --hint: prove `integrable (λ (a : ℝ), exp (-(2⁻¹ * (a - m) ^ 2))) ℙ` first
        have h₁: integrable (λ (a : ℝ), exp (-(2⁻¹ * (a - m) ^ 2))) ℙ,
        {
          rw integrable, fconstructor,
          {measurability,},
          {
            refine (has_finite_integral_norm_iff (λ (a : ℝ), exp (-(2⁻¹ * (a - m) ^ 2)))).mp _,
            apply integrable.has_finite_integral _,
            refine integrable.abs _,
            simp,
            have h_eqfunc : (λ (a : ℝ), exp (-(2)⁻¹ * (a - m)^ 2)) = (λ (a : ℝ), exp (-(2⁻¹ * (a - m) ^ 2)))  ,
              {
                ext x,
                simp,
              },
            rw ← h_eqfunc,
            have hb: (0:ℝ) < (2)⁻¹,
              {simp,},
            have h_gaussexp : integrable (λ (a : ℝ), exp (-2⁻¹ * a ^ 2)) ℙ,
              {
                exact integrable_exp_neg_mul_sq hb,
              },
            exact measure_theory.integrable.comp_sub_right h_gaussexp m,
          },
        },

        simp[(measure_theory.integrable.integrable_on h₁)],
      }
    },
    },

    {
      refine filter.eventually_of_forall _,
      intro x,
      simp,
      have h₁: (sqrt π)⁻¹ * (sqrt 2)⁻¹ = (sqrt(2 * π))⁻¹,
        {
          rw ← mul_inv,
          simp,
          exact mul_comm ((sqrt 2)⁻¹) ((sqrt π)⁻¹),
        },
      rw h₁,
      have h₂: 0 < (sqrt(2 * π))⁻¹,
        {
          simp,
          exact pi_pos,
        },
      have h_compexp_pos : 0 < exp (-(2⁻¹ * (x - m) ^ 2)),
        {
          exact real.exp_pos (-(2⁻¹ * (x - m) ^ 2)),
        },
      rw  le_iff_lt_or_eq,
      left,
      exact mul_pos h₂ h_compexp_pos,
    },

    {
      rw integrable, fconstructor,
      {
        measurability,
      },
      {
        refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)))).mp
  _,
        apply integrable.has_finite_integral _,
        refine integrable.abs _,
        refine integrable.const_mul _ ((sqrt π)⁻¹ * (sqrt 2)⁻¹),
        refine measure_theory.integrable_on.integrable _,
        have h₁: integrable (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2))) ℙ,
          {
            rw integrable, fconstructor,
            {measurability,},
            {
              refine (has_finite_integral_norm_iff (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2)))).mp _,
              apply integrable.has_finite_integral _,
              refine integrable.abs _,
              simp,
              have h_eqfunc : (λ (a : ℝ), exp (-(2)⁻¹ * a^ 2)) = (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2)))  ,
                {
                  ext x,
                  simp,
                },
              rw ← h_eqfunc,
              have hb: (0:ℝ) < (2)⁻¹,
                {simp,},
              exact integrable_exp_neg_mul_sq hb,
            }
          },
        simp[(measure_theory.integrable.integrable_on h₁)],
      },
    },

    {
      refine filter.eventually_of_forall _,
      intro x,
      simp,
      have h₁: (sqrt π)⁻¹ * (sqrt 2)⁻¹ = (sqrt(2 * π))⁻¹,
        {
          rw ← mul_inv,
          simp,
          exact mul_comm ((sqrt 2)⁻¹) ((sqrt π)⁻¹),
        },
      rw h₁,
      have h₂: 0 < (sqrt(2 * π))⁻¹,
        {
          simp,
          exact pi_pos,
        },
      have h_compexp_pos : 0 < exp (-(2⁻¹ * x ^ 2)),
        {
          exact real.exp_pos (-(2⁻¹ * x ^ 2)),
        },
      rw  le_iff_lt_or_eq,
      left,
      exact mul_pos h₂ h_compexp_pos,
    },
  },
  {exact hS},
  {
    measurability,
  },

end
/-
lemma ae_measurable_zerofunc : ae_measurable (0 : ℝ → ℝ) ℙ :=
begin
measurability,
exact measurable_zero,
end
-/
lemma ae_measurable_zerofunc : ae_measurable (λ (x:ℝ), 0) ℙ :=
begin
measurability,
---exact measurable_zero,
end


lemma S_is_im2 (S : set ℝ) (s : ℝ) (hs : s≠0) : {x : ℝ | s • x ∈ S} = (λ (x:ℝ), s⁻¹ * x) '' S :=
begin
  ext e,
  split,
  {intro h1,
  use (s • e),
  split,
  exact h1,
  simp,
  rw ← mul_assoc s⁻¹ s e,
  rw mul_comm s⁻¹ s,
  simp_rw [mul_inv_eq_one s hs],
  simp,
  },
  {intro h2,
  simp at h2,
  simp [h2],
  cases h2 with x h3,
  cases h3 with h4 h5,
  rw ← h5,
  rw ← mul_assoc s s⁻¹ x,
  simp_rw [mul_inv_eq_one s hs],
  simp [hs],
  exact h4,},
end

lemma integ_taking_s_out (S : set ℝ) (s : ℝ) (hs : s ≠ 0) :
∫ (x : ℝ) in S, (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)) =
∫ (x : ℝ) in S, |s⁻¹| * (sqrt (2 * π))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)):=
begin
  have h_2pipos : 0 < 2 * π := two_pi_pos,
  have h2pi_nneg : 0 ≤ 2 * π,
    {
      nlinarith,
    },
  have h_sqrt_split : (sqrt (2 * π * s ^ 2))⁻¹ =  (sqrt (2 * π) * sqrt (s ^ 2))⁻¹,
    {
      simp [h2pi_nneg],
    },
  have h_abs_s : sqrt (s ^ 2) = |s| := real.sqrt_sq_eq_abs s,
  have h_coe_eq : (sqrt (2 * π * s ^ 2))⁻¹ = |s⁻¹| * (sqrt (2 * π))⁻¹,
    {
      rw [h_sqrt_split, h_abs_s],
      simp,
      left,
      simp [abs_inv s],
    },
  simp_rw [h_coe_eq],

end

lemma integ_put_s_x_together (S : set ℝ) (hS : measurable_set S) (s : ℝ) (hs : s≠0):
∫ (x : ℝ) in S, |s⁻¹| * (sqrt (2 * π))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2))
= ∫ (x : ℝ) in S, |s⁻¹| * (sqrt (2 * π))⁻¹ * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)):=
begin
  have h_exp_eq : ∀ (x:ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)) = exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)),
    {
      intro x,
      simp,
      simp_rw [mul_comm (s ^ 2)⁻¹ 2⁻¹],
      rw sq (s⁻¹ * x),
      rw mul_assoc s⁻¹ x (s⁻¹ * x),
      rw mul_comm x (s⁻¹ * x),
      rw ← mul_assoc s⁻¹ (s⁻¹ * x) x,
      rw ← mul_assoc s⁻¹ s⁻¹ x,
      rw sq,
      rw sq x,
      simp,
      ring,
    },
  simp_rw [h_exp_eq],
end

lemma integ_eq_break_bracket (S : set ℝ) (hS : measurable_set S) (s : ℝ) (hs : s≠0):
∫ (x : ℝ) in S, |s⁻¹| * ((sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)))
= ∫ (x : ℝ) in S, |s⁻¹| * ((sqrt π)⁻¹ * (sqrt 2)⁻¹) * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)):=
begin
  have h : ∀ (x:ℝ), |s⁻¹| * ((sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)))
  = |s⁻¹| * ((sqrt π)⁻¹ * (sqrt 2)⁻¹) * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)),
   {intro x,
   ring_nf,
   },
  simp_rw [h],
end

lemma det_constmulid_eq_const2 : | (s⁻¹ • continuous_linear_map.id ℝ ℝ).det| = |s⁻¹| :=
begin
  have h_detid_eq_one : |(continuous_linear_map.id ℝ ℝ).det| = 1 := detid_eq_one,
  have h_deteq : (s⁻¹ • continuous_linear_map.id ℝ ℝ).det = linear_map.det (s⁻¹ • linear_map.id),
    refl,
  rw h_deteq,
  simp [h_detid_eq_one],
end


lemma mul_const_eq_mul_det2 (f g : ℝ → ℝ) (S : set ℝ):
∫ (x : ℝ) in S, |s⁻¹| • g (f x)
 = ∫ (x : ℝ) in S, | (s⁻¹ • continuous_linear_map.id ℝ ℝ).det| • g (f x):=
begin
simp_rw det_constmulid_eq_const2,

end


lemma change_of_vr_gaussian_with_mean_zero (S : set ℝ) (hS : measurable_set S) (hs : s≠0):
 ∫ (x : ℝ) in {x : ℝ | s • x ∈ S}, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2))
  = ∫ (x : ℝ) in S, (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)):=
begin
  let h : ℝ → ℝ := λ x, s⁻¹ * x,
  let g : ℝ → ℝ := λ x, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)),
  rw S_is_im2 S s hs,


  have h_eq_integ2 : ∫ (x : ℝ) in (λ (x : ℝ), s⁻¹ * x) '' S, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2))
  = ∫ (x : ℝ) in h '' S, (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)),
    {
      simp_rw [h],
    },

  rw h_eq_integ2,
  simp_rw [← g],
  rw integ_taking_s_out S s hs,
  rw integ_put_s_x_together S hS s hs,

  have h_eq_integ : ∫ (x : ℝ) in S, |s⁻¹| • (g (h x))
   = ∫ (x : ℝ) in S, |s⁻¹| * (sqrt (2 * π))⁻¹ * exp (-(2⁻¹ * (s⁻¹ * x) ^ 2)),
    {
      simp [smul_eq_mul],
      simp_rw [h, g],
      rw integ_eq_break_bracket S hS s hs,
    },

  rw ← h_eq_integ,

  let h': ℝ → (ℝ →L[ℝ] ℝ) := λ x, s⁻¹ • continuous_linear_map.id ℝ ℝ,
  rw mul_const_eq_mul_det2 h g,

  have h_eq_integ3 : ∫ (x : ℝ) in S, |(h' x).det| • g (h x) =
  ∫ (x : ℝ) in S, |(s⁻¹ • continuous_linear_map.id ℝ ℝ).det| • g (h x) ,
    {
      simp_rw [h],
    },
  rw ← h_eq_integ3,



  have h_h : set.inj_on h S,
    {refine set.inj_on_of_injective _ S,
      ---refine set.injective_iff_inj_on_univ.mp _,
    unfold function.injective,
    intros a1 a2,
    simp_rw[h],
    simp [hs],
    },

  have h_h' : ∀ (x : ℝ), x ∈ S → has_fderiv_within_at h (h' x) S x,
    {intros x hx,
    refine has_fderiv_within_at.const_mul _ s⁻¹,
    --refine has_fderiv_within_at.sub_const _ m,
    exact has_fderiv_within_at_id x S,
    },

  rw ← integral_image_eq_integral_abs_det_fderiv_smul ℙ hS h_h' h_h g,

end


-- the 6th important theorem
lemma std_gaussian_rv_const_smul (hf : std_gaussian_rv f) (hfmeas : measurable f) (s : ℝ) :
  gaussian_rv (s • f) 0 s :=
begin
  unfold std_gaussian_rv at hf,
  unfold gaussian_rv at *,
  unfold real_gaussian at *,
  simp at *,
  split_ifs,
  {
    rw h,
    rw zero_smul,
    classical,
    change map (λ x, 0 : Ω → ℝ) ℙ = dirac 0,
    ext1 S hS,
    rw [measure.map_apply measurable_const hS, measure.dirac_apply,
    set.indicator, set.preimage_const],
    split_ifs;
    simp,
  },
  {
    let h1 : ℝ → ℝ := λ x, s • x,
    have h_f_plus_const_eq_comb : (s • f) = h1 ∘ f,
    {
      ext x,
      simp,
      simp_rw[h1],
      simp,
    },
    rw h_f_plus_const_eq_comb,
    have h_hmeas : measurable h1,
    {measurability},
    rw ← measure.map_map h_hmeas hfmeas,
    rw hf,
    ext1 S hS,
    have h_preim_of_S_eq_Sminusm : (h1 ⁻¹' S) = {x : ℝ | s • x ∈ S},
    {
      ext x,
      simp,
      simp_rw[h1],
      simp,
    },
    rw measure_theory.with_density_apply,
    {
      --simp_rw[h1],
      let μ : measure ℝ := (volume.with_density (gaussian_density 0 1)),
      have ae_measurable2: ae_measurable h1 (volume.with_density (gaussian_density 0 1)),
        {
          have h₁: ae_measurable h1 (volume.with_density (gaussian_density 0 1)) ↔ ae_measurable h1 μ,
            {
              simp_rw[μ],
            },
          rw h₁,
          measurability,
        },
      rw measure_theory.measure.map_apply_of_ae_measurable ae_measurable2 hS,
      rw measure_theory.with_density_apply,
      {
        unfold gaussian_density,

        rw ← measure_theory.of_real_integral_eq_lintegral_of_real,
        rw ← measure_theory.of_real_integral_eq_lintegral_of_real,
        {
          simp,
          rw h_preim_of_S_eq_Sminusm,
          rw ← change_of_vr_gaussian_with_mean_zero S hS h,
        },
        {
          simp,
          rw integrable, fconstructor,
          {
            measurability,
          },
          {
            refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt (2 * π * s ^ 2))⁻¹ * exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)))).mp
  _,
            apply integrable.has_finite_integral _,
            refine integrable.abs _,
            simp,
            refine integrable.const_mul _ (sqrt (2 * π * s ^ 2))⁻¹,
            refine measure_theory.integrable_on.integrable _,
            have h₁: integrable (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * a ^ 2))) ℙ,
              {
                rw integrable, fconstructor,
                {measurability,},
                {
                  refine (has_finite_integral_norm_iff (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * a ^ 2)))).mp _,
                  apply integrable.has_finite_integral _,
                  refine integrable.abs _,
                  simp,
                  have h_eqfunc : (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹) * a ^ 2)) = (λ (a : ℝ), exp (-((s ^ 2)⁻¹ * 2⁻¹ * a ^ 2))),
                    {
                      ext x,
                      simp,
                    },
                  rw ← h_eqfunc,
                  have hb: (0:ℝ) < ((s ^ 2)⁻¹ * 2⁻¹),
                    {
                      simp,
                      exact (s_sq_pos s h),
                    },
                  exact integrable_exp_neg_mul_sq hb,
                },
              },
            simp[(measure_theory.integrable.integrable_on h₁)],
          },
        },
        {
          refine filter.eventually_of_forall _,
          intro x,
          simp,
          have h_invsqrt_pos : 0 < (sqrt (2 * π * s ^ 2))⁻¹,
            {
              simp,
              exact s_sq_pos_2_pi s h,
            },
          have h_compexp_pos : 0 < exp (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
            {
              exact real.exp_pos (-((s ^ 2)⁻¹ * 2⁻¹ * x ^ 2)),
            },
          rw  le_iff_lt_or_eq,
          left,
          exact mul_pos h_invsqrt_pos h_compexp_pos,

        },
        {
          simp,
          rw integrable, fconstructor,
          {
            measurability,
          },
          {
            refine (has_finite_integral_norm_iff
   (λ (x : ℝ), (sqrt π)⁻¹ * (sqrt 2)⁻¹ * exp (-(2⁻¹ * x ^ 2)))).mp
  _,
            apply integrable.has_finite_integral _,
            refine integrable.abs _,
            simp,
            refine integrable.const_mul _ ((sqrt π)⁻¹ * (sqrt 2)⁻¹),
            refine measure_theory.integrable_on.integrable _,
            have h₁: integrable (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2))) ℙ,
              {
                rw integrable, fconstructor,
                {measurability,},
                {
                  refine (has_finite_integral_norm_iff (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2)))).mp _,
                  apply integrable.has_finite_integral _,
                  refine integrable.abs _,
                  simp,
                  have h_eqfunc : (λ (a : ℝ), exp (-(2)⁻¹ * a^ 2)) = (λ (a : ℝ), exp (-(2⁻¹ * a ^ 2)))  ,
                    {
                      ext x,
                      simp,
                    },
                  rw ← h_eqfunc,
                  have hb: (0:ℝ) < (2)⁻¹,
                    {simp,},
                  exact integrable_exp_neg_mul_sq hb,
                },
              },
            simp[(measure_theory.integrable.integrable_on h₁)],
          },
        },
        {
          refine filter.eventually_of_forall _,
          intro x,
          simp,
          have h₁: (sqrt π)⁻¹ * (sqrt 2)⁻¹ = (sqrt(2 * π))⁻¹,
            {
              rw ← mul_inv,
              simp,
              exact mul_comm ((sqrt 2)⁻¹) ((sqrt π)⁻¹),
            },
          rw h₁,
          have h₂: 0 < (sqrt(2 * π))⁻¹,
            {
              simp,
              exact pi_pos,
            },
          have h_compexp_pos : 0 < exp (-(2⁻¹ * x ^ 2)),
            {
              exact real.exp_pos (-(2⁻¹ * x ^ 2)),
            },
          rw  le_iff_lt_or_eq,
          left,
          exact mul_pos h₂ h_compexp_pos,
        },

      },
      {measurability,},
    },
    {exact hS},
  },

end


-- The following lemms are for the seventh important lemma

-- `x^2+y^2 = 0 ↔ x=0 ∧ y = 0`
lemma sum_sq_eq_zero_iff_both_zero (x y : ℝ): x^2+y^2 = 0 ↔ x=0 ∧ y = 0:=
begin
  split,
  {
    intro,
    split,
    nlinarith,
    nlinarith,
  },
  {
    simp,
    intros h1 h2,
    rw [h1, h2],
    simp,
  },

end

-- `x = 0 ↔ sqrt(x) = 0`
lemma zero_iff_sqrt_zero (x : ℝ) (hx : 0 ≤ x): x = (0:ℝ) ↔ sqrt x = (0:ℝ):=
begin
  split,
  {
    intro h1,
    rw h1,
    simp,
  },
  {
    intro h1,
    have h0 : (0:ℝ) ≤ (0:ℝ),
      {simp,},
    rw sqrt_eq_iff_sq_eq hx h0 at h1,
    rw ← h1,
    simp,
  },
end

-- `x ≠ (0:ℝ) ↔ sqrt x ≠ (0:ℝ)`
lemma nzero_iff_sqrt_nzero (x : ℝ) (hx : 0 ≤ x): x ≠ (0:ℝ) ↔ sqrt x ≠ (0:ℝ):=
begin
  simp [zero_iff_sqrt_zero x hx],
end


--test --
-- Hard!

-- `0 ≤ x^2 +y^2`
lemma sum_square_nneg (x y : ℝ): 0 ≤ x^2 +y^2:=
begin
  have hx : 0 ≤ x^2 := sq_nonneg x,
  have hy : 0 ≤ y^2 := sq_nonneg y,
  exact add_nonneg hx hy,
end

-- `a+b = 1 & a = 1 & a,b ≤ 1` → `b = 1`
lemma sum_one_a_one_then_b_zero_forennreal (a: ℝ≥0∞) (b : ℝ≥0∞) (ha : a ≤ (1:ℝ≥0∞))
(hb : b ≤ (1:ℝ≥0∞)) (h1 : a+b=(1:ℝ≥0∞)) (h2 : a=(1:ℝ≥0∞)) : b=(0:ℝ≥0∞):=
begin
  have h :  (a+b).to_real=(1:ℝ≥0∞).to_real ↔ a+b=(1:ℝ≥0∞),
    {
      split,
      simp[h1],
      intro hh,
      simp [hh],
    },
  have h_one_l_T : (1:ℝ≥0∞) < ⊤,
    {
      simp,
    },

  have h_a_l_two : a<(2:ℝ≥0∞),
    {
      finish,
    },
  have ha_notT : a ≠ ⊤ := ne_top_of_lt h_a_l_two,

  have hb_notT : b ≠ ⊤,
    {
      by_contra h_eq_T,
      rw [h2, h_eq_T] at h1,
      have h_T_plus_eq_T: (1:ℝ≥0∞) + ⊤ = ⊤,
        {
          simp,
        },
      rw h1 at h_T_plus_eq_T,
      finish,
    },

  have hh : (a+b).to_real = a.to_real + b.to_real,
    {
      simp [ennreal.to_real_add ha_notT hb_notT],
    },

  rw [←h, hh] at h1,
  have ha_eq_one: a.to_real = (1:ℝ≥0∞).to_real,
    {
      simp[h2],
    },
  simp [ha_eq_one] at h1,
  rw ennreal.to_real_eq_zero_iff at h1,
  simp [hb_notT] at h1,
  exact h1,
end

-- `μ set.univ = 1`
lemma prob_mea_one (μ : measure Ω) (hμ : is_probability_measure μ):
μ set.univ = 1 :=
begin
  simp,
end

-- if the pushforward measure of a function is a dirac function
-- then almost everywhere constant
lemma pushmea_of_func_is_dirac_then_ae_const2 (m:ℝ) (func : Ω → ℝ)
(hmeas : measurable func) (h_func : map func ℙ = dirac m) : func =ᵐ[ℙ] (λ x, m : Ω → ℝ):=
begin
  unfold eventually_eq,
  refine eventually_zero.mpr _,
  let s : set ℝ := {m},
  have h_s_mea : measurable_set s,
    {
      simp,
    },
  have mea_of_s_one : (map func ℙ) s = 1,
    {
      rw h_func,
      simp,
    },
  have h_eq_set : func⁻¹' s = {x:Ω | func x = m},
    {refl,},
  have h_sum_one : (ℙ {x:Ω | func x = m}) + (ℙ {x:Ω | func x = m}ᶜ) = 1,
    {
      have h_disj : disjoint {x:Ω | func x = m} {x:Ω | func x = m}ᶜ,
        {
          refine set.disjoint_iff.mpr _,
          simp,
        },
      have h_mea : measurable_set {x:Ω | func x = m},
        {
          rw ← h_eq_set,
          exact measurable_set_preimage hmeas  h_s_mea,
        },
      have h_eq_mea_of_union : (ℙ {x:Ω | func x = m}) + (ℙ {x:Ω | func x = m}ᶜ) = ℙ ( {x:Ω | func x = m} ∪ {x:Ω | func x = m}ᶜ),
        {
          rw measure_union' h_disj h_mea,
        },
      rw [h_eq_mea_of_union],
      simp,
    },
  have h_mea_of_preimg_one : ℙ {x:Ω | func x = m} = 1,
    {
      rw ← h_eq_set,
      have h_map_expand : (map func ℙ) s = ℙ (func⁻¹' s),
        {
          simp [h_s_mea, hmeas],
        },
      rw h_map_expand at mea_of_s_one,
    exact mea_of_s_one,
    },

  have h_subset1: {x:Ω|func x = m} ⊆ set.univ,
    {
      exact {x : Ω | func x = m}.subset_univ,
    },
  have h_subset2: {x:Ω|func x = m}ᶜ ⊆ set.univ,
    {
      exact {x : Ω | func x = m}ᶜ.subset_univ,
    },

  have h_prob_mea_one : ℙ set.univ = 1,
    {
      exact prob_mea_one ℙ _inst_7,
    },
  have h_bound1: ℙ {x:Ω|func x = m} ≤ (1:ℝ≥0∞),
    {
      rw ← h_prob_mea_one,
      exact measure_mono h_subset1,
    },
  have h_bound2: ℙ {x:Ω|func x = m}ᶜ ≤ (1:ℝ≥0∞),
    {
      rw ← h_prob_mea_one,
      exact measure_mono h_subset2,
    },

  exact sum_one_a_one_then_b_zero_forennreal (ℙ {x:Ω | func x = m}) (ℙ {x:Ω | func x = m}ᶜ)
  h_bound1 h_bound2 h_sum_one h_mea_of_preimg_one,
end



---if the pushforward of func1 is dirac, then pushforward of sum of func1 and
---func2 equals the pushforward of the constant function plus func2.
lemma pushmea_of_func_plus_const_func (func1 func2 : Ω → ℝ) (m:ℝ)
(hmeas1 : measurable func1) (hmeas2 : measurable func2)
(h_dirac : map func1 ℙ = dirac m) :
map (func1+func2) ℙ = map (func2 + λ x, m) ℙ:=
begin

  have h_func1_eq_const_ae : func1 =ᵐ[ℙ] (λ x, m : Ω → ℝ):=
  pushmea_of_func_is_dirac_then_ae_const2 m func1 hmeas1 h_dirac,

  have h_ev_eq_self : func2 =ᵐ[ℙ] func2,
    {
      unfold eventually_eq,
      simp,
    },
  have h_ae_eq : func1 + func2 =ᵐ[ℙ]  (λ x, m : Ω → ℝ) + func2,
    {
      exact eventually_eq.add h_func1_eq_const_ae h_ev_eq_self,
    },

  simp [measure_theory.measure.map_congr h_ae_eq],

  have h_comm : func2 + (λ (x : Ω), m) = (λ (x : Ω), m) + func2,
    {
      ext x,
      simp,
      linarith,
    },

  rw h_comm,
end





-- lemma gaussian_rv_add (hf : gaussian_rv f m₁ s₁) (hg : gaussian_rv g m₂ s₂)
--   (hfmeas : measurable f) (hgmeas : measurable g) (hfg : indep_fun f g) :
--   gaussian_rv (f + g) (m₁ + m₂) (sqrt (s₁^2 + s₂^2)) :=
-- begin
--   unfold gaussian_rv at *,
--   unfold real_gaussian at *,
--   ---split_ifs,
--   by_cases h1: s₁=0,
--   {by_cases h2: s₂=0,
--   {
--     rw [h1, h2],
--     simp,
--     simp [h1] at hf,
--     simp [h2] at hg,
--     sorry},
--   {

--       simp [(sq_pos_iff s₂).mpr h2, sq_nonneg s₁, lt_add_of_le_of_pos, ne_of_gt],
--       simp [h1, h2] at hf hg ⊢,
--       rw pushmea_of_func_plus_const_func f g m₁ hfmeas hgmeas hf,
--       unfold gaussian_density,
--       /-let h : ℝ → ℝ := λ x, x + m₁,
--       have h_f_plus_const_eq_comb : (f + g) = h ∘ g,
--       {
--         ext x,
--         simp [h],
--       },
--       -- rw ← measure.map_map h_hmeas hfmeas,-/


--       ---WE ARE AIMING TO SOLVE THIS BRACKET
--       ---WE ARE AIMING TO SOLVE THIS BRACKET
--       ---WE ARE AIMING TO SOLVE THIS BRACKET
--       ---WE ARE AIMING TO SOLVE THIS BRACKET
--       ---WE ARE AIMING TO SOLVE THIS BRACKET
--       sorry,

--       },
--   },
--   {by_cases h2: s₂=0,
--   {sorry},
--   {sorry},

--   },



-- end

-- lemma mgf_gaussian_rv  (hf : gaussian_rv f m s) (hfmeas : measurable f) (t : ℝ) :
--   mgf f volume t = exp (m * t + s^2 * t^2 / 2) :=
-- begin
--   unfold mgf,
--   unfold gaussian_rv real_gaussian at hf,
--   by_cases hs : s = 0;
--   {simp [hs] at *,
--   sorry,
--   },
-- end

end gaussian_rv

#where
section tvs

/- ### Gaussian measure on TVS -/

variables {E' : Type*} [measurable_space E']
  [topological_space E'] [add_comm_monoid E'] [module ℝ E']

/-- A measure `ν` on a topological vector space `E` is said to be a Gaussian measure if for all
continuous linear functionals `l` of `E`, the push-forward measure of `l` along `ν` is a Gaussian
measure on ℝ with mean 0. -/
def gaussian (ν : measure E') : Prop :=
∀ l : E' →L[ℝ] ℝ, ∃ s, (ν.map l).real_gaussian 0 s

end tvs

end measure_theory

#lint
