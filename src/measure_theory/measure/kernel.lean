/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.constructions.prod

/-!
# Markov Kernel

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

-/

open measure_theory

open_locale measure_theory ennreal

namespace measure_theory

variables {α β γ δ : Type*}
  {mα : measurable_space α} {μα : measure α}
  {mβ : measurable_space β} {μβ : measure β}
  {mγ : measurable_space γ} {μγ : measure γ}
  {mδ : measurable_space δ} {μδ : measure δ}

/-
localized "notation P `[` X `;` s `]` := ∫ x in s, X x ∂P" in measure_theory

noncomputable
def cond_meas {m₀ : measurable_space α} (μ : measure α) (s : set α) (m : measurable_space α) :
  α → ℝ :=
  μ[s.indicator (λ _, (1 : ℝ)) | m]

lemma cond_meas_def : cond_meas μ s m = μ[s.indicator (λ _, (1 : ℝ)) | m] := rfl

lemma set_integral_cond_meas {hm : m ≤ m₀} [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t)  :
  μ[cond_meas μ s m; t] = (μ (s ∩ t)).to_real :=
by rw [cond_meas_def, set_integral_condexp hm
    ((integrable_indicator_iff hs).mpr (integrable_on_const.mpr (or.inr hμs.lt_top))) ht,
  integral_indicator_const _ hs, measure.restrict_apply hs, smul_eq_mul, mul_one]
-/

instance measure.has_measurable_add₂ {m : measurable_space β} : has_measurable_add₂ (measure β) :=
begin
  refine ⟨measure.measurable_of_measurable_coe _ (λ s hs, _)⟩,
  simp_rw [measure.coe_add, pi.add_apply],
  refine measurable.add _ _,
  { exact (measure.measurable_coe hs).comp measurable_fst, },
  { exact (measure.measurable_coe hs).comp measurable_snd, },
end

def transition_kernel (mα : measurable_space α) (mβ : measurable_space β) :
  add_submonoid (α → measure β) :=
{ carrier := measurable, -- ∀ s : set β, measurable_set[mβ] s → measurable[mα] (λ a, κ a s)
  zero_mem' := measurable_zero,
  add_mem' := λ f g hf hg, measurable.add hf hg, }

instance : has_coe_to_fun (transition_kernel mα mβ) (λ _, α → measure β) := ⟨λ κ, κ.val⟩

class is_markov_kernel (κ : transition_kernel mα mβ) : Prop :=
(is_probability_measure : ∀ a, is_probability_measure (κ a))

class is_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a set.univ ≤ C)

noncomputable
def is_finite_kernel.bound (κ : transition_kernel mα mβ) [h : is_finite_kernel κ] : ℝ≥0∞ :=
h.exists_univ_le.some

lemma is_finite_kernel.bound_lt_top (κ : transition_kernel mα mβ) [h : is_finite_kernel κ] :
  is_finite_kernel.bound κ < ∞ :=
h.exists_univ_le.some_spec.1

lemma measure_le_bound (κ : transition_kernel mα mβ) [h : is_finite_kernel κ] (a : α) (s : set β) :
  κ a s ≤ is_finite_kernel.bound κ :=
(measure_mono (set.subset_univ s)).trans (h.exists_univ_le.some_spec.2 a)

def singular (κ : ℕ → transition_kernel mα mβ) : Prop :=
∃ s : ℕ → set (α × β), ∀ i a, κ i a {b | (a,b) ∈ s i}ᶜ = 0

class is_sigma_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(tsum_singular : ∃ κs : ℕ → transition_kernel mα mβ,
  (∀ n, is_finite_kernel (κs n)) ∧ (∀ a s, κ a s = ∑' n, κs n a s) ∧ singular κs)

class is_s_finite_kernel (κ : transition_kernel mα mβ) : Prop :=
(tsum_finite : ∃ κs : ℕ → transition_kernel mα mβ,
  (∀ n, is_finite_kernel (κs n)) ∧ ∀ a s, κ a s = ∑' n, κs n a s)

variables {κ : transition_kernel mα mβ}

instance todo [h : is_markov_kernel κ] (a : α) : is_probability_measure (κ a) :=
is_markov_kernel.is_probability_measure a

instance todo' [h : is_finite_kernel κ] (a : α) : is_finite_measure (κ a) :=
⟨(h.exists_univ_le.some_spec.2 a).trans_lt h.exists_univ_le.some_spec.1⟩

instance is_markov_kernel.is_finite_kernel [h : is_markov_kernel κ] : is_finite_kernel κ :=
⟨⟨1, ennreal.one_lt_top, λ a, prob_le_one⟩⟩

instance is_finite_kernel.is_sigma_finite_kernel [h : is_finite_kernel κ] :
  is_sigma_finite_kernel κ :=
⟨⟨λ n, if n = 0 then κ else 0, sorry, sorry, sorry⟩⟩

instance is_sigma_finite_kernel.is_s_finite_kernel [h : is_sigma_finite_kernel κ] :
  is_s_finite_kernel κ :=
⟨⟨h.tsum_singular.some, h.tsum_singular.some_spec.1, h.tsum_singular.some_spec.2.1⟩⟩

namespace transition_kernel

@[ext] lemma ext {κ : transition_kernel mα mβ} {η : transition_kernel mα mβ} (h : ∀ a, κ a = η a) :
  κ = η :=
by { ext1, ext1 a, exact h a, }

noncomputable
def seq (κ : transition_kernel mα mβ) [h : is_s_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] :
  ℕ → transition_kernel mα mβ :=
if hσ : is_sigma_finite_kernel κ then hσ.tsum_singular.some else h.tsum_finite.some

lemma tsum_seq (κ : transition_kernel mα mβ) [h : is_s_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] (a : α) (s : set β) :
  ∑' n, transition_kernel.seq κ n a s = κ a s :=
begin
  simp_rw seq,
  split_ifs with hσ hσ,
  { exact (hσ.tsum_singular.some_spec.2.1 a s).symm, },
  { exact (h.tsum_finite.some_spec.2 a s).symm, },
end

lemma singular_seq (κ : transition_kernel mα mβ) [h : is_sigma_finite_kernel κ]
  [decidable (is_sigma_finite_kernel κ)] :
  singular (transition_kernel.seq κ) :=
by { rw [seq, dif_pos h], exact h.tsum_singular.some_spec.2.2, }

end transition_kernel


/- Regular conditional distribution -/
--def is_reg_cond_distribution (κ : transition_kernel mα mβ) (Y : α → β) : Prop :=
--∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = ennreal.of_real (cond_meas μ (Y ⁻¹' s) mα ω)

-- ∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = μ[(Y ⁻¹' s).indicator (λ _, 1) | mα] ω
-- ∀ᵐ ω ∂μ, ∀ s : set β, κ ω s = μ[Y ∈ s | mα] ω

namespace transition_kernel

protected lemma measurable (κ : transition_kernel mα mβ) : measurable κ := κ.prop

protected lemma measurable_coe (κ : transition_kernel mα mβ)
  {s : set β} (hs : measurable_set[mβ] s) :
  measurable[mα] (λ a, κ a s) :=
(measure.measurable_coe hs).comp (transition_kernel.measurable κ)

/-- Constant kernel, which always returns the same measure. -/
def const (mα : measurable_space α) (mβ : measurable_space β) (μβ : measure β) :
  transition_kernel mα mβ :=
{ val := λ _, μβ,
  property := measure.measurable_of_measurable_coe _ (λ s hs, measurable_const), }

/-- Kernel which to `a` associates the dirac measure at `f a`. -/
noncomputable
def deterministic {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) :
  transition_kernel mα mβ :=
{ val := λ a, measure.dirac (f a),
  property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      simp_rw measure.dirac_apply' _ hs,
      refine measurable.indicator _ (hf hs),
      simp only [pi.one_apply, measurable_const],
    end, }

lemma coe_fn_deterministic {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) (a : α) :
  deterministic hf a = measure.dirac (f a) := rfl

lemma deterministic_apply {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) (a : α) {s : set β} (hs : measurable_set s) :
  deterministic hf a s = s.indicator (λ _, 1) (f a) :=
begin
  rw [deterministic],
  change measure.dirac (f a) s = s.indicator 1 (f a),
  simp_rw measure.dirac_apply' _ hs,
end

lemma is_finite_measure_deterministic {mα : measurable_space α} {mβ : measurable_space β}
  {f : α → β} (hf : measurable f) (a : α) :
  is_finite_measure (deterministic hf a) :=
by { simp_rw [deterministic], apply_instance, }

instance is_finite_kernel.deterministic {mα : measurable_space α} {mβ : measurable_space β}
  {f : α → β} (hf : measurable f) :
  is_finite_kernel (deterministic hf) :=
begin
  refine ⟨⟨1, ennreal.one_lt_top, λ a, le_of_eq _⟩⟩,
  rw [deterministic_apply hf a measurable_set.univ, set.indicator_univ],
end

lemma is_finite_kernel_const [hμβ : is_finite_measure μβ] : is_finite_kernel (const mα mβ μβ) :=
⟨⟨μβ set.univ, measure_lt_top _ _, λ a, le_rfl⟩⟩

lemma is_markov_kernel_const [hμβ : is_probability_measure μβ] :
  is_markov_kernel (const mα mβ μβ) :=
⟨λ a, hμβ⟩

def of_fun_of_countable (mα : measurable_space α) (mβ : measurable_space β)
  [countable α] [measurable_singleton_class α] (f : α → measure β) :
  transition_kernel mα mβ :=
{ val := f,
  property := measurable_of_countable f }

lemma aux (κ : transition_kernel mα mβ) {s : set β} {t : set (α × β)} (hs : measurable_set s)
  (ht : measurable_set t) (hκs : ∀ a, κ a s ≠ ∞) :
  measurable (λ a, κ a (s ∩ {b | (a, b) ∈ t})) :=
begin
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { simp only [set.mem_empty_iff_false, set.set_of_false, set.inter_empty, measure_empty,
      measurable_const], },
  { intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    simp only [set.prod_mk_mem_set_prod_eq],
    classical,
    have h_eq_ite : ∀ a, s ∩ {b : β | a ∈ t₁ ∧ b ∈ t₂} = ite (a ∈ t₁) (s ∩ t₂) ∅,
    { intros a,
      ext1 b,
      split_ifs; simp [h], },
    simp_rw h_eq_ite,
    have : (λ a, (κ a) (ite (a ∈ t₁) (s ∩ t₂) ∅)) = (λ a, ite (a ∈ t₁) (κ a (s ∩ t₂)) 0),
    { ext1 a,
      split_ifs,
      { refl, },
      { exact measure_empty, }, },
    rw this,
    exact measurable.ite ht₁ (transition_kernel.measurable_coe κ (hs.inter ht₂)) measurable_const },
  { intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, s ∩ {b : β | (a, b) ∈ t'ᶜ} = s \ {b : β | (a, b) ∈ t'},
    { intro a,
      ext1 b,
      simp only [set.mem_compl_iff, set.mem_inter_iff, set.mem_set_of_eq, set.mem_diff], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (s \ {b : β | (a, b) ∈ t'}))
      = (λ a, (κ a s - κ a (s ∩ {b : β | (a, b) ∈ t'}))),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, measure_diff],
      { rw set.inter_comm, },
      { exact set.inter_subset_right _ _, },
      { exact ((@measurable_prod_mk_left α β mα mβ a) t' ht').inter hs, },
      { exact (lt_of_le_of_lt (measure_mono (set.inter_subset_right _ _)) (hκs a).lt_top).ne, }, },
    rw this,
    exact measurable.sub (transition_kernel.measurable_coe κ hs) h_meas, },
  { intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a (s ∩ {b : β | (a, b) ∈ ⋃ i, f i}))
      = (λ a, κ a (⋃ i, s ∩ {b : β | (a, b) ∈ f i})),
    { ext1 a,
      congr' with b,
      simp only [set.mem_Union, set.mem_inter_iff, set.mem_set_of_eq, exists_and_distrib_left], },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, s ∩ {b : β | (a, b) ∈ f i}))
      = (λ a, ∑' i, κ a (s ∩ {b : β | (a, b) ∈ f i})),
    { ext1 a,
      rw measure_Union,
      { intros i j hij b hb,
        simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hb,
        specialize h_disj i j hij ⟨hb.1.2, hb.2.2⟩,
        simpa using h_disj, },
      { exact λ i, hs.inter ((@measurable_prod_mk_left α β mα mβ a) _ (hf_meas i)), }, },
    rw h_tsum,
    exact measurable.ennreal_tsum hf, },
end

lemma aux' (κ : transition_kernel mα mβ) {t : set (α × β)}
  (ht : measurable_set t) (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
by { convert aux κ measurable_set.univ ht (λ a, measure_ne_top _ _), ext1 a, rw set.univ_inter, }

lemma lintegral_indicator' {mβ : measurable_space β} {f : α → β} {s : set β}
  (hf : measurable f) (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) (f a) ∂μα = c * μα (f ⁻¹' s) :=
begin
  rw ← lintegral_add_compl _ (hf hs),
  rw ← add_zero (c * μα (f ⁻¹' s)),
  classical,
  simp_rw [set.indicator_apply],
  congr,
  { have h_eq_1 : ∀ x ∈ f ⁻¹' s, ite (f x ∈ s) c 0 = c := λ _ hx, if_pos hx,
    rw set_lintegral_congr_fun (hf hs) (filter.eventually_of_forall h_eq_1),
    simp only,
    rw [lintegral_const, measure.restrict_apply measurable_set.univ, set.univ_inter], },
  { have h_eq_zero : ∀ x ∈ (f ⁻¹' s)ᶜ, ite (f x ∈ s) c 0 = 0,
      from λ _ hx, if_neg hx,
    rw set_lintegral_congr_fun (hf hs).compl (filter.eventually_of_forall h_eq_zero),
    simp only [lintegral_const, zero_mul], },
end

lemma measurable_set_lintegral (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b in s, (⨆ n, (simple_func.eapprox (function.uncurry f) n) (a, b)) ∂κ a
    = ⨆ n, ∫⁻ b in s, (simple_func.eapprox (function.uncurry f) n) (a, b) ∂κ a,
  { intro a,
    rw lintegral_supr,
    { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable.comp
        measurable_prod_mk_left, },
    { intros i j hij b,
      have h_mono := simple_func.monotone_eapprox (function.uncurry f) hij,
      rw ← simple_func.coe_le at h_mono,
      exact h_mono _, }, },
  simp_rw this,
  refine measurable_supr (λ n, _),
  refine simple_func.induction _ _ (simple_func.eapprox (function.uncurry f) n),
  { intros c t ht,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    have : (λ a, ∫⁻ b in s, t.indicator (function.const (α × β) c) (a, b) ∂κ a)
      = (λ a, c * κ a (s ∩ {b | (a, b) ∈ t})),
    { ext1 a,
      rw lintegral_indicator' measurable_prod_mk_left ht,
      rw measure.restrict_apply,
      { rw set.inter_comm,
        refl, },
      { exact measurable_prod_mk_left ht, }, },
    rw this,
    refine measurable.const_mul _ c,
    exact aux _ hs ht (λ a, measure_ne_top (κ a) s), },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b in s, g₁ (a, b) + g₂ (a, b) ∂κ a)
      = (λ a, ∫⁻ b in s, g₁ (a, b) ∂κ a) + (λ a, ∫⁻ b in s, g₂ (a, b) ∂κ a),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left],
      exact g₁.measurable.comp measurable_prod_mk_left, },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable_lintegral (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂κ a) :=
begin
  convert measurable_set_lintegral κ hκ f hf measurable_set.univ,
  simp only [measure.restrict_univ],
end

noncomputable
def of_density (κ : transition_kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  transition_kernel mα mβ :=
{ val := λ a, (κ a).with_density (f a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, (κ a).with_density (f a) s) = (λ a, ∫⁻ b in s, f a b ∂κ a),
    { ext1 a, exact with_density_apply (f a) hs, },
    rw this,
    exact measurable_set_lintegral κ hκ f hf hs,
  end, }

section composition

/-!
### Composition of kernels
 -/

noncomputable
def comp_fun (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ) (a : α)
  (s : set (β × γ)) :
  ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a

lemma comp_fun_empty (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ) (a : α) :
  comp_fun κ η a ∅ = 0 :=
by simp only [comp_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty, lintegral_const,
  zero_mul]

lemma comp_fun_Union (κ : transition_kernel mα mβ) (η : transition_kernel (mα.prod mβ) mγ)
  (hη : ∀ ab, is_finite_measure (η ab)) (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  comp_fun κ η a (⋃ i, f i) = ∑' i, comp_fun κ η a (f i) :=
begin
  have h_Union : (λ b, η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i})
    = λ b, η (a,b) (⋃ i, {c : γ | (b, c) ∈ f i}),
  { ext b,
    congr' with c,
    simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
    refl, },
  rw [comp_fun, h_Union],
  have h_tsum : (λ b, η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i}))
    = λ b, ∑' i, η (a, b) {c : γ | (b, c) ∈ f i},
  { ext1 b,
    rw measure_Union,
    { intros i j hij c hc,
      simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hc,
      specialize hf_disj i j hij hc,
      simpa using hf_disj, },
    { exact λ i, (@measurable_prod_mk_left β γ mβ mγ b) _ (hf_meas i), }, },
  rw [h_tsum, lintegral_tsum],
  { refl, },
  intros i,
  have hm : measurable_set {p : (α × β) × γ | (p.1.2, p.2) ∈ f i},
    from (measurable_fst.snd.prod_mk measurable_snd) (hf_meas i),
  exact (aux' η hm hη).comp measurable_prod_mk_left,
end

/-- Composition of kernels.

About assumptions: the hypothesis `[is_finite_kernel κ]` could be replaced by
`∀ a, is_finite_measure (κ a)` to define the composition (same for η). This would be a weaker
hypothesis since it removes the uniform bound assumption of `is_finite_kernel`. However, that second
property is not stable by composition, in contrast to `is_finite_kernel`. Hence we choose to use the
typeclass with an uniform bound on `κ a univ`. -/
noncomputable
def comp (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel (mα.prod mβ) mγ) [is_finite_kernel η] :
  transition_kernel mα (mβ.prod mγ) :=
have hη : ∀ ab, is_finite_measure (η ab) := infer_instance,
{ val := λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η hη a),
  property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      have : (λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
          (comp_fun_Union κ η hη a) s) = λ a, comp_fun κ η a s,
      { ext1 a, rwa measure.of_measurable_apply, },
      rw this,
      simp only [comp_fun],
      have h_meas : measurable (function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})),
      { have : function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})
          = λ p, η p {c : γ | (p.2, c) ∈ s},
        { ext1 p,
          have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
          rw [hp_eq_mk, function.uncurry_apply_pair], },
        rw this,
        exact aux' η ((measurable_fst.snd.prod_mk measurable_snd) hs) hη, },
      exact measurable_lintegral κ infer_instance (λ a b, η (a, b) {c : γ | (b, c) ∈ s}) h_meas,
    end, }

lemma comp_apply (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel (mα.prod mβ) mγ) [is_finite_kernel η] (a : α)
  {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a :=
begin
  rw [comp],
  change measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η infer_instance a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a,
  rw measure.of_measurable_apply _ hs,
  refl,
end

lemma comp_apply_univ_le (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel (mα.prod mβ) mγ) [is_finite_kernel η] (a : α) :
  comp κ η a set.univ ≤ (κ a set.univ) * (is_finite_kernel.bound η) :=
begin
  rw comp_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true],
  let Cη := is_finite_kernel.bound η,
  calc ∫⁻ b, η (a, b) set.univ ∂κ a
      ≤ ∫⁻ b, Cη ∂κ a : lintegral_mono (λ b, measure_le_bound η (a, b) set.univ)
  ... = Cη * κ a set.univ : lintegral_const Cη
  ... = κ a set.univ * Cη : mul_comm _ _,
end

instance is_finite_kernel.comp (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel (mα.prod mβ) mγ) [is_finite_kernel η] :
  is_finite_kernel (comp κ η) :=
begin
  let Cκ := is_finite_kernel.bound κ,
  let Cη := is_finite_kernel.bound η,
  refine ⟨⟨Cκ * Cη, ennreal.mul_lt_top (is_finite_kernel.bound_lt_top κ).ne
    (is_finite_kernel.bound_lt_top η).ne, λ a, _⟩⟩,
  calc comp κ η a set.univ
      ≤ (κ a set.univ) * Cη : comp_apply_univ_le κ η a
  ... ≤ Cκ * Cη : ennreal.mul_le_mul (measure_le_bound κ a set.univ) le_rfl,
end

end composition

section map_comap
/-! ### map, comap and another composition -/

noncomputable
def map (κ : transition_kernel mα mβ) (f : β → γ) (hf : measurable f) :
  transition_kernel mα mγ :=
{ val := λ a, (κ a).map f,
  property := (measure.measurable_map _ hf).comp (transition_kernel.measurable κ) }

lemma map_apply {mγ : measurable_space γ} (κ : transition_kernel mα mβ) {f : β → γ}
  (hf : measurable f) (a : α) {s : set γ} (hs : measurable_set s) :
  map κ f hf a s = κ a (f ⁻¹' s) :=
begin
  rw [map],
  change (κ a).map f s = κ a (f ⁻¹' s),
  exact measure.map_apply hf hs,
end

def comap (κ : transition_kernel mα mβ) (f : γ → α) (hf : measurable f) :
  transition_kernel mγ mβ :=
{ val := λ a, κ (f a),
  property := (transition_kernel.measurable κ).comp hf }

lemma comap_apply {mγ : measurable_space γ} (κ : transition_kernel mα mβ) {f : γ → α}
  (hf : measurable f) (c : γ) {s : set β} (hs : measurable_set s) :
  comap κ f hf c s = κ (f c) s :=
rfl

def prod_mk_left (κ : transition_kernel mα mβ) (mγ : measurable_space γ) :
  transition_kernel (mγ.prod mα) mβ :=
comap κ (λ a, a.2) measurable_snd

lemma prod_mk_left_apply (κ : transition_kernel mα mβ) (mγ : measurable_space γ) (ca : γ × α)
  {s : set β} (hs : measurable_set s) :
  prod_mk_left κ mγ ca s = (κ ca.snd) s :=
by rw [prod_mk_left, comap_apply _ _ _ hs]

lemma is_finite_measure_prod_mk_left (κ : transition_kernel mα mβ)
  (hκ : ∀ a, is_finite_measure (κ a)) (ca : γ × α) :
  is_finite_measure (prod_mk_left κ mγ ca) :=
begin
  constructor,
  rw [prod_mk_left_apply _ _ _ measurable_set.univ],
  exact measure_lt_top (κ ca.snd) set.univ,
end

instance is_finite_kernel.prod_mk_left (κ : transition_kernel mα mβ) [is_finite_kernel κ] :
  is_finite_kernel (prod_mk_left κ mγ) :=
begin
  let C := is_finite_kernel.bound κ,
  refine ⟨⟨C, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw [prod_mk_left_apply _ _ _ measurable_set.univ],
  exact measure_le_bound κ _ _,
end

noncomputable
def snd_right (κ : transition_kernel mα (mβ.prod mγ)) : transition_kernel mα mγ :=
map κ (λ p, p.2) measurable_snd

lemma snd_right_apply (κ : transition_kernel mα (mβ.prod mγ)) (a : α) {s : set γ}
  (hs : measurable_set s) :
  snd_right κ a s = κ a {p | p.2 ∈ s} :=
by { rw [snd_right, map_apply _ _ _ hs], refl, }

lemma snd_right_univ (κ : transition_kernel mα (mβ.prod mγ)) (a : α) :
  snd_right κ a set.univ = κ a set.univ :=
snd_right_apply _ _ measurable_set.univ

lemma is_finite_measure_snd_right (κ : transition_kernel mα (mβ.prod mγ))
  (hκ : ∀ a, is_finite_measure (κ a)) (a : α) :
  is_finite_measure (snd_right κ a) :=
begin
  constructor,
  rw [snd_right_apply _ _ measurable_set.univ],
  exact measure_lt_top (κ a) set.univ,
end

instance is_finite_kernel.snd_right (κ : transition_kernel mα (mβ.prod mγ)) [is_finite_kernel κ] :
  is_finite_kernel (snd_right κ) :=
begin
  let C := is_finite_kernel.bound κ,
  refine ⟨⟨C, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw [snd_right_univ _ _],
  exact measure_le_bound κ _ _,
end

noncomputable
def comp2 (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel mβ mγ) [is_finite_kernel η] :
  transition_kernel mα mγ :=
snd_right (comp κ (prod_mk_left η mα))

lemma comp2_apply (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel mβ mγ) [is_finite_kernel η] (a : α) {s : set γ}
  (hs : measurable_set s) :
  comp2 κ η a s = ∫⁻ b, η b s ∂κ a :=
begin
  rw [comp2, snd_right_apply _ _ hs, comp_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq],
  simp_rw prod_mk_left_apply _ _ _ hs,
end

instance is_finite_kernel.comp2 (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel mβ mγ) [is_finite_kernel η] :
  is_finite_kernel (comp2 κ η) :=
by { rw comp2, apply_instance, }

lemma comp2_assoc (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  (η : transition_kernel mβ mγ) [is_finite_kernel η]
  (ξ : transition_kernel mγ mδ) [is_finite_kernel ξ] :
  comp2 (comp2 κ η) ξ = comp2 κ (comp2 η ξ) :=
begin
  ext1 a,
  ext1 s hs,
  simp_rw [comp2_apply _ _ _ hs],
  sorry,
end

lemma comp2_deterministic_right_eq_map {mγ : measurable_space γ}
  (κ : transition_kernel mα mβ) [is_finite_kernel κ]
  {f : β → γ} (hf : measurable f) :
  comp2 κ (deterministic hf) = map κ f hf :=
begin
  ext a s hs,
  simp_rw [map_apply _ _ _ hs, comp2_apply _ _ _ hs, deterministic_apply hf _ hs,
    lintegral_indicator' hf hs, one_mul],
end

lemma comp2_deterministic_left_eq_comap {mγ : measurable_space γ} {f : γ → α} (hf : measurable f)
  (κ : transition_kernel mα mβ) [is_finite_kernel κ] :
  comp2 (deterministic hf) κ = comap κ f hf :=
begin
  ext a s hs,
  simp_rw [comap_apply _ _ _ hs, comp2_apply _ _ _ hs, coe_fn_deterministic hf a,
    lintegral_dirac' _ (transition_kernel.measurable_coe κ hs)],
end

end map_comap

end transition_kernel

section real

def reg_cond_distribution (mα : measurable_space α) (Y : α → ℝ) :
  transition_kernel mα (borel ℝ) :=
sorry

end real

end measure_theory
