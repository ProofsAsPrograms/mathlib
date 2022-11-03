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

open_locale measure_theory ennreal big_operators

namespace measure_theory

variables {α β γ δ ι : Type*}
  {mα : measurable_space α} {μα : measure α}
  {mβ : measurable_space β} {μβ : measure β}
  {mγ : measurable_space γ} {μγ : measure γ}
  {mδ : measurable_space δ} {μδ : measure δ}

instance measure.has_measurable_add₂ {m : measurable_space β} : has_measurable_add₂ (measure β) :=
begin
  refine ⟨measure.measurable_of_measurable_coe _ (λ s hs, _)⟩,
  simp_rw [measure.coe_add, pi.add_apply],
  refine measurable.add _ _,
  { exact (measure.measurable_coe hs).comp measurable_fst, },
  { exact (measure.measurable_coe hs).comp measurable_snd, },
end

def kernel (mα : measurable_space α) (mβ : measurable_space β) :
  add_submonoid (α → measure β) :=
{ carrier := measurable, -- ∀ s : set β, measurable_set[mβ] s → measurable[mα] (λ a, κ a s)
  zero_mem' := measurable_zero,
  add_mem' := λ f g hf hg, measurable.add hf hg, }

instance : has_coe_to_fun (kernel mα mβ) (λ _, α → measure β) := ⟨λ κ, κ.val⟩

@[simp] lemma kernel.zero_apply (a : α) : (0 : kernel mα mβ) a = 0 := rfl

class is_markov_kernel (κ : kernel mα mβ) : Prop :=
(is_probability_measure : ∀ a, is_probability_measure (κ a))

class is_finite_kernel (κ : kernel mα mβ) : Prop :=
(exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a set.univ ≤ C)

noncomputable
def is_finite_kernel.bound (κ : kernel mα mβ) [h : is_finite_kernel κ] : ℝ≥0∞ :=
h.exists_univ_le.some

lemma is_finite_kernel.bound_lt_top (κ : kernel mα mβ) [h : is_finite_kernel κ] :
  is_finite_kernel.bound κ < ∞ :=
h.exists_univ_le.some_spec.1

lemma is_finite_kernel.bound_ne_top (κ : kernel mα mβ) [h : is_finite_kernel κ] :
  is_finite_kernel.bound κ ≠ ∞ :=
(is_finite_kernel.bound_lt_top κ).ne

lemma measure_le_bound (κ : kernel mα mβ) [h : is_finite_kernel κ] (a : α) (s : set β) :
  κ a s ≤ is_finite_kernel.bound κ :=
(measure_mono (set.subset_univ s)).trans (h.exists_univ_le.some_spec.2 a)

lemma is_finite_kernel_zero (mα : measurable_space α) (mβ : measurable_space β) :
  is_finite_kernel (0 : kernel mα mβ) :=
⟨⟨0, ennreal.coe_lt_top,
  λ a, by simp only [kernel.zero_apply, measure.coe_zero, pi.zero_apply, le_zero_iff]⟩⟩

variables {κ : kernel mα mβ}

instance is_markov_kernel.is_probability_measure' [h : is_markov_kernel κ] (a : α) :
  is_probability_measure (κ a) :=
is_markov_kernel.is_probability_measure a

instance is_finite_kernel.is_finite_measure [h : is_finite_kernel κ] (a : α) :
  is_finite_measure (κ a) :=
⟨(measure_le_bound κ a set.univ).trans_lt (is_finite_kernel.bound_lt_top κ)⟩

@[priority 100]
instance is_markov_kernel.is_finite_kernel [h : is_markov_kernel κ] : is_finite_kernel κ :=
⟨⟨1, ennreal.one_lt_top, λ a, prob_le_one⟩⟩

namespace kernel

protected lemma measurable (κ : kernel mα mβ) : measurable κ := κ.prop

protected lemma measurable_coe (κ : kernel mα mβ)
  {s : set β} (hs : measurable_set[mβ] s) :
  measurable[mα] (λ a, κ a s) :=
(measure.measurable_coe hs).comp (kernel.measurable κ)

/-- Constant kernel, which always returns the same measure. -/
def const (mα : measurable_space α) (mβ : measurable_space β) (μβ : measure β) :
  kernel mα mβ :=
{ val := λ _, μβ,
  property := measure.measurable_of_measurable_coe _ (λ s hs, measurable_const), }

/-- Kernel which to `a` associates the dirac measure at `f a`. -/
noncomputable
def deterministic {mα : measurable_space α} {mβ : measurable_space β} {f : α → β}
  (hf : measurable f) :
  kernel mα mβ :=
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
  kernel mα mβ :=
{ val := f,
  property := measurable_of_countable f }

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

@[ext] lemma ext {κ : kernel mα mβ} {η : kernel mα mβ} (h : ∀ a, κ a = η a) :
  κ = η :=
by { ext1, ext1 a, exact h a, }

lemma ext_fun {κ : kernel mα mβ} {η : kernel mα mβ}
  (h : ∀ a f, measurable f → ∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)) :
  κ = η :=
begin
  ext a s hs,
  specialize h a (s.indicator (λ _, 1)) (measurable.indicator measurable_const hs),
  simp_rw [lintegral_indicator' measurable_id' hs, set.preimage_id', one_mul] at h,
  rw h,
end

section restrict

protected noncomputable
def restrict (κ : kernel mα mβ) {s : set β} (hs : measurable_set s) : kernel mα mβ :=
{ val := λ a, (κ a).restrict s,
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ t ht, _),
    simp_rw measure.restrict_apply ht,
    exact kernel.measurable_coe κ (ht.inter hs),
  end, }

lemma restrict_apply (κ : kernel mα mβ) {s : set β} (hs : measurable_set s) (a : α) :
  kernel.restrict κ hs a = (κ a).restrict s := rfl

lemma restrict_apply' (κ : kernel mα mβ) {s : set β} (hs : measurable_set s) (a : α)
  {t : set β} (ht : measurable_set t) :
  kernel.restrict κ hs a t = (κ a) (t ∩ s) :=
by rw [restrict_apply κ hs a, measure.restrict_apply ht]

lemma lintegral_restrict (κ : kernel mα mβ) {s : set β} (hs : measurable_set s)
  (a : α) (f : β → ℝ≥0∞) :
  ∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a) :=
by rw restrict_apply

instance is_finite_kernel.restrict (κ : kernel mα mβ) [is_finite_kernel κ]
  {s : set β} (hs : measurable_set s) :
  is_finite_kernel (kernel.restrict κ hs) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw restrict_apply' κ hs a measurable_set.univ,
  exact measure_le_bound κ a _,
end

end restrict

lemma measurable_prod_mk_mem (κ : kernel mα mβ) {t : set (α × β)} (ht : measurable_set t)
  (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { simp only [set.mem_empty_iff_false, set.set_of_false, measure_empty, measurable_const], },
  { intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    simp only [set.prod_mk_mem_set_prod_eq],
    classical,
    have h_eq_ite : (λ a, κ a {b : β | a ∈ t₁ ∧ b ∈ t₂})
      = (λ a, ite (a ∈ t₁) (κ a t₂) 0),
    { ext1 a,
      split_ifs,
      { simp only [h, true_and], refl, },
      { simp only [h, false_and, set.set_of_false, set.inter_empty, measure_empty], }, },
    rw h_eq_ite,
    exact measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const },
  { intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, {b : β | (a, b) ∈ t'ᶜ} = set.univ \ {b : β | (a, b) ∈ t'},
    { intro a,
      ext1 b,
      simp only [set.mem_compl_iff, set.mem_set_of_eq, set.mem_diff, set.mem_univ, true_and], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (set.univ \ {b : β | (a, b) ∈ t'}))
      = (λ a, (κ a set.univ - κ a {b : β | (a, b) ∈ t'})),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, set.inter_univ, measure_diff],
      { exact set.subset_univ _, },
      { exact (@measurable_prod_mk_left α β mα mβ a) t' ht', },
      { exact measure_ne_top _ _, }, },
    rw this,
    exact measurable.sub (kernel.measurable_coe κ measurable_set.univ) h_meas, },
  { intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a {b : β | (a, b) ∈ ⋃ i, f i}) = λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i}),
    { ext1 a,
      congr' with b,
      simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
      refl, },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i})) = λ a, ∑' i, κ a {b : β | (a, b) ∈ f i},
    { ext1 a,
      rw measure_Union,
      { exact λ i j hij b hb, h_disj i j hij hb, },
      { exact λ i, (@measurable_prod_mk_left α β mα mβ a) _ (hf_meas i), }, },
    rw h_tsum,
    exact measurable.ennreal_tsum hf, },
end

lemma measurable_lintegral_of_finite (κ : kernel mα mβ) (hκ : ∀ a, is_finite_measure (κ a))
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b, (⨆ n, (simple_func.eapprox (function.uncurry f) n) (a, b)) ∂κ a
    = ⨆ n, ∫⁻ b, (simple_func.eapprox (function.uncurry f) n) (a, b) ∂κ a,
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
    have : (λ a, ∫⁻ b, t.indicator (function.const (α × β) c) (a, b) ∂κ a)
      = (λ a, c * κ a {b | (a, b) ∈ t}),
    { ext1 a,
      rw lintegral_indicator' measurable_prod_mk_left ht,
      refl, },
    rw this,
    refine measurable.const_mul _ c,
    exact measurable_prod_mk_mem _ ht hκ, },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a)
      = (λ a, ∫⁻ b, g₁ (a, b) ∂κ a) + (λ a, ∫⁻ b, g₂ (a, b) ∂κ a),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left],
      exact g₁.measurable.comp measurable_prod_mk_left, },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable_set_lintegral_of_finite (κ : kernel mα mβ) [is_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂κ a) :=
by { simp_rw ← lintegral_restrict κ hs, exact measurable_lintegral_of_finite _ infer_instance _ hf }

section sum

protected noncomputable
def sum [countable ι] (κ : ι → kernel mα mβ) : kernel mα mβ :=
{ val := λ a, measure.sum (λ n, κ n a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    simp_rw measure.sum_apply _ hs,
    exact measurable.ennreal_tsum (λ n, kernel.measurable_coe (κ n) hs),
  end, }

lemma sum_apply [countable ι] (κ : ι → kernel mα mβ) (a : α) :
  kernel.sum κ a = measure.sum (λ n, κ n a) := rfl

lemma sum_apply' [countable ι] (κ : ι → kernel mα mβ) (a : α) {s : set β} (hs : measurable_set s) :
  kernel.sum κ a s = ∑' n, κ n a s :=
by rw [sum_apply κ a, measure.sum_apply _ hs]

lemma sum_comm [countable ι] (κ : ι → ι → kernel mα mβ) :
  kernel.sum (λ n, kernel.sum (κ n)) = kernel.sum (λ m, kernel.sum (λ n, κ n m)) :=
begin
  ext a s hs,
  simp_rw [sum_apply, measure.sum_apply _ hs],
  rw ennreal.tsum_comm,
end

end sum

class is_s_finite_kernel (κ : kernel mα mβ) : Prop :=
(tsum_finite : ∃ κs : ℕ → kernel mα mβ, (∀ n, is_finite_kernel (κs n)) ∧ κ = kernel.sum κs)

@[priority 100]
instance is_finite_kernel.is_s_finite_kernel [h : is_finite_kernel κ] : is_s_finite_kernel κ :=
⟨⟨λ n, if n = 0 then κ else 0,
  λ n, by { split_ifs, exact h, exact is_finite_kernel_zero _ _, },
  begin
    ext1 a,
    rw kernel.sum_apply,
    ext1 s hs,
    rw measure.sum_apply _ hs,
    have : (λ i, ((ite (i = 0) κ 0) a) s) = λ i, ite (i = 0) (κ a s) 0,
    { ext1 i, split_ifs; refl, },
    rw [this, tsum_ite_eq],
  end⟩⟩

noncomputable
def seq (κ : kernel mα mβ) [h : is_s_finite_kernel κ] :
  ℕ → kernel mα mβ :=
h.tsum_finite.some

lemma kernel_sum_seq (κ : kernel mα mβ) [h : is_s_finite_kernel κ] :
  kernel.sum (seq κ) = κ :=
h.tsum_finite.some_spec.2.symm

lemma measure_sum_seq (κ : kernel mα mβ) [h : is_s_finite_kernel κ] (a : α) :
  measure.sum (λ n, seq κ n a) = κ a :=
by rw [← kernel.sum_apply, kernel_sum_seq κ]

instance is_finite_kernel_seq (κ : kernel mα mβ) [h : is_s_finite_kernel κ] (n : ℕ) :
  is_finite_kernel (kernel.seq κ n) :=
h.tsum_finite.some_spec.1 n

lemma aux'' (κ : kernel mα mβ) {t : set (α × β)}
  (ht : measurable_set t) [is_s_finite_kernel κ] :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  rw ← kernel_sum_seq κ,
  have : (λ a, kernel.sum (seq κ) a {b : β | (a, b) ∈ t})
    = λ a, ∑' n, seq κ n a {b : β | (a, b) ∈ t},
  { ext1 a,
    rw kernel.sum_apply',
    exact measurable_prod_mk_left ht, },
  rw this,
  refine measurable.ennreal_tsum (λ n, _),
  exact measurable_prod_mk_mem (seq κ n) ht infer_instance,
end

lemma measurable_set_lintegral (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂κ a) :=
begin
  simp_rw ← measure_sum_seq κ,
  suffices : (λ (a : α), lintegral ((measure.sum (λ n, seq κ n a)).restrict s) (f a))
    = λ a, ∑' n, ∫⁻ b in s, f a b ∂(seq κ n a),
  { rw this,
    refine measurable.ennreal_tsum (λ n, _),
    exact measurable_set_lintegral_of_finite (seq κ n) f hf hs, },
  ext1 a,
  rw measure.restrict_sum _ hs,
  rw lintegral_sum_measure,
end

lemma measurable_lintegral (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂κ a) :=
begin
  convert measurable_set_lintegral κ f hf measurable_set.univ,
  simp only [measure.restrict_univ],
end

noncomputable
def with_density (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  kernel mα mβ :=
{ val := λ a, (κ a).with_density (f a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, (κ a).with_density (f a) s) = (λ a, ∫⁻ b in s, f a b ∂κ a),
    { ext1 a, exact with_density_apply (f a) hs, },
    rw this,
    exact measurable_set_lintegral κ f hf hs,
  end, }

protected lemma with_density_apply (κ : kernel mα mβ) [is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (function.uncurry f)) (a : α) :
  with_density κ f hf a = (κ a).with_density (f a) := rfl

lemma with_density_apply' (κ : kernel mα mβ) [is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (function.uncurry f)) (a : α) {s : set β}
  (hs : measurable_set s) :
  with_density κ f hf a s = ∫⁻ b in s, f a b ∂(κ a) :=
by rw [kernel.with_density_apply, with_density_apply _ hs]

lemma lintegral_with_density (κ : kernel mα mβ) [is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (function.uncurry f)) (a : α) {g : β → ℝ≥0∞}
  (hg : measurable g) :
  ∫⁻ b, g b ∂(with_density κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a) :=
begin
  rw kernel.with_density_apply,
  rw lintegral_with_density_eq_lintegral_mul _ _ hg,
  simp_rw pi.mul_apply,
  exact measurable.of_uncurry_left hf,
end

section composition

/-!
### Composition of kernels
 -/

noncomputable
def comp_fun (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ) (a : α) (s : set (β × γ)) : ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a

lemma comp_fun_empty (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ) (a : α) :
  comp_fun κ η a ∅ = 0 :=
by simp only [comp_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty, lintegral_const,
  zero_mul]

lemma comp_fun_Union_of_finite (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ)
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
  exact (measurable_prod_mk_mem η hm hη).comp measurable_prod_mk_left,
end

lemma comp_fun_tsum_right (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η]
  (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp_fun κ η a s = ∑' n, comp_fun κ (seq η n) a s :=
begin
  simp_rw [comp_fun, (measure_sum_seq η _).symm],
  have : ∫⁻ (b : β), ⇑(measure.sum (λ n, seq η n (a, b))) {c : γ | (b, c) ∈ s} ∂κ a
    = ∫⁻ (b : β), ∑' n, seq η n (a, b) {c : γ | (b, c) ∈ s} ∂κ a,
  { congr',
    ext1 b,
    rw measure.sum_apply,
    exact measurable_prod_mk_left hs, },
  rw [this, lintegral_tsum (λ n : ℕ, _)],
  exact (measurable_prod_mk_mem (seq η n) ((measurable_fst.snd.prod_mk measurable_snd) hs)
    infer_instance).comp measurable_prod_mk_left,
end

lemma comp_fun_tsum_left (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel κ]
  (a : α) (s : set (β × γ)) :
  comp_fun κ η a s = ∑' n, comp_fun (seq κ n) η a s :=
by simp_rw [comp_fun, (measure_sum_seq κ _).symm, lintegral_sum_measure]

lemma comp_fun_eq_tsum (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η]
  (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp_fun κ η a s = ∑' n m, comp_fun (seq κ n) (seq η m) a s :=
by simp_rw [comp_fun_tsum_left κ η a s, comp_fun_tsum_right _ η a hs]

lemma comp_fun_Union (κ : kernel mα mβ) (η : kernel (mα.prod mβ) mγ)
  [is_s_finite_kernel η] (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  comp_fun κ η a (⋃ i, f i) = ∑' i, comp_fun κ η a (f i) :=
begin
  rw comp_fun_tsum_right κ η a (measurable_set.Union hf_meas),
  have hn : ∀ n, comp_fun κ (seq η n) a (⋃ i, f i) = ∑' i, comp_fun κ (seq η n) a (f i),
  { intros n,
    rw comp_fun_Union_of_finite κ (seq η n) infer_instance a _ hf_meas hf_disj, },
  simp_rw hn,
  rw ennreal.tsum_comm,
  congr' 1,
  ext1 n,
  rw comp_fun_tsum_right κ η a (hf_meas n),
end

lemma measurable_comp_fun_of_finite (κ : kernel mα mβ) [is_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_finite_kernel η] {s : set (β × γ)} (hs : measurable_set s) :
  measurable (λ a, comp_fun κ η a s) :=
begin
  simp only [comp_fun],
  have h_meas : measurable (function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})
      = λ p, η p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem η (measurable_fst.snd.prod_mk measurable_snd hs) infer_instance, },
  exact measurable_lintegral κ (λ a b, η (a, b) {c : γ | (b, c) ∈ s}) h_meas,
end

lemma measurable_comp_fun (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] {s : set (β × γ)} (hs : measurable_set s) :
  measurable (λ a, comp_fun κ η a s) :=
begin
  simp_rw comp_fun_tsum_right κ η _ hs,
  refine measurable.ennreal_tsum (λ n, _),
  simp only [comp_fun],
  have h_meas : measurable (function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})
      = λ p, seq η n p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem (seq η n) (measurable_fst.snd.prod_mk measurable_snd hs)
      infer_instance, },
  exact measurable_lintegral κ (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s}) h_meas,
end

/-- Composition of finite kernels.

TODO update this:
About assumptions: the hypothesis `[is_finite_kernel κ]` could be replaced by
`∀ a, is_finite_measure (κ a)` to define the composition (same for `η`). This would be a weaker
hypothesis since it removes the uniform bound assumption of `is_finite_kernel`. However, that second
property is not stable by composition, in contrast to `is_finite_kernel`. Hence we choose to use the
typeclass with an uniform bound on `κ a univ`. -/
noncomputable
def comp (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] :
  kernel mα (mβ.prod mγ) :=
{ val := λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
        (comp_fun_Union κ η a) s) = λ a, comp_fun κ η a s,
    { ext1 a, rwa measure.of_measurable_apply, },
    rw this,
    exact measurable_comp_fun κ η hs,
  end, }

lemma comp_apply_eq_comp_fun (κ : kernel mα mβ) [is_s_finite_kernel κ] (η : kernel (mα.prod mβ) mγ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = comp_fun κ η a s :=
begin
  rw [comp],
  change measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a,
  rw measure.of_measurable_apply _ hs,
  refl,
end

lemma comp_apply (κ : kernel mα mβ) [is_s_finite_kernel κ] (η : kernel (mα.prod mβ) mγ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a :=
comp_apply_eq_comp_fun κ η a hs

lemma lintegral_comp (κ : kernel mα mβ) [is_s_finite_kernel κ] (η : kernel (mα.prod mβ) mγ)
  [is_s_finite_kernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : measurable (function.uncurry f)) :
  ∫⁻ bc, f bc.1 bc.2 ∂(comp κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw [← h, prod.mk.eta],
  have h_mono : monotone (λ (n : ℕ) (a : β × γ), simple_func.eapprox (function.uncurry f) n a),
  { intros i j hij b,
    have h_mono := simple_func.monotone_eapprox (function.uncurry f) hij,
    rw ← simple_func.coe_le at h_mono,
    exact h_mono _, },
  rw lintegral_supr,
  rotate,
  { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable, },
  { exact h_mono, },
  have : ∀ b, ∫⁻ c, (⨆ n, simple_func.eapprox (function.uncurry f) n (b, c)) ∂η (a, b)
    = ⨆ n, ∫⁻ c, simple_func.eapprox (function.uncurry f) n (b, c) ∂η (a, b),
  { intro a,
    rw lintegral_supr,
    { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable.comp
      measurable_prod_mk_left, },
    { exact λ i j hij b, h_mono hij _, }, },
  simp_rw this,
  have h_some_meas_integral : ∀ f' : simple_func (β × γ) ℝ≥0∞,
    measurable (λ b, ∫⁻ c, f' (b, c) ∂η (a, b)),
  { intros f',
    have : (λ b, ∫⁻ c, f' (b, c) ∂η (a, b))
        = (λ ab, ∫⁻ c, f' (ab.2, c) ∂η (ab))
          ∘ (λ b, (a, b)),
      { ext1 ab, refl, },
      rw this,
      refine measurable.comp _ measurable_prod_mk_left,
      refine (measurable_lintegral η _
        ((simple_func.measurable _).comp (measurable_fst.snd.prod_mk measurable_snd))), },
  rw lintegral_supr,
  rotate,
  { exact λ n, h_some_meas_integral (simple_func.eapprox (function.uncurry f) n), },
  { exact λ i j hij b, lintegral_mono (λ c, h_mono hij _), },
  congr,
  ext1 n,
  refine simple_func.induction _ _ (simple_func.eapprox (function.uncurry f) n),
  { intros c s hs,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    rw lintegral_indicator' measurable_id' hs,
    simp only [set.preimage_id'],
    rw comp_apply κ η _ hs,
    rw ← lintegral_const_mul c _,
    swap, { exact (aux'' η ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
      measurable_prod_mk_left, },
    congr,
    ext1 b,
    classical,
    rw lintegral_indicator' measurable_prod_mk_left hs,
    refl, },
  { intros f f' h_disj hf_eq hf'_eq,
    simp_rw [simple_func.coe_add],
    simp_rw pi.add_apply,
    change ∫⁻ x : β × γ, ((f : (β × γ) → ℝ≥0∞) x + f' x) ∂(comp κ η a)
      = ∫⁻ b, ∫⁻ (c : γ), f (b, c) + f' (b, c) ∂η (a, b) ∂κ a,
    rw [lintegral_add_left (simple_func.measurable _), hf_eq, hf'_eq, ← lintegral_add_left],
    swap, { exact h_some_meas_integral f, },
    congr,
    ext1 b,
    rw ← lintegral_add_left,
    exact (simple_func.measurable _).comp measurable_prod_mk_left, },
end

lemma comp_eq_tsum_comp (κ : kernel mα mβ) [is_s_finite_kernel κ] (η : kernel (mα.prod mβ) mγ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = ∑' (n m : ℕ), comp (seq κ n) (seq η m) a s :=
by { simp_rw comp_apply_eq_comp_fun _ _ _ hs, exact comp_fun_eq_tsum κ η a hs, }

lemma comp_eq_sum_kernel_comp (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, kernel.sum (λ m, comp (seq κ n) (seq η m))) :=
by { ext a s hs, simp_rw [kernel.sum_apply' _ a hs], rw comp_eq_tsum_comp κ η a hs, }

lemma comp_eq_sum_kernel_comp_left (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, comp (seq κ n) η) :=
begin
  rw comp_eq_sum_kernel_comp,
  congr,
  ext n a s hs,
  simp_rw [kernel.sum_apply' _ _ hs],
  simp_rw comp_apply_eq_comp_fun _ _ _ hs,
  rw comp_fun_tsum_right _ η a hs,
end

lemma comp_eq_sum_kernel_comp_right (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, comp κ (seq η n)) :=
begin
  rw comp_eq_sum_kernel_comp,
  simp_rw comp_eq_sum_kernel_comp_left κ _,
  rw kernel.sum_comm,
end

lemma comp_apply_univ_le (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_finite_kernel η] (a : α) :
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

instance is_finite_kernel.comp (κ : kernel mα mβ) [is_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_finite_kernel η] :
  is_finite_kernel (comp κ η) :=
⟨⟨is_finite_kernel.bound κ * is_finite_kernel.bound η,
  ennreal.mul_lt_top (is_finite_kernel.bound_ne_top κ) (is_finite_kernel.bound_ne_top η),
  λ a, calc comp κ η a set.univ
    ≤ (κ a set.univ) * is_finite_kernel.bound η : comp_apply_univ_le κ η a
... ≤ is_finite_kernel.bound κ * is_finite_kernel.bound η :
        ennreal.mul_le_mul (measure_le_bound κ a set.univ) le_rfl, ⟩⟩

lemma is_s_finite_kernel_of_eq_sum (κ : kernel mα mβ)
  (κs : ℕ → kernel mα mβ) (hκs : ∀ n, is_s_finite_kernel (κs n)) (hκ : κ = kernel.sum κs) :
  is_s_finite_kernel κ :=
begin
  let e : ℕ ≃ (ℕ × ℕ) := denumerable.equiv₂ ℕ (ℕ × ℕ),
  refine ⟨⟨λ n, seq (κs (e n).1) (e n).2, infer_instance, _⟩⟩,
  have hκ_eq : κ = kernel.sum (λ n, kernel.sum (seq (κs n))),
  { simp_rw kernel_sum_seq,
    exact hκ, },
  ext1 a,
  ext1 s hs,
  rw hκ_eq,
  simp_rw kernel.sum_apply' _ _ hs,
  change ∑' n m, seq (κs n) m a s = ∑' n, (λ nm : ℕ × ℕ, seq (κs nm.fst) nm.snd a s) (e n),
  rw e.tsum_eq,
  { rw tsum_prod' ennreal.summable (λ _, ennreal.summable), },
  { apply_instance, },
end

instance is_s_finite_kernel.comp (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel (mα.prod mβ) mγ) [is_s_finite_kernel η] :
  is_s_finite_kernel (comp κ η) :=
begin
  rw comp_eq_sum_kernel_comp_left,
  refine is_s_finite_kernel_of_eq_sum _ _ (λ n, _) rfl,
  refine ⟨⟨λ m, comp (seq κ n) (seq η m), infer_instance, _⟩⟩,
  rw comp_eq_sum_kernel_comp_right,
end

end composition

section map_comap
/-! ### map, comap and another composition -/

noncomputable
def map (κ : kernel mα mβ) (f : β → γ) (hf : measurable f) :
  kernel mα mγ :=
{ val := λ a, (κ a).map f,
  property := (measure.measurable_map _ hf).comp (kernel.measurable κ) }

lemma map_apply {mγ : measurable_space γ} (κ : kernel mα mβ) {f : β → γ}
  (hf : measurable f) (a : α) :
  map κ f hf a = (κ a).map f := rfl

lemma map_apply' {mγ : measurable_space γ} (κ : kernel mα mβ) {f : β → γ}
  (hf : measurable f) (a : α) {s : set γ} (hs : measurable_set s) :
  map κ f hf a s = κ a (f ⁻¹' s) :=
begin
  rw [map],
  change (κ a).map f s = κ a (f ⁻¹' s),
  exact measure.map_apply hf hs,
end

lemma lintegral_map {mγ : measurable_space γ} (κ : kernel mα mβ) {f : β → γ}
  (hf : measurable f) (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ b, g b ∂(map κ f hf a) = ∫⁻ a, g (f a) ∂κ a :=
by rw [map_apply _ hf, lintegral_map hg hf]

instance is_finite_kernel.map {mγ : measurable_space γ} (κ : kernel mα mβ)
  [is_finite_kernel κ] {f : β → γ} (hf : measurable f) :
  is_finite_kernel (map κ f hf) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw map_apply' κ hf a measurable_set.univ,
  exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.map {mγ : measurable_space γ} (κ : kernel mα mβ)
  [is_s_finite_kernel κ] {f : β → γ} (hf : measurable f) :
  is_s_finite_kernel (map κ f hf) :=
begin
  refine ⟨⟨λ n, map (seq κ n) f hf, infer_instance, _⟩⟩,
  ext a s hs,
  rw [kernel.sum_apply, map_apply' κ hf a hs, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ (hf hs)],
  simp_rw map_apply' _ hf _ hs,
end

def comap (κ : kernel mα mβ) (f : γ → α) (hf : measurable f) :
  kernel mγ mβ :=
{ val := λ a, κ (f a),
  property := (kernel.measurable κ).comp hf }

lemma comap_apply {mγ : measurable_space γ} (κ : kernel mα mβ) {f : γ → α}
  (hf : measurable f) (c : γ) (s : set β) :
  comap κ f hf c s = κ (f c) s :=
rfl

lemma lintegral_comap {mγ : measurable_space γ} (κ : kernel mα mβ) {f : γ → α}
  (hf : measurable f) (c : γ) {g : β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c)) :=
rfl

instance is_finite_kernel.comap {mγ : measurable_space γ} (κ : kernel mα mβ)
  [is_finite_kernel κ] {f : γ → α} (hf : measurable f) :
  is_finite_kernel (comap κ f hf) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw comap_apply κ hf a set.univ,
  exact measure_le_bound κ _ _,
end

instance is_s_finite_kernel.comap {mγ : measurable_space γ} (κ : kernel mα mβ)
  [is_s_finite_kernel κ] {f : γ → α} (hf : measurable f) :
  is_s_finite_kernel (comap κ f hf) :=
begin
  refine ⟨⟨λ n, comap (seq κ n) f hf, infer_instance, _⟩⟩,
  ext a s hs,
  rw [kernel.sum_apply, comap_apply κ hf a s, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ hs],
  simp_rw comap_apply _ hf _ s,
end

def prod_mk_left (κ : kernel mα mβ) (mγ : measurable_space γ) :
  kernel (mγ.prod mα) mβ :=
comap κ (λ a, a.2) measurable_snd

lemma prod_mk_left_apply (κ : kernel mα mβ) (mγ : measurable_space γ) (ca : γ × α)
  (s : set β) :
  prod_mk_left κ mγ ca s = (κ ca.snd) s :=
by rw [prod_mk_left, comap_apply _ _ _ s]

lemma lintegral_prod_mk_left (κ : kernel mα mβ) (mγ : measurable_space γ) (ca : γ × α)
  {g : β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ b, g b ∂(prod_mk_left κ mγ ca) = ∫⁻ b, g b ∂κ ca.snd :=
rfl

instance is_finite_kernel.prod_mk_left (κ : kernel mα mβ) [is_finite_kernel κ] :
  is_finite_kernel (prod_mk_left κ mγ) :=
by { rw prod_mk_left, apply_instance, }

instance is_s_finite_kernel.prod_mk_left (κ : kernel mα mβ) [is_s_finite_kernel κ] :
  is_s_finite_kernel (prod_mk_left κ mγ) :=
by { rw prod_mk_left, apply_instance, }

noncomputable
def snd_right (κ : kernel mα (mβ.prod mγ)) : kernel mα mγ :=
map κ (λ p, p.2) measurable_snd

lemma snd_right_apply (κ : kernel mα (mβ.prod mγ)) (a : α) {s : set γ}
  (hs : measurable_set s) :
  snd_right κ a s = κ a {p | p.2 ∈ s} :=
by { rw [snd_right, map_apply' _ _ _ hs], refl, }

lemma lintegral_snd_right (κ : kernel mα (mβ.prod mγ)) (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(snd_right κ a) = ∫⁻ (bc : β × γ), g bc.snd ∂(κ a) :=
by rw [snd_right, lintegral_map _ measurable_snd a hg]

lemma snd_right_univ (κ : kernel mα (mβ.prod mγ)) (a : α) :
  snd_right κ a set.univ = κ a set.univ :=
snd_right_apply _ _ measurable_set.univ

instance is_finite_kernel.snd_right (κ : kernel mα (mβ.prod mγ)) [is_finite_kernel κ] :
  is_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

instance is_s_finite_kernel.snd_right (κ : kernel mα (mβ.prod mγ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

noncomputable
def comp2 (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel mβ mγ) [is_s_finite_kernel η] :
  kernel mα mγ :=
snd_right (comp κ (prod_mk_left η mα))

lemma comp2_apply (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel mβ mγ) [is_s_finite_kernel η] (a : α) {s : set γ}
  (hs : measurable_set s) :
  comp2 κ η a s = ∫⁻ b, η b s ∂κ a :=
begin
  rw [comp2, snd_right_apply _ _ hs, comp_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq],
  simp_rw prod_mk_left_apply _ _ _ s,
end

lemma lintegral_comp2 (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel mβ mγ) [is_s_finite_kernel η] (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(comp2 κ η a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a) :=
begin
  rw [comp2, lintegral_snd_right _ _ hg],
  change ∫⁻ (bc : β × γ), (λ a b, g b) bc.fst bc.snd ∂(comp κ (prod_mk_left η mα)) a
    = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂κ a,
  rw lintegral_comp,
  swap, { exact hg.comp measurable_snd, },
  refl,
end

instance is_finite_kernel.comp2 (κ : kernel mα mβ) [is_finite_kernel κ]
  (η : kernel mβ mγ) [is_finite_kernel η] :
  is_finite_kernel (comp2 κ η) :=
by { rw comp2, apply_instance, }

instance is_s_finite_kernel.comp2 (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel mβ mγ) [is_s_finite_kernel η] :
  is_s_finite_kernel (comp2 κ η) :=
by { rw comp2, apply_instance, }

lemma comp2_assoc (κ : kernel mα mβ) [is_s_finite_kernel κ]
  (η : kernel mβ mγ) [is_s_finite_kernel η]
  (ξ : kernel mγ mδ) [is_s_finite_kernel ξ] :
  comp2 (comp2 κ η) ξ = comp2 κ (comp2 η ξ) :=
begin
  refine ext_fun (λ a f hf, _),
  simp_rw lintegral_comp2 _ _ _ hf,
  have h_meas : measurable (λ b, ∫⁻ d, f d ∂(ξ b)),
    from measurable_lintegral ξ _ (hf.comp measurable_snd),
  rw lintegral_comp2 _ _ _ h_meas,
end

lemma comp2_deterministic_right_eq_map {mγ : measurable_space γ}
  (κ : kernel mα mβ) [is_s_finite_kernel κ]
  {f : β → γ} (hf : measurable f) :
  comp2 κ (deterministic hf) = map κ f hf :=
begin
  ext a s hs,
  simp_rw [map_apply' _ _ _ hs, comp2_apply _ _ _ hs, deterministic_apply hf _ hs,
    lintegral_indicator' hf hs, one_mul],
end

lemma comp2_deterministic_left_eq_comap {mγ : measurable_space γ} {f : γ → α} (hf : measurable f)
  (κ : kernel mα mβ) [is_s_finite_kernel κ] :
  comp2 (deterministic hf) κ = comap κ f hf :=
begin
  ext a s hs,
  simp_rw [comap_apply _ _ _ s, comp2_apply _ _ _ hs, coe_fn_deterministic hf a,
    lintegral_dirac' _ (kernel.measurable_coe κ hs)],
end

end map_comap

end kernel

end measure_theory
