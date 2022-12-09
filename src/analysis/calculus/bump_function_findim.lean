/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.specific_functions
import analysis.calculus.series
import analysis.convolution
import data.set.pointwise.support

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `is_open.exists_smooth_support_eq`.

TODO: use this construction to construct bump functions with nice behavior in any finite-dimensional
real normed vector space, by convolving the indicator function of `closed_ball 0 1` with a
function as above with `s = ball 0 D`.
-/

noncomputable theory

open set metric topological_space function asymptotics measure_theory finite_dimensional
continuous_linear_map filter measure_theory.measure
open_locale pointwise topological_space nnreal big_operators convolution

variables {E : Type*} [normed_add_comm_group E]

section

variables [normed_space ℝ E] [finite_dimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
theorem exists_smooth_tsupport_subset {s : set E} {x : E} (hs : s ∈ 𝓝 x) :
  ∃ (f : E → ℝ), tsupport f ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1 ∧ f x = 1 :=
begin
  obtain ⟨d, d_pos, hd⟩ : ∃ (d : ℝ) (hr : 0 < d), euclidean.closed_ball x d ⊆ s,
    from euclidean.nhds_basis_closed_ball.mem_iff.1 hs,
  let c : cont_diff_bump_of_inner (to_euclidean x) :=
  { r := d/2,
    R := d,
    r_pos := half_pos d_pos,
    r_lt_R := half_lt_self d_pos },
  let f : E → ℝ := c ∘ to_euclidean,
  have f_supp : f.support ⊆ euclidean.ball x d,
  { assume y hy,
    have : to_euclidean y ∈ function.support c,
      by simpa only [f, function.mem_support, function.comp_app, ne.def] using hy,
    rwa c.support_eq at this },
  have f_tsupp : tsupport f ⊆ euclidean.closed_ball x d,
  { rw [tsupport, ← euclidean.closure_ball _ d_pos.ne'],
    exact closure_mono f_supp },
  refine ⟨f, f_tsupp.trans hd, _, _, _, _⟩,
  { refine is_compact_of_is_closed_bounded is_closed_closure _,
    have : bounded (euclidean.closed_ball x d), from euclidean.is_compact_closed_ball.bounded,
    apply this.mono _,
    refine (is_closed.closure_subset_iff euclidean.is_closed_closed_ball).2 _,
    exact f_supp.trans euclidean.ball_subset_closed_ball },
  { apply c.cont_diff.comp,
    exact continuous_linear_equiv.cont_diff _ },
  { rintros t ⟨y, rfl⟩,
    exact ⟨c.nonneg, c.le_one⟩ },
  { apply c.one_of_mem_closed_ball,
    apply mem_closed_ball_self,
    exact (half_pos d_pos).le }
end

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
  nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
  countably many such functions, say `g i`.
  Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
  tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th derivative
  of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the summability
  of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with rfl|h's,
  { exact ⟨(λ x, 0), function.support_zero, cont_diff_const,
      by simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩ },
  let ι := {f : E → ℝ // f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1},
  obtain ⟨T, T_count, hT⟩ : ∃ T : set ι, T.countable ∧ (⋃ f ∈ T, support (f : E → ℝ)) = s,
  { have : (⋃ (f : ι), (f : E → ℝ).support) = s,
    { refine subset.antisymm (Union_subset (λ f, f.2.1)) _,
      assume x hx,
      rcases exists_smooth_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩,
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩,
      have : x ∈ support (g : E → ℝ),
        by simp only [hf.2.2.2.2, subtype.coe_mk, mem_support, ne.def, one_ne_zero, not_false_iff],
      exact mem_Union_of_mem _ this },
    simp_rw ← this,
    apply is_open_Union_countable,
    rintros ⟨f, hf⟩,
    exact hf.2.2.1.continuous.is_open_support },
  obtain ⟨g0, hg⟩ : ∃ (g0 : ℕ → ι), T = range g0,
  { apply countable.exists_eq_range T_count,
    rcases eq_empty_or_nonempty T with rfl|hT,
    { simp only [Union_false, Union_empty] at hT,
      simp only [←hT, not_nonempty_empty] at h's,
      exact h's.elim },
    { exact hT } },
  let g : ℕ → E → ℝ := λ n, (g0 n).1,
  have g_s : ∀ n, support (g n) ⊆ s := λ n, (g0 n).2.1,
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n),
  { assume x hx,
    rw ← hT at hx,
    obtain ⟨i, iT, hi⟩ : ∃ (i : ι) (hi : i ∈ T), x ∈ support (i : E → ℝ),
      by simpa only [mem_Union] using hx,
    rw [hg, mem_range] at iT,
    rcases iT with ⟨n, hn⟩,
    rw ← hn at hi,
    exact ⟨n, hi⟩ },
  have g_smooth : ∀ n, cont_diff ℝ ⊤ (g n) := λ n, (g0 n).2.2.2.1,
  have g_comp_supp : ∀ n, has_compact_support (g n) := λ n, (g0 n).2.2.1,
  have g_nonneg : ∀ n x, 0 ≤ g n x,
    from λ n x, ((g0 n).2.2.2.2 (mem_range_self x)).1,
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
    ∃ (δ : ℕ → ℝ≥0), (∀ (i : ℕ), 0 < δ i) ∧ ∃ (c : nnreal), has_sum δ c ∧ c < 1,
    from nnreal.exists_pos_sum_of_countable one_ne_zero ℕ,
  have : ∀ (n : ℕ), ∃ (r : ℝ),
    0 < r ∧ ∀ i ≤ n, ∀ x, ‖iterated_fderiv ℝ i (r • g n) x‖ ≤ δ n,
  { assume n,
    have : ∀ i, ∃ R, ∀ x, ‖iterated_fderiv ℝ i (λ x, g n x) x‖ ≤ R,
    { assume i,
      have : bdd_above (range (λ x, ‖iterated_fderiv ℝ i (λ (x : E), g n x) x‖)),
      { apply ((g_smooth n).continuous_iterated_fderiv le_top).norm
          .bdd_above_range_of_has_compact_support,
        apply has_compact_support.comp_left _ norm_zero,
        apply (g_comp_supp n).iterated_fderiv },
      rcases this with ⟨R, hR⟩,
      exact ⟨R, λ x, hR (mem_range_self _)⟩ },
    choose R hR using this,
    let M := max (((finset.range (n+1)).image R).max' (by simp)) 1,
    have M_pos : 0 < M := zero_lt_one.trans_le (le_max_right _ _),
    have δnpos : 0 < δ n := δpos n,
    have IR : ∀ i ≤ n, R i ≤ M,
    { assume i hi,
      refine le_trans _ (le_max_left _ _),
      apply finset.le_max',
      apply finset.mem_image_of_mem,
      simp only [finset.mem_range],
      linarith },
    refine ⟨M⁻¹ * δ n, by positivity, λ i hi x, _⟩,
    calc ‖iterated_fderiv ℝ i ((M⁻¹ * δ n) • g n) x‖
        = ‖(M⁻¹ * δ n) • iterated_fderiv ℝ i (g n) x‖ :
      by { rw iterated_fderiv_const_smul_apply, exact (g_smooth n).of_le le_top }
    ... = M⁻¹ * δ n * ‖iterated_fderiv ℝ i (g n) x‖ :
      by { rw [norm_smul, real.norm_of_nonneg], positivity }
    ... ≤ M⁻¹ * δ n * M :
      mul_le_mul_of_nonneg_left ((hR i x).trans (IR i hi)) (by positivity)
    ... = δ n : by field_simp [M_pos.ne'] },
  choose r rpos hr using this,
  have S : ∀ x, summable (λ n, (r n • g n) x),
  { assume x,
    refine summable_of_nnnorm_bounded _ δc.summable (λ n, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm],
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) x },
  refine ⟨λ x, (∑' n, (r n • g n) x), _, _, _⟩,
  { apply subset.antisymm,
    { assume x hx,
      simp only [pi.smul_apply, algebra.id.smul_eq_mul, mem_support, ne.def] at hx,
      contrapose! hx,
      have : ∀ n, g n x = 0,
      { assume n,
        contrapose! hx,
        exact g_s n hx },
      simp only [this, mul_zero, tsum_zero] },
    { assume x hx,
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n), from s_g x hx,
      have I : 0 < r n * g n x,
        from mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (ne.symm hn)),
      exact ne_of_gt (tsum_pos (S x) (λ i, mul_nonneg (rpos i).le (g_nonneg i x)) n I) } },
  { refine cont_diff_tsum_of_eventually (λ n, (g_smooth n).const_smul _)
      (λ k hk, (nnreal.has_sum_coe.2 δc).summable) _,
    assume i hi,
    simp only [nat.cofinite_eq_at_top, pi.smul_apply, algebra.id.smul_eq_mul,
      filter.eventually_at_top, ge_iff_le],
    exact ⟨i, λ n hn x, hr _ _ hn _⟩ },
  { rintros - ⟨y, rfl⟩,
    refine ⟨tsum_nonneg (λ n, mul_nonneg (rpos n).le (g_nonneg n y)), le_trans _ c_lt.le⟩,
    have A : has_sum (λ n, (δ n : ℝ)) c, from nnreal.has_sum_coe.2 δc,
    rw ← A.tsum_eq,
    apply tsum_le_tsum _ (S y) A.summable,
    assume n,
    apply (le_abs_self _).trans,
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) y }
end

end
