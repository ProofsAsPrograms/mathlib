/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry

/-! # Constructions of continuous linear maps between (semi-)normed spaces

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`linear_map` `f : E →ₛₗ[σ] F` is the coercion of some `continuous_linear_map` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `linear_map.mk_continuous`, boundedness implies continuity. The
other direction, `continuous_linear_map.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`continuous_linear_map.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `linear_map.mk_continuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

open metric continuous_linear_map
open set real

open_locale nnreal

variables {𝕜 𝕜₂ E F G 𝓕 : Type*}

section
variables [normed_field 𝕜] [normed_field 𝕜₂]

/-! ## For a general normed field

### General constructions -/

section seminormed

variables [seminormed_add_comm_group E] [seminormed_add_comm_group F] [seminormed_add_comm_group G]
variables [normed_space 𝕜 E] [normed_space 𝕜₂ F] [normed_space 𝕜 G]
variables {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
⟨f, add_monoid_hom_class.continuous_of_bound f C h⟩

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def linear_map.to_continuous_linear_map₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
f.mk_continuous (‖f 1‖) $ λ x, le_of_eq $
by { conv_lhs { rw ← mul_one x }, rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm] }

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
⟨f, let ⟨C, hC⟩ := h in add_monoid_hom_class.continuous_of_bound f C hC⟩

lemma continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = (σ c) • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C*‖x‖) :
  continuous f :=
let φ : E →ₛₗ[σ] F := { to_fun := f, map_add' := h_add, map_smul' := h_smul } in
add_monoid_hom_class.continuous_of_bound φ C h_bound

lemma continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C*‖x‖) :
  continuous f :=
let φ : E →ₗ[𝕜] G := { to_fun := f, map_add' := h_add, map_smul' := h_smul } in
add_monoid_hom_class.continuous_of_bound φ C h_bound

@[simp, norm_cast] lemma linear_map.mk_continuous_coe (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ((f.mk_continuous C h) : E →ₛₗ[σ] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_apply (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
  f.mk_continuous C h x = f x := rfl

@[simp, norm_cast] lemma linear_map.mk_continuous_of_exists_bound_coe
  (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ((f.mk_continuous_of_exists_bound h) : E →ₛₗ[σ] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_of_exists_bound_apply (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x := rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_coe (f : 𝕜 →ₗ[𝕜] E) :
  (f.to_continuous_linear_map₁ : 𝕜 →ₗ[𝕜] E) = f :=
rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
  f.to_continuous_linear_map₁ x = f x :=
rfl

namespace continuous_linear_map

theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
  antilipschitz_with K f :=
add_monoid_hom_class.antilipschitz_of_bound _ h

lemma bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : antilipschitz_with K f) (x) :
  ‖x‖ ≤ K * ‖f x‖ :=
add_monoid_hom_class.bound_of_antilipschitz _ h x

end continuous_linear_map

section

variables {σ₂₁ : 𝕜₂ →+* 𝕜} [ring_hom_inv_pair σ σ₂₁] [ring_hom_inv_pair σ₂₁ σ]

include σ₂₁

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def linear_equiv.to_continuous_linear_equiv_of_bounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
  (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F :=
{ to_linear_equiv := e,
  continuous_to_fun := add_monoid_hom_class.continuous_of_bound e C_to h_to,
  continuous_inv_fun := add_monoid_hom_class.continuous_of_bound e.symm C_inv h_inv }

end

end seminormed

section normed

variables [normed_add_comm_group E] [normed_add_comm_group F] [normed_space 𝕜 E] [normed_space 𝕜₂ F]
variables {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

theorem continuous_linear_map.uniform_embedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
  uniform_embedding f :=
(add_monoid_hom_class.antilipschitz_of_bound f hf).uniform_embedding f.uniform_continuous

end normed

/-! # Homotheties -/

section seminormed

variables [seminormed_add_comm_group E] [seminormed_add_comm_group F]
variables [normed_space 𝕜 E] [normed_space 𝕜₂ F]
variables {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- A (semi-)linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def continuous_linear_map.of_homothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀x, ‖f x‖ = a * ‖x‖) :
  E →SL[σ] F :=
f.mk_continuous a (λ x, le_of_eq (hf x))

variables {σ₂₁ : 𝕜₂ →+* 𝕜} [ring_hom_inv_pair σ σ₂₁] [ring_hom_inv_pair σ₂₁ σ]

include σ₂₁

lemma continuous_linear_equiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
  (∀ (x : E), ‖f x‖ = a * ‖x‖) → (∀ (y : F), ‖f.symm y‖ = a⁻¹ * ‖y‖) :=
begin
  intros hf y,
  calc ‖(f.symm) y‖ = a⁻¹ * (a * ‖ (f.symm) y‖) : _
  ... =  a⁻¹ * ‖f ((f.symm) y)‖ : by rw hf
  ... = a⁻¹ * ‖y‖ : by simp,
  rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul],
end

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
noncomputable def continuous_linear_equiv.of_homothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
  (hf : ∀x, ‖f x‖ = a * ‖x‖) :
  E ≃SL[σ] F :=
linear_equiv.to_continuous_linear_equiv_of_bounds f a a⁻¹
  (λ x, (hf x).le) (λ x, (continuous_linear_equiv.homothety_inverse a ha f hf x).le)

end seminormed

/-! # The span of a single vector -/

section seminormed

variables [seminormed_add_comm_group E] [normed_space 𝕜 E]

namespace linear_isometry
variables (𝕜 E)

/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
    isometry map from `𝕜` to `E` by taking multiples of `x`.-/
def to_span_singleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
{ norm_map' := λ x, by simp [norm_smul, hv],
  .. linear_map.to_span_singleton 𝕜 E v }
variables {𝕜 E}

@[simp] lemma to_span_singleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
  to_span_singleton 𝕜 E hv a = a • v :=
rfl

@[simp] lemma coe_to_span_singleton {v : E} (hv : ‖v‖ = 1) :
  (to_span_singleton 𝕜 E hv).to_linear_map = linear_map.to_span_singleton 𝕜 E v :=
rfl

end linear_isometry

namespace continuous_linear_map

variable (𝕜)

lemma to_span_singleton_homothety (x : E) (c : 𝕜) :
  ‖linear_map.to_span_singleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ :=
by {rw mul_comm, exact norm_smul _ _}

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `𝕜` to `E` by taking multiples of `x`.-/
def to_span_singleton (x : E) : 𝕜 →L[𝕜] E :=
of_homothety (linear_map.to_span_singleton 𝕜 E x) ‖x‖ (to_span_singleton_homothety 𝕜 x)

lemma to_span_singleton_apply (x : E) (r : 𝕜) : to_span_singleton 𝕜 x r = r • x :=
by simp [to_span_singleton, of_homothety, linear_map.to_span_singleton]

lemma to_span_singleton_add (x y : E) :
  to_span_singleton 𝕜 (x + y) = to_span_singleton 𝕜 x + to_span_singleton 𝕜 y :=
by { ext1, simp [to_span_singleton_apply], }

lemma to_span_singleton_smul' (𝕜') [normed_field 𝕜'] [normed_space 𝕜' E]
  [smul_comm_class 𝕜 𝕜' E] (c : 𝕜') (x : E) :
  to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
by { ext1, rw [to_span_singleton_apply, smul_apply, to_span_singleton_apply, smul_comm], }

lemma to_span_singleton_smul (c : 𝕜) (x : E) :
  to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
to_span_singleton_smul' 𝕜 𝕜 c x

end continuous_linear_map

section

namespace continuous_linear_equiv

variable (𝕜)

lemma to_span_nonzero_singleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
  ‖linear_equiv.to_span_nonzero_singleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
continuous_linear_map.to_span_singleton_homothety _ _ _

end continuous_linear_equiv

end

end seminormed

section normed

variables [normed_add_comm_group E] [normed_space 𝕜 E]

namespace continuous_linear_equiv
variable (𝕜)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
noncomputable def to_span_nonzero_singleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] (𝕜 ∙ x) :=
of_homothety
  (linear_equiv.to_span_nonzero_singleton 𝕜 E x h)
  ‖x‖
  (norm_pos_iff.mpr h)
  (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
noncomputable def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 :=
  (to_span_nonzero_singleton 𝕜 x h).symm

@[simp] lemma coe_to_span_nonzero_singleton_symm {x : E} (h : x ≠ 0) :
  ⇑(to_span_nonzero_singleton 𝕜 x h).symm = coord 𝕜 x h := rfl

@[simp] lemma coord_to_span_nonzero_singleton {x : E} (h : x ≠ 0) (c : 𝕜) :
  coord 𝕜 x h (to_span_nonzero_singleton 𝕜 x h c) = c :=
(to_span_nonzero_singleton 𝕜 x h).symm_apply_apply c

@[simp] lemma to_span_nonzero_singleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
  to_span_nonzero_singleton 𝕜 x h (coord 𝕜 x h y) = y :=
(to_span_nonzero_singleton 𝕜 x h).apply_symm_apply y

@[simp] lemma coord_self (x : E) (h : x ≠ 0) :
  (coord 𝕜 x h) (⟨x, submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
linear_equiv.coord_self 𝕜 E x h

end continuous_linear_equiv

end normed

end

/-! ## For a nontrivially normed field -/

section
variables [nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂]

section semi_normed

variables [seminormed_add_comm_group E] [seminormed_add_comm_group F]
  [normed_space 𝕜 E] [normed_space 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂}

/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
lemma norm_image_of_norm_zero [semilinear_map_class 𝓕 σ E F] (f : 𝓕)
  (hf : continuous f) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 :=
begin
  refine le_antisymm (le_of_forall_pos_le_add (λ ε hε, _)) (norm_nonneg (f x)),
  rcases normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩,
  replace hδ := hδ x,
  rw [sub_zero, hx] at hδ,
  replace hδ := le_of_lt (hδ δ_pos),
  rw [map_zero, sub_zero] at hδ,
  rwa [zero_add]
end

variables [ring_hom_isometric σ]

lemma semilinear_map_class.bound_of_shell_semi_normed [semilinear_map_class 𝓕 σ E F]
  (f : 𝓕) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
  (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
  ‖f x‖ ≤ C * ‖x‖ :=
begin
  rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, δinv⟩,
  have := hf (δ • x) leδx δxle,
  simpa only [map_smulₛₗ, norm_smul, mul_left_comm C, mul_le_mul_left (norm_pos_iff.2 hδ),
              ring_hom_isometric.is_iso] using hf (δ • x) leδx δxle
end

/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
lemma semilinear_map_class.bound_of_continuous [semilinear_map_class 𝓕 σ E F] (f : 𝓕)
  (hf : continuous f) : ∃ C, 0 < C ∧ (∀ x : E, ‖f x‖ ≤ C * ‖x‖) :=
begin
  rcases normed_add_comm_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  simp only [sub_zero, map_zero] at hε,
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have : 0 < ‖c‖ / ε, from div_pos (zero_lt_one.trans hc) ε_pos,
  refine ⟨‖c‖ / ε, this, λ x, _⟩,
  by_cases hx : ‖x‖ = 0,
  { rw [hx, mul_zero],
    exact le_of_eq (norm_image_of_norm_zero f hf hx) },
  refine semilinear_map_class.bound_of_shell_semi_normed f ε_pos hc (λ x hle hlt, _) hx,
  refine (hε _ hlt).le.trans _,
  rwa [← div_le_iff' this, one_div_div]
end

theorem continuous_linear_map.bound (f : E →SL[σ] F) :
  ∃ C, 0 < C ∧ (∀ x : E, ‖f x‖ ≤ C * ‖x‖) :=
semilinear_map_class.bound_of_continuous f f.2

end semi_normed

section normed
variables [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]

variables
  [normed_space 𝕜 E] [normed_space 𝕜₂ F] [normed_space 𝕜 G]
  {σ : 𝕜 →+* 𝕜₂}
  (f g : E →SL[σ] F) (x y z : E)

lemma linear_map.bound_of_shell [ring_hom_isometric σ] (f : E →ₛₗ[σ] F) {ε C : ℝ}
  (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
  (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
  ‖f x‖ ≤ C * ‖x‖ :=
begin
  by_cases hx : x = 0, { simp [hx] },
  exact semilinear_map_class.bound_of_shell_semi_normed f ε_pos hc hf
    (ne_of_lt (norm_pos_iff.2 hx)).symm
end

/--
`linear_map.bound_of_ball_bound'` is a version of this lemma over a field satisfying `is_R_or_C`
that produces a concrete bound.
-/
lemma linear_map.bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] G)
  (h : ∀ z ∈ metric.ball (0 : E) r, ‖f z‖ ≤ c) :
  ∃ C, ∀ (z : E), ‖f z‖ ≤ C * ‖z‖ :=
begin
  cases @nontrivially_normed_field.non_trivial 𝕜 _ with k hk,
  use c * (‖k‖ / r),
  intro z,
  refine linear_map.bound_of_shell _ r_pos hk (λ x hko hxo, _) _,
  calc ‖f x‖ ≤ c : h _ (mem_ball_zero_iff.mpr hxo)
         ... ≤ c * ((‖x‖ * ‖k‖) / r) : le_mul_of_one_le_right _ _
         ... = _ : by ring,
  { exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos])) },
  { rw [div_le_iff (zero_lt_one.trans hk)] at hko,
    exact (one_le_div r_pos).mpr hko }
end

namespace continuous_linear_map

/-- If a continuous linear map is a uniform embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_uniform_embedding (f : E →L[𝕜] G) (hf : uniform_embedding f) :
  ∃ K, antilipschitz_with K f :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ {x y : E}, dist (f x) (f y) < ε → dist x y < 1,
    from (uniform_embedding_iff.1 hf).2.2 1 zero_lt_one,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos εpos,
  have H : ∀{x}, ‖f x‖ ≤ δ → ‖x‖ ≤ 1,
  { assume x hx,
    have : dist x 0 ≤ 1,
    { refine (hε _).le,
      rw [f.map_zero, dist_zero_right],
      exact hx.trans_lt (half_lt_self εpos) },
    simpa using this },
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine ⟨⟨δ⁻¹, _⟩ * ‖c‖₊, add_monoid_hom_class.antilipschitz_of_bound f $ λx, _⟩,
  exact inv_nonneg.2 (le_of_lt δ_pos),
  by_cases hx : f x = 0,
  { have : f x = f 0, by { simp [hx] },
    have : x = 0 := (uniform_embedding_iff.1 hf).1 this,
    simp [this] },
  { rcases rescale_to_shell hc δ_pos hx with ⟨d, hd, dxlt, ledx, dinv⟩,
    rw [← f.map_smul d] at dxlt,
    have : ‖d • x‖ ≤ 1 := H dxlt.le,
    calc ‖x‖ = ‖d‖⁻¹ * ‖d • x‖ :
      by rwa [← norm_inv, ← norm_smul, ← mul_smul, inv_mul_cancel, one_smul]
    ... ≤ ‖d‖⁻¹ * 1 :
      mul_le_mul_of_nonneg_left this (inv_nonneg.2 (norm_nonneg _))
    ... ≤ δ⁻¹ * ‖c‖ * ‖f x‖ :
      by rwa [mul_one] }
end

end continuous_linear_map

end normed

end
