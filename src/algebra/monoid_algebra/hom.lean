/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury G. Kudryashov, Scott Morrison
-/
import algebra.algebra.equiv
import algebra.hom.non_unital_alg
import algebra.monoid_algebra.basic
import linear_algebra.finsupp

/-!
# Monoid algebras

TODO
-/

noncomputable theory
open_locale big_operators

open finset finsupp

universes u₁ u₂ u₃
variables (k : Type u₁) (G : Type u₂) {R : Type*}

namespace monoid_algebra

variables {k G}

/-! #### Non-unital, non-associative algebra structure -/
section non_unital_non_assoc_algebra

variables (k) [semiring k] [distrib_smul R k] [has_mul G]
variables {A : Type u₃} [non_unital_non_assoc_semiring A]
/-- A non_unital `k`-algebra homomorphism from `monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
lemma non_unital_alg_hom_ext [distrib_mul_action k A]
  {φ₁ φ₂ : monoid_algebra k G →ₙₐ[k] A}
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
non_unital_alg_hom.to_distrib_mul_action_hom_injective $
  finsupp.distrib_mul_action_hom_ext' $
  λ a, distrib_mul_action_hom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma non_unital_alg_hom_ext' [distrib_mul_action k A]
  {φ₁ φ₂ : monoid_algebra k G →ₙₐ[k] A}
  (h : φ₁.to_mul_hom.comp (of_magma k G) = φ₂.to_mul_hom.comp (of_magma k G)) : φ₁ = φ₂ :=
non_unital_alg_hom_ext k $ mul_hom.congr_fun h

/-- The functor `G ↦ monoid_algebra k G`, from the category of magmas to the category of non-unital,
non-associative algebras over `k` is adjoint to the forgetful functor in the other direction. -/
@[simps] def lift_magma [module k A] [is_scalar_tower k A A] [smul_comm_class k A A] :
  (G →ₙ* A) ≃ (monoid_algebra k G →ₙₐ[k] A) :=
{ to_fun    := λ f,
    { to_fun    := λ a, a.sum (λ m t, t • f m),
      map_smul' :=  λ t' a,
        begin
          rw [finsupp.smul_sum, sum_smul_index'],
          { simp_rw smul_assoc, },
          { intros m, exact zero_smul k (f m), },
        end,
      map_mul'  := λ a₁ a₂,
        begin
          let g : G → k → A := λ m t, t • f m,
          have h₁ : ∀ m, g m 0 = 0, { intros, exact zero_smul k (f m), },
          have h₂ : ∀ m (t₁ t₂ : k), g m (t₁ + t₂) = g m t₁ + g m t₂, { intros, rw ← add_smul, },
          simp_rw [finsupp.mul_sum, finsupp.sum_mul, smul_mul_smul, ← f.map_mul, mul_def,
            sum_comm a₂ a₁, sum_sum_index h₁ h₂, sum_single_index (h₁ _)],
        end,
      .. lift_add_hom (λ x, (smul_add_hom k A).flip (f x)) },
  inv_fun   := λ F, F.to_mul_hom.comp (of_magma k G),
  left_inv  := λ f, by { ext m, simp only [non_unital_alg_hom.coe_mk, of_magma_apply,
    non_unital_alg_hom.to_mul_hom_eq_coe, sum_single_index, function.comp_app, one_smul, zero_smul,
    mul_hom.coe_comp, non_unital_alg_hom.coe_to_mul_hom], },
  right_inv := λ F, by { ext m, simp only [non_unital_alg_hom.coe_mk, of_magma_apply,
    non_unital_alg_hom.to_mul_hom_eq_coe, sum_single_index, function.comp_app, one_smul, zero_smul,
    mul_hom.coe_comp, non_unital_alg_hom.coe_to_mul_hom], }, }

end non_unital_non_assoc_algebra

/-! #### Algebra structure -/
section algebra

local attribute [reducible] monoid_algebra
/-- `finsupp.single 1` as a `alg_hom` -/
@[simps]
def single_one_alg_hom {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] :
  A →ₐ[k] monoid_algebra A G :=
{ commutes' := λ r, by { ext, simp, }, ..single_one_ring_hom}

end algebra

section lift

variables {k G} [comm_semiring k] [monoid G]
variables {A : Type u₃} [semiring A] [algebra k A] {B : Type*} [semiring B] [algebra k B]

/-- `lift_nc_ring_hom` as a `alg_hom`, for when `f` is an `alg_hom` -/
def lift_nc_alg_hom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ x y, commute (f x) (g y)) :
  monoid_algebra A G →ₐ[k] B :=
{ to_fun := lift_nc_ring_hom (f : A →+* B) g h_comm,
  commutes' := by simp [lift_nc_ring_hom],
  ..(lift_nc_ring_hom (f : A →+* B) g h_comm)}

/-- A `k`-algebra homomorphism from `monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
lemma alg_hom_ext ⦃φ₁ φ₂ : monoid_algebra k G →ₐ[k] A⦄
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
alg_hom.to_linear_map_injective $ finsupp.lhom_ext' $ λ a, linear_map.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma alg_hom_ext' ⦃φ₁ φ₂ : monoid_algebra k G →ₐ[k] A⦄
  (h : (φ₁ : monoid_algebra k G →* A).comp (of k G) =
    (φ₂ : monoid_algebra k G →* A).comp (of k G)) : φ₁ = φ₂ :=
alg_hom_ext $ monoid_hom.congr_fun h

variables (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`monoid_algebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (monoid_algebra k G →ₐ[k] A) :=
{ inv_fun := λ f, (f : monoid_algebra k G →* A).comp (of k G),
  to_fun := λ F, lift_nc_alg_hom (algebra.of_id k A) F $ λ _ _, algebra.commutes _ _,
  left_inv := λ f, by { ext, simp [lift_nc_alg_hom, lift_nc_ring_hom] },
  right_inv := λ F, by { ext, simp [lift_nc_alg_hom, lift_nc_ring_hom] } }

variables {k G A}

lemma lift_apply' (F : G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, (algebra_map k A b) * F a) := rfl

lemma lift_apply (F : G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, b • F a) :=
by simp only [lift_apply', algebra.smul_def]

lemma lift_def (F : G →* A) :
  ⇑(lift k G A F) = lift_nc ((algebra_map k A : k →+* A) : k →+ A) F :=
rfl

@[simp] lemma lift_symm_apply (F : monoid_algebra k G →ₐ[k] A) (x : G) :
  (lift k G A).symm F x = F (single x 1) := rfl

lemma lift_of (F : G →* A) (x) :
  lift k G A F (of k G x) = F x :=
by rw [of_apply, ← lift_symm_apply, equiv.symm_apply_apply]

@[simp] lemma lift_single (F : G →* A) (a b) :
  lift k G A F (single a b) = b • F a :=
by rw [lift_def, lift_nc_single, algebra.smul_def, ring_hom.coe_add_monoid_hom]

lemma lift_unique' (F : monoid_algebra k G →ₐ[k] A) :
  F = lift k G A ((F : monoid_algebra k G →* A).comp (of k G)) :=
((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `monoid_algebra k G` by
its values on `F (single a 1)`. -/
lemma lift_unique (F : monoid_algebra k G →ₐ[k] A) (f : monoid_algebra k G) :
  F f = f.sum (λ a b, b • F (single a 1)) :=
by conv_lhs { rw lift_unique' F, simp [lift_apply] }

/-- If `f : G → H` is a homomorphism between two magmas, then
`finsupp.map_domain f` is a non-unital algebra homomorphism between their magma algebras. -/
@[simps]
def map_domain_non_unital_alg_hom (k A : Type*) [comm_semiring k] [semiring A] [algebra k A]
  {G H F : Type*} [has_mul G] [has_mul H] [mul_hom_class F G H] (f : F) :
  monoid_algebra A G →ₙₐ[k] monoid_algebra A H :=
{ map_mul' := λ x y, map_domain_mul f x y,
  map_smul' := λ r x, map_domain_smul r x,
  ..(finsupp.map_domain.add_monoid_hom f : monoid_algebra A G →+ monoid_algebra A H) }

lemma map_domain_algebra_map (k A : Type*) {H F : Type*} [comm_semiring k] [semiring A]
  [algebra k A] [monoid H] [monoid_hom_class F G H] (f : F) (r : k) :
  map_domain f (algebra_map k (monoid_algebra A G) r) =
    algebra_map k (monoid_algebra A H) r :=
by simp only [coe_algebra_map, map_domain_single, map_one]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`finsupp.map_domain f` is an algebra homomorphism between their monoid algebras. -/
@[simps]
def map_domain_alg_hom (k A : Type*) [comm_semiring k] [semiring A] [algebra k A] {H F : Type*}
  [monoid H] [monoid_hom_class F G H] (f : F) :
  monoid_algebra A G →ₐ[k] monoid_algebra A H :=
{ commutes' := map_domain_algebra_map k A f,
  ..map_domain_ring_hom A f}

end lift

end monoid_algebra

/-! ### Additive monoids -/

namespace add_monoid_algebra

variables {k G}

end add_monoid_algebra

namespace add_monoid_algebra

variables {k G}

/-! #### Non-unital, non-associative algebra structure -/

section non_unital_non_assoc_algebra

variables (k) [semiring k] [distrib_smul R k] [has_add G]

variables {A : Type u₃} [non_unital_non_assoc_semiring A]

/-- A non_unital `k`-algebra homomorphism from `add_monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
lemma non_unital_alg_hom_ext [distrib_mul_action k A]
  {φ₁ φ₂ : add_monoid_algebra k G →ₙₐ[k] A}
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
@monoid_algebra.non_unital_alg_hom_ext k (multiplicative G) _ _ _ _ _ φ₁ φ₂ h

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma non_unital_alg_hom_ext' [distrib_mul_action k A]
  {φ₁ φ₂ : add_monoid_algebra k G →ₙₐ[k] A}
  (h : φ₁.to_mul_hom.comp (of_magma k G) = φ₂.to_mul_hom.comp (of_magma k G)) : φ₁ = φ₂ :=
@monoid_algebra.non_unital_alg_hom_ext' k (multiplicative G) _ _ _ _ _ φ₁ φ₂ h

/-- The functor `G ↦ add_monoid_algebra k G`, from the category of magmas to the category of
non-unital, non-associative algebras over `k` is adjoint to the forgetful functor in the other
direction. -/
@[simps] def lift_magma [module k A] [is_scalar_tower k A A] [smul_comm_class k A A] :
  (multiplicative G →ₙ* A) ≃ (add_monoid_algebra k G →ₙₐ[k] A) :=
{ to_fun := λ f, { to_fun := λ a, sum a (λ m t, t • f (multiplicative.of_add m)),
                   .. (monoid_algebra.lift_magma k f : _)},
  inv_fun := λ F, F.to_mul_hom.comp (of_magma k G),
  .. (monoid_algebra.lift_magma k : (multiplicative G →ₙ* A) ≃ (_ →ₙₐ[k] A)) }

end non_unital_non_assoc_algebra

/-! #### Algebra structure -/
section algebra

local attribute [reducible] add_monoid_algebra

/-- `finsupp.single 0` as a `alg_hom` -/
@[simps] def single_zero_alg_hom [comm_semiring R] [semiring k] [algebra R k] [add_monoid G] :
  k →ₐ[R] add_monoid_algebra k G :=
{ commutes' := λ r, by { ext, simp, }, ..single_zero_ring_hom}

end algebra

section lift

variables {k G} [comm_semiring k] [add_monoid G]
variables {A : Type u₃} [semiring A] [algebra k A] {B : Type*} [semiring B] [algebra k B]

/-- `lift_nc_ring_hom` as a `alg_hom`, for when `f` is an `alg_hom` -/
def lift_nc_alg_hom (f : A →ₐ[k] B) (g : multiplicative G →* B)
  (h_comm : ∀ x y, commute (f x) (g y)) :
  add_monoid_algebra A G →ₐ[k] B :=
{ to_fun := lift_nc_ring_hom (f : A →+* B) g h_comm,
  commutes' := by simp [lift_nc_ring_hom],
  ..(lift_nc_ring_hom (f : A →+* B) g h_comm)}

/-- A `k`-algebra homomorphism from `monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
lemma alg_hom_ext ⦃φ₁ φ₂ : add_monoid_algebra k G →ₐ[k] A⦄
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
@monoid_algebra.alg_hom_ext k (multiplicative G) _ _ _ _ _ _ _ h

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma alg_hom_ext' ⦃φ₁ φ₂ : add_monoid_algebra k G →ₐ[k] A⦄
  (h : (φ₁ : add_monoid_algebra k G →* A).comp (of k G) =
    (φ₂ : add_monoid_algebra k G →* A).comp (of k G)) : φ₁ = φ₂ :=
alg_hom_ext $ monoid_hom.congr_fun h

variables (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`monoid_algebra k G →ₐ[k] A`. -/
def lift : (multiplicative G →* A) ≃ (add_monoid_algebra k G →ₐ[k] A) :=
{ inv_fun := λ f, (f : add_monoid_algebra k G →* A).comp (of k G),
  to_fun := λ F,
  { to_fun := lift_nc_alg_hom (algebra.of_id k A) F $ λ _ _, algebra.commutes _ _,
    .. @monoid_algebra.lift k (multiplicative G) _ _ A _ _ F},
  .. @monoid_algebra.lift k (multiplicative G) _ _ A _ _ }

variables {k G A}

lemma lift_apply' (F : multiplicative G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, (algebra_map k A b) * F (multiplicative.of_add a)) := rfl

lemma lift_apply (F : multiplicative G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, b • F (multiplicative.of_add a)) :=
by simp only [lift_apply', algebra.smul_def]

lemma lift_def (F : multiplicative G →* A) :
  ⇑(lift k G A F) = lift_nc ((algebra_map k A : k →+* A) : k →+ A) F :=
rfl

@[simp] lemma lift_symm_apply (F : add_monoid_algebra k G →ₐ[k] A) (x : multiplicative G) :
  (lift k G A).symm F x = F (single x.to_add 1) := rfl

lemma lift_of (F : multiplicative G →* A) (x : multiplicative G) :
  lift k G A F (of k G x) = F x :=
by rw [of_apply, ← lift_symm_apply, equiv.symm_apply_apply]

@[simp] lemma lift_single (F : multiplicative G →* A) (a b) :
  lift k G A F (single a b) = b • F (multiplicative.of_add a) :=
by rw [lift_def, lift_nc_single, algebra.smul_def, ring_hom.coe_add_monoid_hom]

lemma lift_unique' (F : add_monoid_algebra k G →ₐ[k] A) :
  F = lift k G A ((F : add_monoid_algebra k G →* A).comp (of k G)) :=
((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `monoid_algebra k G` by
its values on `F (single a 1)`. -/
lemma lift_unique (F : add_monoid_algebra k G →ₐ[k] A) (f : monoid_algebra k G) :
  F f = f.sum (λ a b, b • F (single a 1)) :=
by conv_lhs { rw lift_unique' F, simp [lift_apply] }

lemma alg_hom_ext_iff {φ₁ φ₂ : add_monoid_algebra k G →ₐ[k] A} :
  (∀ x, φ₁ (finsupp.single x 1) = φ₂ (finsupp.single x 1)) ↔ φ₁ = φ₂ :=
⟨λ h, alg_hom_ext h, by rintro rfl _; refl⟩

end lift

/-- If `f : G → H` is a homomorphism between two additive magmas, then `finsupp.map_domain f` is a
non-unital algebra homomorphism between their additive magma algebras. -/
@[simps]
def map_domain_non_unital_alg_hom (k A : Type*) [comm_semiring k] [semiring A] [algebra k A]
  {G H F : Type*} [has_add G] [has_add H] [add_hom_class F G H] (f : F) :
  add_monoid_algebra A G →ₙₐ[k] add_monoid_algebra A H :=
{ map_mul' := λ x y, map_domain_mul f x y,
  map_smul' := λ r x, map_domain_smul r x,
  ..(finsupp.map_domain.add_monoid_hom f : monoid_algebra A G →+ monoid_algebra A H) }

/-- If `f : G → H` is an additive homomorphism between two additive monoids, then
`finsupp.map_domain f` is an algebra homomorphism between their add monoid algebras. -/
@[simps] def map_domain_alg_hom (k A : Type*) [comm_semiring k] [semiring A] [algebra k A]
  [add_monoid G] {H F : Type*} [add_monoid H] [add_monoid_hom_class F G H] (f : F) :
  add_monoid_algebra A G →ₐ[k] add_monoid_algebra A H :=
{ commutes' := map_domain_algebra_map f,
  ..map_domain_ring_hom A f}

end add_monoid_algebra

variables [comm_semiring R] (k G)

/-- The algebra equivalence between `add_monoid_algebra` and `monoid_algebra` in terms of
`multiplicative`. -/
def add_monoid_algebra.to_multiplicative_alg_equiv [semiring k] [algebra R k] [add_monoid G] :
  add_monoid_algebra k G ≃ₐ[R] monoid_algebra k (multiplicative G) :=
{ commutes' := λ r, by simp [add_monoid_algebra.to_multiplicative],
  ..add_monoid_algebra.to_multiplicative k G }

/-- The algebra equivalence between `monoid_algebra` and `add_monoid_algebra` in terms of
`additive`. -/
def monoid_algebra.to_additive_alg_equiv [semiring k] [algebra R k] [monoid G] :
  monoid_algebra k G ≃ₐ[R] add_monoid_algebra k (additive G) :=
{ commutes' := λ r, by simp [monoid_algebra.to_additive],
  ..monoid_algebra.to_additive k G }
