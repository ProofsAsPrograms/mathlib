/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext
import algebra.algebra.operations
import linear_algebra.multilinear.basic

/-!
# Tensor Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the tensor algebra of `M`.
This is the free `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `tensor_algebra R M` is the tensor algebra itself. It is endowed with an R-algebra structure.
2. `tensor_algebra.ι R` is the canonical R-linear map `M → tensor_algebra R M`.
3. Given a linear map `f : M → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `tensor_algebra R M → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : tensor_algebra R M → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.

## Implementation details

As noted above, the tensor algebra of `M` is constructed as the free `R`-algebra generated by `M`,
modulo the additional relations making the inclusion of `M` into an `R`-linear map.
-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [module R M]

namespace tensor_algebra

/--
An inductively defined relation on `pre R M` used to force the initial algebra structure on
the associated quotient.
-/
inductive rel : free_algebra R M → free_algebra R M → Prop
-- force `ι` to be linear
| add {a b : M} :
  rel (free_algebra.ι R (a+b)) (free_algebra.ι R a + free_algebra.ι R b)
| smul {r : R} {a : M} :
  rel (free_algebra.ι R (r • a)) (algebra_map R (free_algebra R M) r * free_algebra.ι R a)

end tensor_algebra

/--
The tensor algebra of the module `M` over the commutative semiring `R`.
-/
@[derive [inhabited, semiring, algebra R]]
def tensor_algebra := ring_quot (tensor_algebra.rel R M)

namespace tensor_algebra

instance {S : Type*} [comm_ring S] [module S M] : ring (tensor_algebra S M) :=
ring_quot.ring (rel S M)

variables {M}
/--
The canonical linear map `M →ₗ[R] tensor_algebra R M`.
-/
@[irreducible] def ι : M →ₗ[R] (tensor_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (free_algebra.ι R m)),
  map_add' := λ x y, by { rw [←alg_hom.map_add], exact ring_quot.mk_alg_hom_rel R rel.add, },
  map_smul' := λ r x, by { rw [←alg_hom.map_smul], exact ring_quot.mk_alg_hom_rel R rel.smul, } }

lemma ring_quot_mk_alg_hom_free_algebra_ι_eq_ι (m : M) :
  ring_quot.mk_alg_hom R (rel R M) (free_algebra.ι R m) = ι R m :=
by { rw [ι], refl }

/--
Given a linear map `f : M → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `tensor_algebra R M → A`.
-/
@[irreducible, simps symm_apply]
def lift {A : Type*} [semiring A] [algebra R A] : (M →ₗ[R] A) ≃ (tensor_algebra R M →ₐ[R] A) :=
{ to_fun := ring_quot.lift_alg_hom R ∘ λ f,
    ⟨free_algebra.lift R ⇑f, λ x y (h : rel R M x y), by induction h;
        simp only [algebra.smul_def, free_algebra.lift_ι_apply, linear_map.map_smulₛₗ,
          ring_hom.id_apply, map_mul, alg_hom.commutes, map_add]⟩,
  inv_fun := λ F, F.to_linear_map.comp (ι R),
  left_inv := λ f, begin
    rw [ι],
    ext1 x,
    exact (ring_quot.lift_alg_hom_mk_alg_hom_apply _ _ _ _).trans (free_algebra.lift_ι_apply f x),
  end,
  right_inv := λ F, ring_quot.ring_quot_ext' _ _ _ $ free_algebra.hom_ext $ funext $ λ x, begin
    rw [ι],
    exact (ring_quot.lift_alg_hom_mk_alg_hom_apply _ _ _ _).trans (free_algebra.lift_ι_apply _ _)
  end }

variables {R}

@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) :
  (lift R f).to_linear_map.comp (ι R) = f :=
by { convert (lift R).symm_apply_apply f, simp only [lift, equiv.coe_fn_symm_mk] }

@[simp]
theorem lift_ι_apply {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) (x) :
  lift R f (ι R x) = f x :=
by { conv_rhs { rw ← ι_comp_lift f}, refl }

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensor_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R f :=
by { rw ← (lift R).symm_apply_eq, simp only [lift, equiv.coe_fn_symm_mk] }

-- Marking `tensor_algebra` irreducible makes `ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.

@[simp]
theorem lift_comp_ι {A : Type*} [semiring A] [algebra R A] (g : tensor_algebra R M →ₐ[R] A) :
  lift R (g.to_linear_map.comp (ι R)) = g :=
by { rw ←lift_symm_apply, exact (lift R).apply_symm_apply g }

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : tensor_algebra R M →ₐ[R] A}
  (w : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
begin
  rw [←lift_symm_apply, ←lift_symm_apply] at w,
  exact (lift R).symm.injective w,
end

/-- If `C` holds for the `algebra_map` of `r : R` into `tensor_algebra R M`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `tensor_algebra R M`.
-/
-- This proof closely follows `free_algebra.induction`
@[elab_as_eliminator]
lemma induction {C : tensor_algebra R M → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (tensor_algebra R M) r))
  (h_grade1 : ∀ x, C (ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : tensor_algebra R M) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : subalgebra R (tensor_algebra R M) :=
  { carrier := C,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : M →ₗ[R] s := (ι R).cod_restrict s.to_submodule h_grade1,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (tensor_algebra R M) = s.val.comp (lift R of),
  { ext,
    simp [of], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift R of a),
  exact alg_hom.congr_fun of_id a,
end

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv : tensor_algebra R M →ₐ[R] R :=
lift R (0 : M →ₗ[R] R)

variables (M)

lemma algebra_map_left_inverse :
  function.left_inverse algebra_map_inv (algebra_map R $ tensor_algebra R M) :=
λ x, by simp [algebra_map_inv]

@[simp] lemma algebra_map_inj (x y : R) :
  algebra_map R (tensor_algebra R M) x = algebra_map R (tensor_algebra R M) y ↔ x = y :=
(algebra_map_left_inverse M).injective.eq_iff

@[simp] lemma algebra_map_eq_zero_iff (x : R) : algebra_map R (tensor_algebra R M) x = 0 ↔ x = 0 :=
map_eq_zero_iff (algebra_map _ _) (algebra_map_left_inverse _).injective

@[simp] lemma algebra_map_eq_one_iff (x : R) : algebra_map R (tensor_algebra R M) x = 1 ↔ x = 1 :=
map_eq_one_iff (algebra_map _ _) (algebra_map_left_inverse _).injective

variables {M}

/-- The canonical map from `tensor_algebra R M` into `triv_sq_zero_ext R M` that sends
`tensor_algebra.ι` to `triv_sq_zero_ext.inr`. -/
def to_triv_sq_zero_ext : tensor_algebra R M →ₐ[R] triv_sq_zero_ext R M :=
lift R (triv_sq_zero_ext.inr_hom R M)

@[simp] lemma to_triv_sq_zero_ext_ι (x : M) :
   to_triv_sq_zero_ext (ι R x) = triv_sq_zero_ext.inr x :=
lift_ι_apply _ _

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv : tensor_algebra R M →ₗ[R] M :=
(triv_sq_zero_ext.snd_hom R M).comp to_triv_sq_zero_ext.to_linear_map

lemma ι_left_inverse : function.left_inverse ι_inv (ι R : M → tensor_algebra R M) :=
λ x, by simp [ι_inv]

variables (R)

@[simp] lemma ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
ι_left_inverse.injective.eq_iff

@[simp] lemma ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 :=
by rw [←ι_inj R x 0, linear_map.map_zero]

variables {R}

@[simp] lemma ι_eq_algebra_map_iff (x : M) (r : R) : ι R x = algebra_map R _ r ↔ x = 0 ∧ r = 0 :=
begin
  refine ⟨λ h, _, _⟩,
  { have hf0 : to_triv_sq_zero_ext (ι R x) = (0, x), from lift_ι_apply _ _,
    rw [h, alg_hom.commutes] at hf0,
    have : r = 0 ∧ 0 = x := prod.ext_iff.1 hf0,
    exact this.symm.imp_left eq.symm, },
  { rintro ⟨rfl, rfl⟩,
    rw [linear_map.map_zero, ring_hom.map_zero] }
end

@[simp] lemma ι_ne_one [nontrivial R] (x : M) : ι R x ≠ 1 :=
begin
  rw [←(algebra_map R (tensor_algebra R M)).map_one, ne.def, ι_eq_algebra_map_iff],
  exact one_ne_zero ∘ and.right,
end

/-- The generators of the tensor algebra are disjoint from its scalars. -/
lemma ι_range_disjoint_one : disjoint (linear_map.range (ι R : M →ₗ[R] tensor_algebra R M))
  (1 : submodule R (tensor_algebra R M)) :=
begin
  rw submodule.disjoint_def,
  rintros _ ⟨x, hx⟩ ⟨r, (rfl : algebra_map _ _ _ = _)⟩,
  rw ι_eq_algebra_map_iff x at hx,
  rw [hx.2, ring_hom.map_zero]
end

variables (R M)

/-- Construct a product of `n` elements of the module within the tensor algebra.

See also `pi_tensor_product.tprod`. -/
def tprod (n : ℕ) : multilinear_map R (λ i : fin n, M) (tensor_algebra R M) :=
(multilinear_map.mk_pi_algebra_fin R n (tensor_algebra R M)).comp_linear_map $ λ _, ι R

@[simp] lemma tprod_apply {n : ℕ} (x : fin n → M) :
  tprod R M n x = (list.of_fn (λ i, ι R (x i))).prod := rfl

variables {R M}

end tensor_algebra

namespace free_algebra

variables {R M}

/-- The canonical image of the `free_algebra` in the `tensor_algebra`, which maps
`free_algebra.ι R x` to `tensor_algebra.ι R x`. -/
def to_tensor : free_algebra R M →ₐ[R] tensor_algebra R M :=
free_algebra.lift R (tensor_algebra.ι R)

@[simp] lemma to_tensor_ι (m : M) : (free_algebra.ι R m).to_tensor = tensor_algebra.ι R m :=
by simp [to_tensor]

end free_algebra
