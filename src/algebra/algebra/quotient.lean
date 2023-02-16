import algebra.algebra.subalgebra.basic

namespace algebra

universes u v

variables (R : Type u) (A : Type v) [comm_semiring R] [comm_ring A] [algebra R A]

namespace double_quot

variables (I J : ideal A)

/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
def quot_left_to_quot_sup : A ⧸ I →ₐ[R] A ⧸ (I ⊔ J) :=
alg_hom.mk (double_quot.quot_left_to_quot_sup I J) rfl (map_mul _) rfl (map_add _) (λ _, rfl)

/-- The kernel of `quot_left_to_quot_sup` -/
@[simp]
lemma ker_quot_left_to_quot_sup :
  ring_hom.ker (quot_left_to_quot_sup R A I J) = J.map (I^.quotient.mkₐ R) :=
double_quot.ker_quot_left_to_quot_sup I J

/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J) induced by `quot_left_to_quot_sup`,
  where `J'` is the projection of `J` in `A / I`. -/
def quot_quot_to_quot_sup : (A ⧸ I) ⧸ J.map (I^.quotient.mkₐ R) →ₐ[R] A ⧸ I ⊔ J :=
alg_hom.mk (double_quot.quot_quot_to_quot_sup I J) rfl (map_mul _) rfl (map_add _) (λ _, rfl)

/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
def quot_quot_mk : A →ₐ[R] ((A ⧸ I) ⧸ J.map (I^.quotient.mkₐ R)) :=
alg_hom.mk (double_quot.quot_quot_mk I J) rfl (map_mul _) rfl (map_add _) (λ _, rfl)

/-- The kernel of `quot_quot_mk`. -/
@[simp]
lemma ker_quot_quot_mk : ring_hom.ker (quot_quot_mk R A I J) = I ⊔ J :=
double_quot.ker_quot_quot_mk I J

/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'`induced by `quot_quot_mk`,
  where `J'` is the projection `J` in `A / I`. -/
def lift_sup_quot_quot_mk (I J : ideal A) :
  A ⧸ (I ⊔ J) →ₐ[R] (A ⧸ I) ⧸ J.map (I^.quotient.mkₐ R) :=
alg_hom.mk (double_quot.lift_sup_quot_quot_mk I J) rfl (map_mul _) rfl (map_add _) (λ _, rfl)

/-- `quot_quot_to_quot_add` and `lift_sup_quot_quot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`). -/
def quot_quot_equiv_quot_sup : ((A ⧸ I) ⧸ J.map (I^.quotient.mkₐ R)) ≃ₐ[R] A ⧸ I ⊔ J :=
@alg_equiv.of_ring_equiv R _ _ _ _ _ _ _ (double_quot.quot_quot_equiv_quot_sup I J) (λ _, rfl)

@[simp]
lemma quot_quot_equiv_quot_sup_quot_quot_mk (x : A) :
  quot_quot_equiv_quot_sup R A I J (quot_quot_mk R A I J x) = (I ⊔ J)^.quotient.mkₐ R x :=
rfl

@[simp]
lemma quot_quot_equiv_quot_sup_symm_quot_quot_mk (x : A) :
  (quot_quot_equiv_quot_sup R A I J).symm ((I ⊔ J)^.quotient.mkₐ R x) =
    quot_quot_mk R A I J x :=
rfl

/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
def quot_quot_equiv_comm :
  ((A ⧸ I) ⧸ J.map (I^.quotient.mkₐ R)) ≃ₐ[R]
    ((A ⧸ J) ⧸ I.map (J^.quotient.mkₐ R)) :=
@alg_equiv.of_ring_equiv R _ _ _ _ _ _ _ (double_quot.quot_quot_equiv_comm I J) (λ _, rfl)

@[simp]
lemma quot_quot_equiv_comm_quot_quot_mk (x : A) :
  quot_quot_equiv_comm R A I J (quot_quot_mk R A I J x) = quot_quot_mk R A J I x :=
rfl

@[simp]
lemma quot_quot_equiv_comm_comp_quot_quot_mk :
  alg_hom.comp ↑(quot_quot_equiv_comm R A I J) (quot_quot_mk R A I J) = quot_quot_mk R A J I :=
alg_hom.ext $ quot_quot_equiv_comm_quot_quot_mk R A I J

-- @[simp]
-- lemma quot_quot_equiv_comm_symm :
--   (quot_quot_equiv_comm R I J).symm = quot_quot_equiv_comm R J I :=
-- begin convert rfl end

variables {I J}

/-- The **Third Isomorphism Theorem** for rings. See `quot_quot_equiv_quot_sup` for a version
    that does not assume an inclusion of ideals. -/
def quot_quot_equiv_quot_of_le (h : I ≤ J) :
  ((A ⧸ I) ⧸ (J.map (I^.quotient.mkₐ R))) ≃ₐ[R] A ⧸ J :=
@alg_equiv.of_ring_equiv R _ _ _ _ _ _ _ (double_quot.quot_quot_equiv_quot_of_le h) (λ _, rfl)

@[simp]
lemma quot_quot_equiv_quot_of_le_quot_quot_mk (x : A) (h : I ≤ J) :
  quot_quot_equiv_quot_of_le R A h (quot_quot_mk R A I J x) = J^.quotient.mkₐ R x := rfl

@[simp]
lemma quot_quot_equiv_quot_of_le_symm_mk (x : A) (h : I ≤ J) :
  (quot_quot_equiv_quot_of_le R A h).symm (J^.quotient.mkₐ R x) =
    (quot_quot_mk R A I J x) := rfl

@[simp]
lemma quot_quot_equiv_quot_of_le_comp_quot_quot_mk (h : I ≤ J) :
  alg_hom.comp ↑(quot_quot_equiv_quot_of_le R A h) (quot_quot_mk R A I J) =
    J^.quotient.mkₐ R :=
rfl

@[simp]
lemma quot_quot_equiv_quot_of_le_symm_comp_mk (h : I ≤ J) :
  alg_hom.comp ↑(quot_quot_equiv_quot_of_le R A h).symm (J^.quotient.mkₐ R) =
    quot_quot_mk R A I J :=
rfl

end double_quot

end algebra
