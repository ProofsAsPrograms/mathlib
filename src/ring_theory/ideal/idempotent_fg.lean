/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import algebra.ring.idempotents
import ring_theory.finiteness

/-!
## Lemmas on idempotent finitely generated ideals
-/

namespace ideal

/-- A finitely generated idempotent ideal is generated by an idempotent element -/
lemma is_idempotent_elem_iff_of_fg {R : Type*} [comm_ring R] (I : ideal R)
  (h : I.fg) :
  is_idempotent_elem I ↔ ∃ e : R, is_idempotent_elem e ∧ I = R ∙ e :=
begin
  split,
  { intro e,
    obtain ⟨r, hr, hr'⟩ := submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
      (by { rw [smul_eq_mul], exact e.ge }),
    simp_rw smul_eq_mul at hr',
    refine ⟨r, hr' r hr, antisymm _ ((submodule.span_singleton_le_iff_mem _ _).mpr hr)⟩,
    intros x hx,
    rw ← hr' x hx,
    exact ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩ },
  { rintros ⟨e, he, rfl⟩,
    simp [is_idempotent_elem, ideal.span_singleton_mul_span_singleton, he.eq] }
end

lemma is_idempotent_elem_iff_eq_bot_or_top {R : Type*} [comm_ring R] [is_domain R]
  (I : ideal R) (h : I.fg) :
  is_idempotent_elem I ↔ I = ⊥ ∨ I = ⊤ :=
begin
  split,
  { intro H,
    obtain ⟨e, he, rfl⟩ := (I.is_idempotent_elem_iff_of_fg h).mp H,
    simp only [ideal.submodule_span_eq, ideal.span_singleton_eq_bot],
    apply or_of_or_of_imp_of_imp (is_idempotent_elem.iff_eq_zero_or_one.mp he) id,
    rintro rfl,
    simp },
  { rintro (rfl|rfl); simp [is_idempotent_elem] }
end

end ideal