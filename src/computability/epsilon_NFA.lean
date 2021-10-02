/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import computability.NFA

/-!
# Epsilon Nondeterministic Finite Automata
This file contains the definition of an epsilon Nondeterministic Finite Automaton (`ε_NFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitons,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `fintype` instance must be
supplied for true `ε_NFA`'s.
-/

open set

universes u v

/-- An `ε_NFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states and can make ε-transitions by
  inputing `none`.
  Since this definition allows for Automata with infinite states, a `fintype` instance must be
  supplied for true `ε_NFA`'s.-/
structure ε_NFA (α : Type u) (σ : Type v) :=
(step : σ → option α → set σ)
(start : set σ)
(accept : set σ)

variables {α : Type u} {σ σ' : Type v} (M : ε_NFA α σ)

namespace ε_NFA

/-- The `ε_closure` of a set is the set of states which can be reached by taking a finite string of
  ε-transitions from an element of the set -/
inductive ε_closure : set σ → set σ
| base : ∀ S (s ∈ S), ε_closure S s
| step : ∀ S s (t ∈ M.step s none), ε_closure S s → ε_closure S t

/-- `M.step_set S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
def step_set : set σ → α → set σ :=
λ S a, S >>= (λ s, M.ε_closure (M.step s a))

/-- `M.eval_from S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
def eval_from (start : set σ) : list α → set σ :=
list.foldl M.step_set (M.ε_closure start)

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
  `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts : language α :=
λ x, ∃ S ∈ M.accept, S ∈ M.eval x

/-! ### Regex-like operations -/

variables (α σ)

protected def zero : ε_NFA α σ :=
ε_NFA.mk (λ _ _, ∅) ∅ ∅

instance : has_zero (ε_NFA α σ) := ⟨ε_NFA.zero α σ⟩

protected def one : ε_NFA α σ :=
{ step := λ _ _, univ,
  start := univ,
  accept := univ }

instance : has_one (ε_NFA α σ) := ⟨ε_NFA.one α σ⟩

variables {α σ} (P : ε_NFA α σ) (Q : ε_NFA α σ')

def char [decidable_eq α] (a : α) : ε_NFA α (option unit) :=
{ step := λ s b, if (a ∈ b ∧ s = none) then {some ()} else ∅,
    start := set.univ,
    accept := set.univ }

def add : ε_NFA α (σ × σ') :=
{ step := λ s a, (P.step s.1 a).prod (Q.step s.2 a),
  start := P.start.prod Q.start,
  accept := {ab | ab.1 ∈ P.accept ∨ ab.2 ∈ Q.accept} }

protected def mul : ε_NFA α (σ × σ') :=
{ step := λ s a, (P.step s.1 a).prod (Q.step s.2 a),
  start := P.start.prod Q.start,
  accept := P.accept.prod Q.accept }


def star [Π s, decidable (s ∈ P.accept)] : ε_NFA α (option σ) :=
{ step := λ s a, match s with
    | none := match a with
      | none := coe '' P.start
      | (some a) := ∅
      end
    | (some s) :=  match a with
      | none := (coe '' P.step s none) ∪ (if (s ∈ P.accept) then {none} else ∅)
      | (some a) := coe '' P.step s a
      end
    end,
  start := {none},
  accept := {none} }

lemma accept_zero : (0 : ε_NFA α σ).accept = ∅ := rfl

lemma accepts_zero : (0 : ε_NFA α σ).accepts = 0 :=
begin
  ext,
  refine iff_of_false _ (language.not_mem_zero _),
  rintro ⟨s, h, _⟩,
  exact set.not_mem_empty _ h,
end

lemma accepts_one : (1 : ε_NFA α σ).accepts = 1 :=
begin
  ext,
  rw language.mem_one,
  split,
  {
    rintro ⟨s, h, hs⟩,
    sorry,
  },
  rintro rfl,
  sorry
end

lemma accepts_add : (P.add Q).accepts = P.accepts + Q.accepts :=
begin
  ext,
  rw language.mem_add,
end

lemma accepts_mul : (P.mul Q).accepts = P.accepts * Q.accepts :=
begin
  ext,
  rw language.mem_mul,
end

lemma accepts_star [Π s, decidable (s ∈ P.accept)] : P.star.accepts = P.accepts.star :=
begin
  ext,
  rw language.mem_star,
end

/-! ### Conversions between `ε_NFA` and `NFA` -/

/-- `M.to_NFA` is an `NFA` constructed from an `ε_NFA` `M`. -/
def to_NFA : NFA α σ :=
{ step := λ S a, M.ε_closure (M.step S a),
  start := M.ε_closure M.start,
  accept := M.accept }

@[simp] lemma to_NFA_eval_from_match (start : set σ) :
  M.to_NFA.eval_from (M.ε_closure start) = M.eval_from start := rfl

@[simp] lemma to_NFA_correct :
  M.to_NFA.accepts = M.accepts :=
begin
  ext x,
  rw [accepts, NFA.accepts, eval, NFA.eval, ←to_NFA_eval_from_match],
  refl
end

lemma pumping_lemma [fintype σ] {x : list α} (hx : x ∈ M.accepts)
  (hlen : fintype.card (set σ) + 1 ≤ list.length x) :
  ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ fintype.card (set σ) + 1 ∧ b ≠ [] ∧
  {a} * language.star {b} * {c} ≤ M.accepts :=
begin
  rw ←to_NFA_correct at hx ⊢,
  exact M.to_NFA.pumping_lemma hx hlen
end

end ε_NFA

namespace NFA

/-- `M.to_ε_NFA` is an `ε_NFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
def to_ε_NFA (M : NFA α σ) : ε_NFA α σ :=
{ step := λ s a, a.cases_on' ∅ (λ a, M.step s a),
  start := M.start,
  accept := M.accept }

@[simp] lemma to_ε_NFA_ε_closure (M : NFA α σ) (S : set σ) : M.to_ε_NFA.ε_closure S = S :=
begin
  ext a,
  split,
  { rintro ( ⟨ _, _, h ⟩ | ⟨ _, _, _, h, _ ⟩ ),
    exact h,
    cases h },
  { intro h,
    apply ε_NFA.ε_closure.base,
    exact h }
end

@[simp] lemma to_ε_NFA_eval_from_match (M : NFA α σ) (start : set σ) :
  M.to_ε_NFA.eval_from start = M.eval_from start :=
begin
  rw [eval_from, ε_NFA.eval_from, step_set, ε_NFA.step_set, to_ε_NFA_ε_closure],
  congr,
  ext S s,
  simp only [exists_prop, set.mem_Union, set.bind_def],
  apply exists_congr,
  simp only [and.congr_right_iff],
  intros t ht,
  rw M.to_ε_NFA_ε_closure,
  refl
end

@[simp] lemma to_ε_NFA_correct (M : NFA α σ) :
  M.to_ε_NFA.accepts = M.accepts :=
begin
  rw [accepts, ε_NFA.accepts, eval, ε_NFA.eval, to_ε_NFA_eval_from_match],
  refl
end

end NFA
