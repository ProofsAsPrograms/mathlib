/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.multiset.pi

/-!
# The cartesian product of lists
-/

namespace list
variables {ι : Type*} [dec : decidable_eq ι] {α : ι → Sort*}

namespace pi

/-- Given `α : ι → Sort*`, `pi.nil α` is the trivial dependent function out of the empty list. -/
def nil (α : ι → Sort*) : (Π i ∈ ([] : list ι), α i).

variables {i : ι} {l : list ι}

/-- Given `f` a function whose domain is `i :: l`, get its value at `i`.  -/
def head (f : Π j ∈ (i :: l), α j) : α i := f i (mem_cons_self _ _)

/-- Given `f` a function whose domain is `i :: l`, produce a function whose domain
is restricted to `l`.  -/
def tail (f : Π j ∈ (i :: l), α j) : Π j ∈ l, α j := λ j hj, f j (mem_cons_of_mem _ hj)

include dec

/-- Given `α : ι → Sort*`, a list `l` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `j` in `l`, `pi.cons a f` is a function `g` such
that `g k : α k` for all `k` in `i :: l`. -/
def cons (a : α i) (f : Π j ∈ l, α j) : Π j ∈ (i :: l), α j :=
@multiset.pi.cons _ _ _ _ ↑l a f

lemma cons_def (a : α i) (f : Π j ∈ l, α j) :
  cons a f = λ j hj, if h : j = i then h.symm.rec a else f j (hj.resolve_left h) :=
rfl

@[simp] lemma _root_.multiset.pi.cons_coe {l : list ι} (a : α i) (f : Π j ∈ l, α j) :
  @multiset.pi.cons _ _ _ _ (↑l) a f = cons a f := rfl

@[simp] lemma cons_eta (f : Π j ∈ (i :: l), α j) :
  cons (head f) (tail f) = f :=
multiset.pi.cons_eta f

lemma cons_map (a : α i) (f : Π j ∈ l, α j)
  {α' : ι → Sort*} (φ : ∀ ⦃j⦄, α j → α' j) :
  cons (φ a) (λ j hj, φ (f j hj)) = (λ j hj, φ ((cons a f) j hj)) :=
multiset.pi.cons_map _ _ _

lemma forall_rel_cons_ext (r : Π ⦃i⦄, α i → α i → Prop) {a₁ a₂ : α i} {f₁ f₂ : Π j ∈ l, α j}
  (ha : r a₁ a₂) (hf : ∀ (i : ι) (hi : i ∈ l), r (f₁ i hi) (f₂ i hi)) :
  ∀ j hj, r (cons a₁ f₁ j hj) (cons a₂ f₂ j hj) :=
@multiset.pi.forall_rel_cons_ext _ _ _ _ ↑l _ _ _ _ _ ha hf

end pi

include dec

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {α : ι → Type*} : Π l : list ι, (Π i, list (α i)) →
  list (Π i, i ∈ l → α i)
| []       fs := [λ x h, h.elim]
| (i :: l) fs := list.pi.cons <$> fs i <*> pi l fs

end list
