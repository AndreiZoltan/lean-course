/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext a
  constructor
  rintro (hA|hA) <;> exact hA
  intro hA
  left
  exact hA

example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := by
  ext n
  apply h

-- #check propext

example : A ∩ A = A :=
  inter_self A

example : A ∩ ∅ = ∅ := by
  ext n
  constructor
  · rintro ⟨a1, a2⟩
    exact a2
  · intro a
    exact False.elim a


example : A ∪ univ = univ := by
  exact union_univ A

example : A ⊆ B → B ⊆ A → A = B := by
  intro a b
  exact Subset.antisymm a b

example : A ∩ B = B ∩ A := by
  exact inter_comm A B

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  exact Eq.symm (inter_assoc A B C)

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  exact Eq.symm (union_assoc A B C)

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  exact union_inter_distrib_left A B C

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_union_distrib_left A B C
