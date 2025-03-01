/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simp [TendsTo] at *
  peel ha with X hX n hn m hm
  calc
    _ = |- (a hn - t)| := by ring_nf
    _ = |a hn - t| := by rw [abs_neg]
  assumption



/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  simp [TendsTo] at *
  -- rw [tendsTo_def] at *
  -- let ε > 0 be arbitrary
  intro ε hε
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε / 2) (by linarith)

  cases' ha with X hX
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  -- specialize hb (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  --  use max(X,Y),
  use max X Y
  -- now say n ≥ max(X,Y)
  intro n hn
  simp at hn
  -- rw [Nat.max_le] at hn
  specialize hX n hn.left
  specialize hY n hn.right
  --  Then easy.
  rw [abs_lt] at *
  constructor <;> linarith -- `<;>` means "do next tactic to all goals produced by this tactic"

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  simp [TendsTo] at *
  intro ε hε
  specialize ha (ε/2) (by linarith)
  specialize hb (ε/2) (by linarith)
  obtain ⟨X, hX⟩ := ha
  obtain ⟨Y, hY⟩ := hb
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  rw [abs_lt] at *
  constructor <;> linarith

end Section2sheet5
