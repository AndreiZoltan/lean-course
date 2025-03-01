import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics.Section02reals.Sheet5 -- import a bunch of previous stuff
open Section2sheet3 -- чтобы иметь определение `TendsTo`
open Section2sheet5
/-!
# Инструкция по выполнению ДЗ №2.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
На полный балл достаточно решить **любые 2 задачи**.
Могут оказаться полезными следующие тактики:
* `use` для подстановки значения в квантор `∃` в цели
* `obtain` для "распаковки" квантора `∃` в гипотезах
* `specialize` для подстановки значения в квантор `∀` в гипотезе

* `norm_num` для упрощения выражений содержащих нумералы
* `ring_nf`/`ring` для упрощения выражений в кольцах (и `ℝ` в частности)
* `linarith` для решения линейных уравнений/неравенств
* `simp` для упрощения выражений и раскрытия определений

* `exact?` для поиска в библиотеке подходящей леммы, которая бы закрыла цель при помощи `exact`.
* `rw?` для поиска леммы, которая бы упростила или закрыла цель при помощи тактики `rw`.

* `have` для введения вспомогательных гипотез в контекст

Пользуйтесь так же теоремами доказанными на лекции (они должны быть доступны благодаря `import` и `open` выше).

Не стесняйтесь спрашивать вопросы в чате!
-/


/-- Задача 1.
Комментарий: на самом деле условие `hc` не требуется. Можете попробовать его убрать доказать факт в общем случае.
-/
example (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) (c : ℝ) (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    simp [TendsTo] at *
    intros ε hε
    specialize h (ε / c) (div_pos hε hc)
    cases' h with N hN
    use N
    intro n hn
    calc
      _ =  |c * (a n - t)| := by ring_nf
      _ = |c| * |a n - t| := abs_mul c (a n - t)
      _ = c * |a n - t| := by rw [abs_of_pos hc]
      _ < ε := by exact (lt_div_iff₀' hc).mp (hN n hn)

/-- Задача 2.
`x ∣ y` означает "`x` делит `y`". Тактика `norm_num` умеет доказывать делимость для числовых выражений.
Подсказка: сократить доказательство поможет комбинатор `<;>`.
-/
example : ∀ (a b c : ℤ), ∃ m, (a = 1 ∨ a = 9) → (b = 3 ∨ b = 5) → (c = 42 ∨ c = 24) → m ∣ (a + b + c) := by
  intro a b c
  use 2
  rintro (rfl | rfl) (rfl | rfl) (rfl | rfl) <;> norm_num


/-- Задача 3 (сложная). -/
example (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  simp [TendsTo] at *
  have hst : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - s| < ε/2 ∧ |a n - t| < ε/2 := by
    intros ε hε
    specialize hs (ε/2) (by linarith)
    specialize ht (ε/2) (by linarith)
    obtain ⟨Ns, hNs⟩ := hs
    obtain ⟨Nt, hNt⟩ := ht
    use max Ns Nt
    intro n hn
    constructor
    exact (hNs n (le_of_max_le_left hn))
    exact (hNt n (le_of_max_le_right hn))
  have hst' : ∀ ε > 0, |s - t| < ε := by
    intros ε hε
    specialize hst ε hε
    obtain ⟨N, hN⟩ := hst
    specialize hN N (le_refl N)
    calc
      |s - t| = |(s - a N) + (a N - t)| := by ring_nf
      _ ≤ |s - a N| + |a N - t| := abs_add _ _
      _ = |- (a N - s)| + |a N - t| := by ring_nf
      _ = |a N - s| + |a N - t| := by rw [abs_neg]
      _ < ε := by linarith
  by_contra h
  have h1: |s - t| > 0 := by exact abs_sub_pos.mpr h
  specialize hst' (|s - t| / 2) (by linarith)
  linarith
