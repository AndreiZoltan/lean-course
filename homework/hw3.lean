import Mathlib
/-!
# Инструкция по выполнению ДЗ №3.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
На полный балл достаточно решить **любые 2 задачи**.

Могут оказаться полезными:
* Тактика `ext` для для применения правил экстенсиональности (для множеств, функций, ...)
* Тактика `unfold` для распаковки определений
* Если цель имеет вид `A ⊆ B` можно сразу использовать `intro x hx` где `hx : x ∈ A` и переходить к цели `x ∈ B`
* Точно так же если есть гипотеза `h : A ⊆ B` то можно использовать ее для `apply`: к примеру если `h_mem : x ∈ A`
  то `apply h at h_mem` заменит ее на `h_mem : x ∈ B`.
* Если Вам нужен некоторый вспомогательный факт `Some_New_Fact` и вы чувствуете что он
  должен выводиться из текущего контекста при помощи лемм из библиотеки можно использовать
  синтаксис `have h_new : Some_New_Fact := by exact?`
* `rw [← h]` для переписывания цели/гипотезы при помощи `h` используя `h` в обратном направлении (справа налево)
* `simp` для упрощения выражений.

## Небольшая справка о `simp`
`simp` работает как `rw`, но кроме переданных ему лемм (которых вообще может не быть) он использует леммы
вида `A = B` или `A ↔ B` из библиотеки помеченные аттрибутом `@[simp]`. Если какое-то подвыражение текущей цели
совпадает с левой частью в лемме, то она заменяется на правую часть. Цель тактики `simp` -- привести
выражение к "нормальной форме" насколько это возможно. Например есть `simp`-леммы
в которых доказано `|1| = 1`, `p ∧ True ↔ p`, `List.length List.nil = 0`, `x ∈ {y | P y} ↔ P x` и т.п.
Применяя `simp` к выражениям содержащим левые части этих лемм, мы упрощаем эти выражения и с ними становится
легче работать.

Подробнее можно прочитать в секциях Rewriting и Using the Simplifier здесь:
https://leanprover.github.io/theorem_proving_in_lean4/tactics.html

Не стесняйтесь задавать вопросы в чате!
-/

/-- Задача 1.

Комментарий: эта задача решается в одну строчку тактикой `tauto_set`.
Вам нужно справиться без нее, хотя тактика `tauto` не заперещена.
-/
example {X : Type} (A B C : Set X) (h : A ∪ B ⊆ C) : Cᶜ ⊆ Aᶜ ∩ Bᶜ := by
  intro x hx
  by_contra hc
  change ¬ (x ∈ C) at hx
  rw [← Set.compl_union] at hc
  rw [← Set.compl_subset_compl] at h
  exact hc (h hx)

/-- Задача 2. -/
example : ∃ f : ℕ → ℕ × ℕ, f '' {n | Even n} = {(n, m) | n = m} := by
  let f : ℕ → ℕ × ℕ := λ n ↦ (n / 2, n / 2)
  use f
  ext ⟨a, b⟩
  constructor
  simp [Prod.ext_iff]
  intro n hn ha hb
  rw [← ha, ← hb]
  intro hab
  rw [hab]
  use 2 * b
  constructor
  unfold Even
  use b
  ring
  simp [f]


def IsLinear (f : ℚ → ℚ) : Prop := ∃ c, ∀ x, f x = c * x

/-- Задача 3. -/
example : {f : ℚ → ℚ | IsLinear f ∧ ∀ x, |f x| = |x|} = {id, -id} := by
  unfold IsLinear
  ext f
  constructor
  · intro h
    simp at h ⊢
    cases' h with hl ha
    rcases hl with ⟨c, hc⟩
    have hc_norm : |c| = 1 := by
      specialize ha 1
      simp [hc] at ha
      exact ha
    have hc' : c = 1 ∨ c = -1 := by
      exact abs_eq_abs.mp hc_norm
    cases' hc' with cpos cneg
    · left
      ext x
      rw [hc, cpos]
      norm_num
    · right
      ext x
      rw [hc, cneg]
      norm_num
  · simp
    intro h
    constructor
    · rcases h with (rfl | rfl)
      use 1; simp
      use -1; simp
    · intro x
      rcases h with (rfl | rfl) <;> simp
