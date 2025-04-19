import Mathlib
/-!
# Инструкция по выполнению ДЗ №4.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Могут оказаться полезными:
* Индуктивные типы, ключевое слово `match`.
* Тактика `induction`.

Не стесняйтесь задавать вопросы в чате!
-/
open Function

/-- Задача 1. `BinTree` это тип бинарных деревьев, на листьях которого написаны натуральные числа.
Ваша задача -- определить функцию `BinTree.sum` которая вычисляет сумму этих чисел. После этого проверьте
что "тесты" ниже могут быть доказаны с помощью `by rfl`.
-/
inductive BinTree
| leaf (val : ℕ)
| node (left : BinTree) (right : BinTree)

def BinTree.sum (tree : BinTree) : ℕ :=
  match tree with
  | BinTree.leaf v => v
  | BinTree.node left right => BinTree.sum left + BinTree.sum right

-- Тесты
example (v : ℕ) : BinTree.sum (BinTree.leaf v) = v := by rfl
example : BinTree.sum (BinTree.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = 10 := by rfl

/-- Задача 2. Определите предикат `BinTree.AllEven` означающий что все написанные на листьях числа четны.
Проверьте что "тесты" нижы могут быть доказаны через `by reduce; norm_num`. Затем докажите теорему ниже.

Примечание: чтобы это сработало выражайте факт "`n` - четное" как `n % 2 = 0`.

Примечание №2: `reduce` это тактика которая приводит все термы в цели к нормальной форме. В частности она
раскрывает определения и определяет по какой ветви `match` пойти.
-/

def IsEven (n : ℕ) := n % 2 = 0

def BinTree.AllEven (tree : BinTree) : Prop :=
  match tree with
  | BinTree.leaf n => IsEven n
  |BinTree.node left right => BinTree.AllEven left ∧ BinTree.AllEven right

-- Тесты
example : BinTree.AllEven (.leaf 3) = False := by reduce; norm_num
example : BinTree.AllEven (.leaf 2048) = True := by reduce; norm_num
example : BinTree.AllEven (.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = False := by reduce; norm_num
example : BinTree.AllEven (.node (.leaf 8) (.node (.node (.leaf 8) (.leaf 0)) (.leaf 4))) = True := by reduce; norm_num

-- Теорема
theorem EvenSum (tree : BinTree) (h_even : tree.AllEven) : tree.sum % 2 = 0 := by
  match tree with
  | BinTree.leaf n => exact h_even
  | BinTree.node left right =>
    have h_left : left.sum % 2 = 0 := by
      apply EvenSum
      exact h_even.left
    have h_right : right.sum % 2 = 0 := by
      apply EvenSum
      exact h_even.right

    calc
      (left.sum + right.sum) % 2 = (left.sum % 2 + right.sum) % 2 := by rw [← Nat.mod_add_mod]
      _ = (right.sum+left.sum % 2 ) % 2 := by rw [Nat.add_comm]
      _ = (right.sum% 2+left.sum % 2 ) % 2 := by rw [← Nat.mod_add_mod]
      _ = (0 + 0) % 2 := by rw [h_left, h_right]
/-- Задача 3: Существует счетная цепочка типов `Fₙ` такая что `Fₙ` можно инъективно и строго вложить
в `Fₙ₊₁`, и при этом `Fₙ₊₁ ≠ Fₙ`. -/
example : ∃ F : ℕ → Type, ∀ n, ∃ ι : F n → F (n + 1), Injective ι ∧ ι '' Set.univ ≠ Set.univ := by
  refine ⟨fun n => Fin (n + 1), ?_⟩
  intro n
  let ι : Fin (n + 1) → Fin (n + 2) :=
    Fin.castLE (Nat.le_succ _)
  have h_inj : Injective ι := Fin.castLE_injective _
  have h_not_surj :
      ι '' (Set.univ : Set (Fin (n + 1)))
        ≠ (Set.univ : Set (Fin (n + 2))) := by
    intro h_eq
    have h_mem_univ :
        (Fin.last (n + 1) : Fin (n + 2))
          ∈ (Set.univ : Set (Fin (n + 2))) := by
      simp
    have h_mem_img :
    (Fin.last (n + 1) : Fin (n + 2)) ∈
      (ι '' (Set.univ : Set (Fin (n + 1)))) := by
      simp [h_eq] at h_mem_univ
      rw [h_eq]
      exact h_mem_univ
    rcases h_mem_img with ⟨x, -, hx⟩
    have hx_val : (x : ℕ) = n + 1 := by
      simpa using congrArg Fin.val hx
    have hx_lt : (x : ℕ) < n + 1 := x.is_lt
    have : (n + 1) < n + 1 := by
      simp [hx_val] at hx_lt
    exact (Nat.lt_irrefl _ this).elim

  exact ⟨ι, h_inj, h_not_surj⟩
