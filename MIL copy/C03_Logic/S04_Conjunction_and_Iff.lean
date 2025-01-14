import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor --finds a suffices contructor and creates subgoals
  · assumption --goal one comes from h₀
  intro h --not need x≠y, start by h:x=y
  apply h₁ --need False, apply h1 to get false from y ≤ x
  rw [h] --rw into y≤y and solves by reflexivity

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩ --anon constructor of and

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁ --now need ¬h (x=y)→ ¬ h1 ( ¬ ¬ y ≤ x = y ≤ x)
    rw [h₁] --refl of ≤
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁ --now need ¬ ¬ y ≤ x → x = y ( y ≤ x →  x=y)
  exact le_antisymm h₀ h₁ --combined x≤y and y≤x to get x=y

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h' --via x ≤ y and y ≤ x (to get false) get x = y ( goal is false)
  exact h₁ (le_antisymm h₀ h') -- use x ≠ y = ¬ (x = y) on (x=y)

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

#check Nat.div_left_inj

#check Nat.eq_of_mul_eq_mul_left
#check Nat.mul_one
#check Nat.dvd_antisymm

--tactic proof
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
 constructor
 . exact h.1
 . intro ndm
   exact h.2 (dvd_antisymm h.1 ndm)

--term proof
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
suffices hnndm: ¬n ∣ m from And.intro h.1 hnndm
fun ndm => h.2 (dvd_antisymm h.1 ndm)

/-
You can nest uses of ∃ and ∧ with anonymous constructors, rintro, and rcases.
-/

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩ --allows nesting i.e equal to ⟨ _, ⟨ _, _ ⟩ ⟩ . First is exists, then next is the And



example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩ --since its after the :, allows implicit deconstruction of first argument
  exact lt_trans xltz zlty --uses transitivity via z

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty --implicit deconstruction, term proof

/-
You can also use the use tactic:
-/

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num --applies norm_num to each goal

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

--my one
example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  repeat constructor <;> norm_num



example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')


/-
Iff section
-/

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor --uses a suffices to get mp and mpr goals
  · contrapose! -- x = y → y ≤ x
    rintro rfl -- creates x = y
    rfl --reflexivity of ≤ means x=y →y ≤ x
  contrapose! -- y≤x → x = y
  exact le_antisymm h --get x=y via antisym h and y≤x → x=y

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦  h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

--term proof
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  ⟨fun ⟨hxley,hnylex⟩ ↦ ⟨hxley,fun hxeqy ↦ by rw [hxeqy] at hnylex;exact hnylex (le_refl y)⟩, fun ⟨hxley,hnxeqy⟩ ↦ ⟨hxley, fun hylex ↦ hnxeqy (le_antisymm hxley hylex) ⟩⟩


--tactic proof
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  . intro ⟨hxley,hnylex⟩
    constructor
    . exact hxley
    . intro hxeqy
      rw [hxeqy] at hnylex
      exact hnylex (le_refl y)
  . intro ⟨hxley,hnxeqy⟩
    constructor
    . exact hxley
    . intro hylex
      exact hnxeqy (le_antisymm hxley hylex)




#check pow_two_nonneg
#check pow_eq_zero
#check lt_of_le_of_ne
#check ne_comm.mp
#check add_pos_of_nonneg_of_pos

--tactic-term proof (no term proof for this one, too long)
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
   by_contra! h'
   have: x^2 > 0 := lt_of_le_of_ne (pow_two_nonneg x) (ne_comm.mp h')
   have: y^2 + x^2 > 0 := (add_pos_of_nonneg_of_pos (pow_two_nonneg y) this)
   linarith
  pow_eq_zero h'

#check zero_pow
#check not_and.mp
--term-tactic proof
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
 constructor
 . intro heq0
   constructor
   . exact aux heq0
   . rw [add_comm] at heq0
     exact aux heq0
 . rintro ⟨xeq0,yeq0⟩
   rw [xeq0,yeq0]
   rw [zero_pow (by linarith)]
   rw [zero_add]

section


--using propext here to rw iff as equality

#check abs_lt --  |a| < b ↔ -b < a ∧ a < b
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith


#check Nat.dvd_gcd_iff -- k ∣ m.gcd n ↔ k ∣ m ∧ k ∣ n

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num -- gets 3|6 and 3|15 via norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl


#check Monotone
#print Monotone -- → (α → β) → Prop := fun {α} {β} [Preorder α] [Preorder β] f => ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

#check neg_le_neg
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  push_neg
  use 2
  use 3
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

#check lt_iff_le_not_le --a < b ↔ a ≤ b ∧ ¬b ≤ a
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le] --rewrutes a < b with a ≤ b ∧ ¬b ≤ a to make goal a ≤ b ∧ ¬b ≤ a ↔  a ≤ b ∧ a ≠ b
  constructor
  . rintro ⟨h,h1⟩
    constructor
    . exact h
    . by_contra h'
      rw [h'] at h1
      exact h1 (le_refl b)
  . rintro ⟨h2,h3⟩
    constructor
    . exact h2
    . by_contra h'
      exact h3 (le_antisymm h2 h')

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

#check lt_iff_le_not_le --a < b ↔ a ≤ b ∧ ¬b ≤ a
example : ¬a < a := by
  rw [lt_iff_le_not_le] --rewrites goal into ¬ (a ≤ b ∧ ¬b ≤ a)
  push_neg
  intro h
  exact h

#check le_trans --a ≤ b → b ≤ c → a ≤ c
example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  intro a1 a2
  constructor
  . exact le_trans a1.1 a2.1
  . by_contra h'
    have: c ≤ b := le_trans h' a1.1
    exact a2.2 this

end
