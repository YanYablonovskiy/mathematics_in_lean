import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs


#check abs_pos
#check abs_of_nonneg
#check abs_of_neg
#check abs_neg
#check abs_add_le
#check lt_or_ge --a < b ∨ a ≥ b

--tactic proof
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases lt_or_ge x 0 with h|h
  . have: |x| = -x := abs_of_neg h
    rw [this]
    linarith
  . have: |x| = x := abs_of_nonneg h
    rw [this]


#check Eq.subst
#check neg_le_self

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases lt_or_ge x 0 with h|h
  . have: |x| = -x := abs_of_neg h
    rw [this]
  . have h1:|x| = x := abs_of_nonneg h
    have: -x ≤ x := neg_le_self h
    nth_rewrite 2 [←h1] at this
    exact this

#check neg_one_mul
#check mul_add
#check le_add_left --(h : a ≤ c) : a ≤ b + c

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases lt_or_ge (x+y) 0 with h|h
  . have h1:|x+y| = -x+-y :=
      calc |x+y| = -(x+y) := abs_of_neg h
      _ = -1*(x+y) := by rw [←neg_one_mul]
      _ = -1*x + -1*y := by rw [mul_add]
      _ = -x + -y := by rw [neg_one_mul,neg_one_mul]
    rw [h1]
    have h2: -x ≤ |x| := neg_le_abs_self x
    have h3: -y ≤ |y| := neg_le_abs_self y
    linarith
  . have h4:|x+y|= x + y := abs_of_nonneg h
    have h5: x ≤ |x| := le_abs_self x
    have h6: y ≤ |y| := le_abs_self y
    linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . rcases lt_or_ge y 0 with h|h
    . rw [abs_of_neg h]
      intro h
      apply Or.inr
      exact h
    . rw [abs_of_nonneg h]
      intro h1
      apply Or.inl
      exact h1
  . rintro h
    rcases h with h|h
    . rcases lt_or_ge y 0 with g|g
      . rw [abs_of_neg g]; linarith
      . rw [abs_of_nonneg g]; exact h
    . rcases lt_or_ge y 0 with g|g
      . rw [abs_of_neg g]; exact h
      . rw [abs_of_nonneg g]; linarith

#check neg_lt

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . rcases lt_or_ge x 0 with h|h
    . rw [abs_of_neg h]
      by_contra! h'
      rcases h' with ⟨a1,a2⟩
      have: y≤x := a2 (neg_lt.mp a1)
      linarith
    . rw [abs_of_nonneg h]
      intro h1
      constructor
      . linarith
      . exact h1
  . by_contra! h''
    rcases h'' with ⟨h1,h2⟩
    rcases h1 with ⟨h3,h4⟩
    rcases lt_or_ge x 0 with h|h
    . rw [abs_of_neg h] at h2;
      linarith
    . rw [abs_of_nonneg h] at h2;linarith


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x,hzx⟩;rcases hzx with ⟨y,hyz⟩;rcases hyz with h|h<;>have h1: x^2 ≥ 0 := pow_two_nonneg x<;>have h2: y^2 ≥ 0 := pow_two_nonneg y<;>linarith


#check eq_zero_or_eq_zero_of_mul_eq_zero
#check eq_one_of_mul_left
#check pow_two
#check lt_mul_of_lt_one_left
#check lt_mul_left
#check eq_one_iff_eq_one_of_mul_eq_one
#check lt_or_eq_of_le
#check mul_self_eq_one_iff.mp
#check mul_one
--not what they wanted
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
 rw [pow_two] at h
 exact mul_self_eq_one_iff.mp h

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
 have: x^2 - 1^2 = 0 := by rw [h];rw [pow_two,mul_one]; exact sub_self 1
 have: (x+1)*(x-1) = 0 := by rw [sq_sub_sq] at this;exact this
 have: (x+1)=0 ∨ (x-1)=0 := by exact eq_zero_or_eq_zero_of_mul_eq_zero this
 rcases this with hxpy0|hxsy0
 . apply Or.inr
   exact eq_neg_of_add_eq_zero_left hxpy0
 . apply Or.inl
   exact eq_of_sub_eq_zero hxsy0

#check sq_sub_sq

#check eq_zero_or_eq_zero_of_mul_eq_zero
#check eq_neg_of_add_eq_zero_left
#check eq_of_sub_eq_zero



example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have: x ^ 2 - y ^ 2 = 0 := by rw [h]; exact sub_self (y^2)
  have: (x+y)*(x-y) = 0 := by rw [sq_sub_sq] at this;exact this
  have: (x+y)=0 ∨ (x-y)=0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with hxpy0|hxsy0
  . apply Or.inr
    exact eq_neg_of_add_eq_zero_left hxpy0
  . apply Or.inl
    exact eq_of_sub_eq_zero hxsy0





section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
 rw [pow_two] at h
 exact mul_self_eq_one_iff.mp h

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have: x ^ 2 - y ^ 2 = 0 := by rw [h]; exact sub_self (y^2)
  have: (x+y)*(x-y) = 0 := by rw [sq_sub_sq] at this;exact this
  have: (x+y)=0 ∨ (x-y)=0 := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with hxpy0|hxsy0
  . apply Or.inr
    exact eq_neg_of_add_eq_zero_left hxpy0
  . apply Or.inl
    exact eq_of_sub_eq_zero hxsy0

end

--my section based on comment

/-
In fact, if you are careful, you can prove the first theorem without using commutativity of multiplication.

In that case, it suffices to assume that R is a Ring instead of an CommRing.
-/
section
variable {R : Type*} [Ring R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
 rw [pow_two] at h
 exact mul_self_eq_one_iff.mp h

end


example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro hpq
  cases (Classical.em P)
  . case mp.inl h => exact Or.inr (hpq h)
  . case mp.inr h => exact Or.inl h
  intro nhprq
  rcases nhprq with hnp|hq
  . exact (fun hp ↦ False.elim (hnp hp))
  . exact (fun hp ↦ hq)
