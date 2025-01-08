import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h1:a < c :=
   by apply lt_of_le_of_lt h₀ h₁
  have h2: a < d :=
   by apply lt_of_lt_of_le h1 h₂
  apply lt_trans h2 h₃


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h'] --a proof of exp b ≤ exp c via b ≤ c

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
have h1: a+d ≤ a+e := by linarith
have h2: exp (a +d) ≤ exp (a+e) := by exact exp_le_exp.mpr h1
linarith



example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  apply log_le_log h₀
  . linarith [exp_le_exp.mpr h]

example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

#check neg_le_neg


example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h1:-(exp b) ≤ -(exp a) :=
   by exact neg_le_neg (exp_le_exp.mpr h)
  linarith [h1]



example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example (a b: ℝ) :a*b ≤ (a^2 + b^2)/2 := by
have h1: (a-b)^2 = a^2 - 2*a*b + b^2 := by ring_nf
have h2: 0 ≤ (a-b)^2 := sq_nonneg (a-b)
have h3: 0 ≤ a^2 - 2*a*b + b^2 := by linarith [h2]
have h4: 2*a*b ≤ a^2 + b^2 := by linarith
have h5: a*b ≤ (a^2 + b^2)/2 := by linarith
exact h5






example : |a*b| ≤ (a^2 + b^2)/2 := by
 apply abs_le'.mpr
 apply And.intro
 . have h1:(a-b)^2 = a^2 - 2*a*b + b^2 := by ring_nf
   have h2:(a-b)^2 ≥ 0 := by apply sq_nonneg
   have h3: a^2 - 2*a*b + b^2 ≥ 0 := by rw [h1] at h2; exact h2
   have h4: a^2 + b^2 ≥ 2*a*b := by linarith
   have h5: (a^2 + b^2)/2 ≥ a*b := by linarith
   exact h5
 . have h11:(a+b)^2 = a^2 + 2*a*b + b^2 := by ring_nf
   have h21:(a+b)^2 ≥ 0 := by apply sq_nonneg
   have h31: a^2 + 2*a*b + b^2 ≥ 0 := by rw [h11] at h21; exact h21
   have h41: a^2 + b^2 ≥ -2*a*b := by linarith
   have h51: (a^2 + b^2)/2 ≥ -(a*b) := by linarith
   exact h51


-- example : |a*b| ≤ (a^2 + b^2)/2 := by
--   have pos2: (2:ℝ) > 0 := by norm_num
--   have ht:(|(a-b)^2| ≤ a^2 - 2*|a*b| + b^2) :=
--    calc |(a-b)^2| = |a^2 + 2*a*(-b) + (-b)^2| := by ring_nf
--    _ ≤ |a^2| - |2*a*b| + |b^2| := abs_add_three (a^2) (2*a*b) (b^2)
  --  _ = |a^2| + |2| * |a*b| + |b^2| := by rw [mul_assoc 2 a b,abs_mul 2]
  --  _ = |a^2| + 2 * |a*b| + |b^2| := by rw [abs_of_pos pos2]
  --  _ =  a^2 + 2*|a*b| + b^2 := by rw [abs_sq,abs_sq]
--   have pht: 0 ≤ |(a+b)^2| := abs_nonneg ((a+b)^2)
--   have ht2: 0 ≤ a^2 + 2*|a*b| + b^2 := le_trans pht ht

#check abs_nonneg
#check abs_sq
#check sq_nonneg
#check abs_of_pos
#check abs_mul
#check abs_add_three
#check abs_le'.mpr
