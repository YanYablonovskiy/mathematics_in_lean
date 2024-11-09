import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]





theorem test (a b c: ℕ+) : a * b * c = b * (a * c) :=
  have hc: a*b*c = b*a*c := mul_right_cancel_iff.mpr (mul_comm a b)
  sorry

variable (m n k: ℕ+)
variable (a b c: ℝ)
#check mul_right_cancel_iff.mpr
-- mul_right_cancel_iff.mpr : ?m.1063 = ?m.1064 → ?m.1063 * ?m.1062 = ?m.1064 * ?m.1062
#check mul_right_cancel_iff.mpr (mul_comm m n)
#check mul_right_cancel_iff.mpr
--#check mul_right_cancel_iff.mpr (mul_comm a b)
#check mul_comm m (n*k)
#check mul_assoc

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc c b a]
  rw [mul_comm c (b*a)]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]


-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]




/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc]
  rw [mul_comm a ] -- just one argument, matching first pattern.
  rw [mul_assoc]

-- Using facts from the local context.
--v1
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

--v2
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
  rw [h']




example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp,hyp',mul_comm,sub_self]

--v1
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

--v2
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc, h', h,mul_assoc]


section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check mul_assoc a
#synth LinearOrder Nat


end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add,add_mul,add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [ ← add_assoc, add_assoc (a * a) (b * a) (a * b)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm a b,← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)
variable (p₂:b*a  = b*a)
 --v1
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add,add_mul,add_mul,← add_assoc,add_assoc (a * c) (b * c),add_comm (b * c),← add_assoc]

--v2
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d) = (a + b) * c + (a + b)*d := by rw [left_distrib]
  _ = a*c + b*c + (a + b)*d := by rw [right_distrib]
  _ = a*c + b*c + (a*d + b*d) := by rw [right_distrib]
  _ = a*c + b*c + a*d + b*d := by rw [← add_assoc]
  _ = a*c + (b*c + a*d) + b*d := by rw [add_assoc (a*c)]
  _ = a*c + (a*d + b*c) + b*d := by rw [add_comm (a*d)]
  _ = a*c + a*d + b*c + b*d := by rw [← add_assoc]


--v1 via apply?
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  exact Eq.symm (sq_sub_sq a b)

--v2 made up improv
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [right_distrib,sub_eq_add_neg,left_distrib,left_distrib,← add_assoc,mul_neg,mul_comm a b,add_assoc (a*a),add_comm (-(b*a)),← sub_eq_add_neg,sub_eq_zero.mpr,add_zero,mul_neg,← sub_eq_add_neg,← pow_two, ← pow_two]
  simp

--v3 neater no calc
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
rw [right_distrib,mul_sub_left_distrib,mul_sub_left_distrib]
rw [sub_eq_add_neg,sub_eq_add_neg,← add_assoc]
rw [mul_comm a b,← sub_eq_add_neg]
rw [add_assoc (a*a), add_comm (-(b * a)),← sub_eq_add_neg]
rw [←pow_two,←pow_two]
rw [sub_self,add_zero]



def p₁: Prop := ((b*a) = (b*a))
variable (p₂:b*a  = b*a)
#check b*a  = b*a
#check p₁ a b
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
--
#check sub_eq_add_neg
#check mul_neg
#check sub_eq_zero
#check sub_eq_zero.mpr p₂
#check sub_zero


end


-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
