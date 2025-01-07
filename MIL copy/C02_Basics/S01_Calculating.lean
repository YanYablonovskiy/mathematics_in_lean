
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
-- conv version
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  conv =>
  rhs
  rw [←mul_assoc,mul_comm,←mul_assoc]

--term proof
example (a b c : ℝ) : c * b * a = b * (a * c) :=
calc
c*b*a = c*(b*a) := mul_assoc c b a
_ = (b*a)*c := mul_comm c (b*a)
_ = b*a*c := rfl
_ = b*(a*c) := mul_assoc b a c

example (a b c : ℝ) : c * b * a = b * (a * c) := by
 rw [mul_comm c,mul_comm a,←mul_assoc]

--conv proof
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  conv =>
  rhs
  rw [←mul_assoc]
  rw [mul_comm b a]
  exact mul_assoc a b c



example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
calc
 a*(b*c) = a*b*c := Eq.comm.mp (mul_assoc a b c)
 _ = b*a*c := by rw [mul_comm a b]
 _ = b*(a*c) := mul_assoc b a c








-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm,mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a,mul_comm a,mul_assoc]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a,h,←mul_assoc a]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp,hyp',mul_comm b,sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

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
      rw [←add_assoc, add_assoc (a*a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

theorem m1 : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add,add_mul,add_mul,←add_assoc,add_assoc (a*c),add_comm (b*c),←add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  have h1: a-b = a+(-b) := rfl;
  rw [h1,m1,mul_neg,mul_neg];
  rw [←pow_two,←pow_two]
  rw [mul_comm b a,add_assoc (a^2),add_comm (-(a*b)),add_neg_cancel,add_zero]
  rfl


#check add_neg_cancel
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check mul_neg

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
