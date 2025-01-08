import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

section
variable (R : Type*) [Ring R]


#print Ring




#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc,add_comm b,neg_add_cancel,add_zero]


--with three rw
example (a b : R) : a + b + -b = a := by
  rw [add_assoc,add_right_neg,add_zero]




variable (x:R)
#check zero_add
#check Eq.comm.mp (zero_add x)

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
 calc b = 0 + b := Eq.comm.mp (zero_add b)
 _ = ((-a)+a) + b   := by rw [←neg_add_cancel a]
 _ = (-a) + (a+b)   := by rw [add_assoc]
 _ = (-a) + (a+c)   := by rw [h]
 _ = ((-a) + a) + c := by rw [←add_assoc]
 _ = 0 + c          := by rw [neg_add_cancel]
 _ = c              := by rw [zero_add]

--add_left_cancel with least re-writes (ideally 3)
example {a b c : R} (h : a + b = a + c) : b = c := by
rw [←neg_add_cancel_left a b,h,neg_add_cancel_left]

example {a b c : R} (h : a + b = a + c) : b = c := by
have h1: -a + (a + b) = b := (neg_add_cancel_left a b)
rw [h,←add_assoc,neg_add_cancel,zero_add] at h1
exact Eq.comm.mp h1



theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  calc a = a + 0 := Eq.comm.mp (add_zero a)
  _ = a + ((-b) + b) := by rw [←neg_add_cancel b]
  _ = a + b + (-b) := by rw [add_comm (-b),←add_assoc]
  _ = c + b + (-b) := by rw [h]
  _ = c := by rw [add_assoc,add_comm b,neg_add_cancel,add_zero]



theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h1: 0*a = 0*a + 0*a :=
  calc 0 * a = (0 + 0)*a := by rw [add_zero 0]
    _ = 0*a + 0*a := by rw [right_distrib]
  have h2: -(0*a) + (0*a) = 0 := by rw [neg_add_cancel]
  nth_rewrite 2 [h1] at h2;
  rw [←add_assoc,neg_add_cancel,zero_add] at h2;
  exact h2

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have h1: a+b = a+(-a) := by rw [←neg_add_cancel a, add_comm (-a)] at h; exact h
  rw [add_left_cancel h1]


theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have h1: a+b = (-b)+b := by rw [←neg_add_cancel b] at h; exact h
  rw [add_right_cancel h1]


theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have h1: -(-a) + -a =  a + -a := by rw [neg_add_cancel (-a),add_comm a,neg_add_cancel a]
  rw [add_right_cancel h1]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]


/-
In Lean, subtraction in a ring is provably equal to addition of the additive inverse.
-/
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

/-
On the real numbers, it is defined that way:
-/

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg,add_comm,neg_add_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [←one_add_one_eq_two,right_distrib,one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem inv_mul_1 (a b :G): (b⁻¹ * a⁻¹)*(a*b) = 1 := by
 calc (b⁻¹ * a⁻¹)*(a*b) = b⁻¹ * (a⁻¹*a)*b := by rw [←mul_assoc,mul_assoc  b⁻¹]
  _ = b⁻¹ * 1 * b := by rw [inv_mul_cancel a]
  _ = b⁻¹ * b := by rw [mul_assoc,one_mul b]
  _ = 1 := inv_mul_cancel b








theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
 have h1: a * a⁻¹ = (a * a⁻¹)*(a * a⁻¹) :=
  calc a * a⁻¹ =  a * (1 * a⁻¹) := by rw [one_mul]
  _ = a * ((a⁻¹*a)*a⁻¹) := by rw [←inv_mul_cancel a]
  _ = a * a⁻¹ * a * a⁻¹ := by rw [←mul_assoc,←mul_assoc]
  _ = a * a⁻¹ * (a * a⁻¹) := by rw [mul_assoc]
 have h2: (a * a⁻¹)⁻¹*(a * a⁻¹) = (a * a⁻¹)⁻¹ * (a * a⁻¹)*(a * a⁻¹) := by nth_rewrite 2 [h1];rw [←mul_assoc]
 rw [inv_mul_cancel,one_mul] at h2
 exact Eq.comm.mp h2

theorem mul_one (a : G) : a * 1 = a := by
  rw [←inv_mul_cancel a,←mul_assoc,mul_inv_cancel,one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h1:(a * b)⁻¹ * (a * b) = (b⁻¹ * a⁻¹)*(a*b) := by rw [inv_mul_1 a b,inv_mul_cancel]
  have h2: ((a * b)⁻¹ * (a * b))*(a * b)⁻¹ = ((b⁻¹ * a⁻¹)*(a*b))*(a * b)⁻¹ := by rw [h1]
  rw [mul_assoc (a * b)⁻¹, mul_inv_cancel (a*b),mul_one,mul_assoc,mul_inv_cancel (a*b),mul_one] at h2
  exact h2
end MyGroup

end
