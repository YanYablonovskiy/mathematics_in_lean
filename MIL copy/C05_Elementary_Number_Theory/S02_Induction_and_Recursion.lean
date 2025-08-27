import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Lattice

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h


/-
The set of natural numbers is not only fundamentally important in its own right, but also a plays a central role in the construction of new mathematical objects.

Lean’s foundation allows us to declare inductive types, which are types generated inductively by a given list of constructors.

In Lean, the natural numbers are declared as follows.
-/
namespace mine

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

end mine

#check (Nat)

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

--mine
def fac' (n: Nat): Nat :=
let rec loop : Nat → Nat × Nat
    | 0   => (1, 1)
    | 1   => (1,1)
    | 2   => (1,2)
    | n+1 => let p := loop n; (p.2, (n+1) * p.2)
 (loop n).2

#eval fac 1
#eval fac' 6


#check (1,2,3)
#eval  (1,2,3).2

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

--doesnt work
example : fac' 0 = 1 := by
  rw [fac'];admit
--works
example : fac' 0 = 1 := by
 rfl


example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl


--no longer works for my fac , since its not definitionally true
--though computationally faster?
example (n : ℕ) : fac' (n + 1) = (n + 1) * fac' n := by
 rw [fac'];admit

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih --ih being the induction hypothesis bridging the zero cases with any n
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile) --ile being i ≤ 0 here for n = 0, which is absurd with ipos: i > 0
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

#check mul_le_mul_of_nonneg --  (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) : a * c ≤ b * d
#check Nat.one_le_of_lt
#check pow_succ


theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  . simp [fac]
    induction n with --now its the n in the factorial ; but this is the lean original induction way
    | zero => simp [fac]
    | succ n ih =>
      simp [fac]
      rw [pow_succ]
      have: 2 ≤ n + 1 + 1 := by linarith
      rw [mul_comm (n+1+1)]
      apply mul_le_mul_of_nonneg (a:=2^n) (d:= (n+1+1))
      . exact ih
      . exact this
      . simp
      . simp

example (n : ℕ):  2 ^ (n-1) ≤ fac n := by
rcases n with _ | n
. simp [fac]
. simp [fac] --now its easier since n is not 0.
  induction' n with j ih
  . simp [fac]
  . simp [fac]
    rw [pow_succ]
    have: 2 ≤ j + 1 + 1 := by linarith
    rw [mul_comm (j+1+1)]
    apply mul_le_mul_of_nonneg (a:=2^j) (d:= (j+1+1))
    . exact ih
    . exact this
    . simp
    . simp

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset



example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n := --range n is {0,1,2...,n-1}. So when n+1, its {0,1,2,..,n-1,n}, hence f x + f n
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with j ih
  · simp [fac, prod_range_zero]
  simp only [fac]
  simp only [prod_range_succ] -- (j + 1) * fac j = (∏ i ∈ range j, (i + 1)) * (j + 1)
  rw [←ih]
  apply mul_comm
  --simp [fac, ih]
  --simp [prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2) --symm is the same as Eq.comm.mp (for any commutative goal)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
#check div_mul_cancel
#check Nat.div_mul_cancel
#check Nat.mod_two_eq_zero_or_one
#check Nat.add_div
open Set

#check Nat.mod_two_eq_zero_or_one
#check Nat.div_self
#check Nat.mul_one
#check Nat.mul_div_cancel_left
#check Nat.add_assoc
#check Nat.sub_eq_iff_eq_add --Nat.sub_eq_iff_eq_add {b a c : ℕ} (h : b ≤ a) : a - b = c ↔ a = c + b
#check Nat.add_div_of_dvd_right
#check Nat.mul_div_cancel'
#check Nat.div_le_of_le_mul
#check Nat.mul_div_assoc
#check Nat.add_left_cancel_iff

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
apply Eq.comm.mp
induction' n with j ih
. simp
. rw [Finset.sum_range_succ,←ih]
  simp [mul_add,add_mul,←pow_two]
  ring_nf
  rw [←add_comm ((j + j ^ 2 * 3 + j ^ 3 * 2) / 6)]
  have: (6 + j * 13 + j ^ 2 * 9 + j ^ 3 * 2) = (6*(1+j*2 + j ^ 2) + (j + j^2*3 + (j^ 3)*2)) := by simp +arith
  rw [this]
  rw [Nat.add_div_of_dvd_right (a:=6 * (1 + j * 2 + j ^ 2))]
  rw [add_comm]
  rw [propext (Nat.add_left_cancel_iff)]
  simp
  use (1 + j * 2 + j ^ 2)







  example:(@Nat.div_self 6 (by norm_num)) = (h:6/6 = 1) := by
   rfl




inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]



theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' n with j ih
  . rw [zero_add]
    nth_rewrite 2 [add_comm]
    rw [zero_add]
  . rw [succ_add,add_comm m,succ_add,succ_add,add_comm j,ih]
    rw [add_comm m (j.add k).succ,succ_add,add_comm m]


theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with j ih
  . rw [add_comm n,zero_add]
    have: mul m zero = zero := rfl
    rw [this,add_comm,zero_add]
  . rw [add_comm n,succ_add]
    simp [mul]
    rw [add_comm j,ih,add_assoc]


theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with j ih
  . rfl
  . simp [mul]
    rw [add_comm,zero_add,ih]

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with j ih
  . simp [mul,zero_add]
  . simp [mul,add]
    rw [ih]
    rcases m with z | s
    . simp [zero_mul,zero_add]
      rw [add_comm,zero_add]
    . rw [add_comm]
      simp [succ_add]
      rw [add_comm _ s.succ]
      simp [succ_add,mul,add_assoc]


theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with j ih
  . simp [mul,zero_mul]
  . simp [mul,succ_mul,ih]

end MyNat
