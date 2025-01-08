import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)
#print min --doesnt have order in it?
#print Min
#print min_le_right
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h --swaps the arguments

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left


variable (x:ℝ)

#check max_le_max_right
#check max_le_max_right (h:= le_refl x)
#check max_le_max_left (h:= le_refl x)
#check le_max_left
#check le_max_right


#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check max_le --∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤ c → max a b ≤ c

example : max a b = max b a := by
  apply le_antisymm
  . have h11: max b a ≥ a ∧ max b a ≥ b := And.intro (le_max_right b a) (le_max_left b a)
    exact max_le (c:=max b a) h11.1 h11.2
  . have h1: max a b ≥ b ∧ max a b ≥ a := And.intro (le_max_right a b) (le_max_left a b)
    exact max_le (c:=max a b) h1.1 h1.2

#check min_cases

example : min (min a b) c = min a (min b c) := by
  rw [min_comm a (min b c)];
  cases min_cases (min b c) a
  . case inl h => rw [h.1]; apply (min_le_iff.mp h.2).elim; intro hp; rw [min_eq_right hp];intro hp;admit
  admit


#check min_le_left  (b + c) (a + c)
#check min_eq_left
#check min_eq_right



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
 cases min_cases a b
 . case inl h =>
    rw [h.1];
    let (h1: (a + c) ≤ (b + c)) := add_le_add (h.2) (le_refl c);
    rw [min_eq_left]; exact h1
 . case inr h =>
     rw [h.1];
     let (h2: (b + c) ≤ (a + c)) := by linarith;
     rw [min_eq_right]; exact h2


#check add_le_add (_:a ≤ b) (le_refl c)
#check aux
#check aux a b (b - a) --aux a b (b - a) : min a b + (b - a) ≤ min (a + (b - a)) (b + (b - a))

--aux a b (b - a) : min a b + (b - a) ≤ min (a + (b - a)) (b + (b - a))
--aux a b (b - a) : min a b + (b - a) ≤ min b (b + (b - a))
-- min a b + b ≤ min b (b + (b - a)) + a

#check add_neg_cancel_right





example : min a b + c = min (a + c) (b + c) := by
  sorry
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)


#check add_sub_cancel_right


example : |a| - |b| ≤ |a - b| :=
  calc |a| - |b| = |a + b - b| - |b| := by rw [add_sub_cancel_right a b]
  _ ≤ |a-b| + |b| -|b| := by rw [add_comm,←add_sub]; linarith [abs_add b (a-b)]
  _ ≤ |a-b| := by rw [←add_sub];simp




#check add_sub
section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    . rw [←mul_assoc y x z,mul_comm y,mul_assoc]; exact dvd_mul_right x (y*z)
    . apply dvd_mul_left
  . rw [pow_two w];apply dvd_mul_of_dvd_left h w

#check Nat.pow_two
#check dvd_mul_of_dvd_left  (_ : x ∣ w) w
#check dvd_mul_left x (y*z)
#check dvd_add
end
section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
 apply dvd_antisymm
 . have h1: m.gcd n ∣ m ∧ n.gcd m ∣ n := And.intro ((Nat.gcd_dvd m n).1) ((Nat.gcd_dvd n m).1)
   admit
 . admit





#check (Nat.gcd_dvd m n).1
#check (Nat.gcd_dvd n m).1


end

#check gcd
#check Nat.gcd_gcd_self_left_left
#check Nat.gcd_dvd
#check Nat.gcd_dvd_gcd_of_dvd_right
#check Nat.gcd_le_left
#check Nat.gcd_zero_left
