import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  . apply le_inf (a:= x ⊓ y)
    . exact inf_le_right
    . exact inf_le_left
  . apply le_inf (a:= y ⊓ x)
    . exact inf_le_right
    . exact inf_le_left

--one line
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat (first|apply le_inf (a:= _ ⊓ _)|exact inf_le_right|exact inf_le_left)


example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . case a _ =>
      have h1: (x ⊓ y) ⊓ z ≤ x :=
       le_trans (inf_le_left) (inf_le_left)
      have h2: (x ⊓ y) ⊓ z ≤ y ⊓ z :=
       have h21: (x ⊓ y) ⊓ z ≤ y := le_trans (inf_le_left) (inf_le_right)
       have h22: (x ⊓ y) ⊓ z ≤ z := inf_le_right
       le_inf h21 h22
      exact le_inf h1 h2
  . case a _ =>
     have h3: x ⊓ (y ⊓ z) ≤ x ⊓ y :=
      have h31: x ⊓ (y ⊓ z) ≤ x := inf_le_left
      have h32: x ⊓ (y ⊓ z) ≤ y := le_trans (inf_le_right) (inf_le_left)
      le_inf h31 h32
     have h4: x ⊓ (y ⊓ z) ≤ z := le_trans (inf_le_right) (inf_le_right)
     exact le_inf h3 h4


#check le_inf
#check le_sup_iff --∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c
#check sup_le_iff.mp
#check sup_le
#check le_sup_right



example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  . exact sup_le (le_sup_right) (le_sup_left)
  . exact sup_le (le_sup_right) (le_sup_left)




example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . case a _ =>
     have h3: x ⊔ (y ⊔ z) ≥ x ⊔ y :=
      have h31: x ⊔ (y ⊔ z) ≥  x := le_sup_left
      have h32: x ⊔ (y ⊔ z) ≥ y := le_trans (le_sup_left) (le_sup_right)
      sup_le h31 h32
     have h4: x ⊔ (y ⊔ z) ≥ z := le_trans (le_sup_right) (le_sup_right)
     exact sup_le h3 h4
  . case a _ =>
      have h1: (x ⊔ y) ⊔ z ≥ x :=
       le_trans (le_sup_left) (le_sup_left)
      have h2: (x ⊔ y) ⊔ z ≥ y ⊔ z :=
       have h21: (x ⊔ y) ⊔ z ≥ y := le_trans (le_sup_right (b:=y)) (le_sup_left (b:=z))
       have h22: (x ⊔ y) ⊔ z ≥ z := le_sup_right
       sup_le h21 h22
      exact sup_le (c:= (x ⊔ y) ⊔ z) h1 h2

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . exact inf_le_left
  . exact le_inf (le_refl x) (le_sup_left)   --b is x, c is x ⊔ y, a is x


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . exact sup_le (le_refl x) (inf_le_left)
  . exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry


example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check one_pos
#check le_of_add_le_add_left -- (bc : a + b ≤ a + c) : b ≤ c
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check mul_le_mul_left_of_neg


example (h : a ≤ b) : 0 ≤ b - a := by
  have h1:_ := add_le_add_right h (-a)
  rw [add_comm,neg_add_cancel] at h1
  rw [←sub_eq_add_neg] at h1
  exact h1

--quickest way
example (h: 0 ≤ b - a) : a ≤ b := by
  rw [←neg_add_cancel b,add_comm,sub_eq_add_neg] at h
  have h1:_ := le_of_add_le_add_left h
  simp_all


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1: b-a ≥ 0 := by simp_all
  have h2: (b-a)*c ≥0 := mul_nonneg h1 h'
  rw [mul_sub_right_distrib] at h2
  simp_all

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)


--long version
example (x y : X) : 0 ≤ dist x y := by
  have h1:_ := dist_triangle x y x
  rw [dist_self,dist_comm y] at h1
  have h2: dist x y + dist x y = dist x y*(1+1) := by rw [mul_add_one (b:=1) (dist x y),mul_one]
  rw [h2] at h1
  exact nonneg_of_mul_nonneg_left h1 (add_pos (one_pos) (one_pos))


--short version
example (x y : X) : 0 ≤ dist x y := by
  have h1:_ := dist_triangle x y x
  rw [dist_self,dist_comm y] at h1
  linarith


#check nonneg_of_mul_nonneg_left
#check mul_add_one
#check one_pos
#check add_pos (one_pos) (one_pos)

end
