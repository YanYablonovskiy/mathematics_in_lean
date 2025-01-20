import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Util.Delaborators

open Set
open Function
/-

-/


noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]



section
variable (f : α → β) (g : β → α)




def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x


#check invFun
#print invFun

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    constructor
    . trivial
    . exact hx
  have : ∃ y, g y = x := by
    simp at this
    exact this
  rw [invFun]
  rw [dif_pos this,choose_spec this]


section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)
#check (RightInverse)
#print RightInverse
end
#check dif_pos
#check if_neg

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂) --to prove h is injective, so show x₁ = x₂
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        rw [hxeq]
        apply Eq.comm.mp
        exact sb_right_inv f g x₂nA
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A,if_pos x₂A] at hxeq
    exact hf hxeq
  push_neg at xA
  rcases xA with ⟨x₁nA,x₂nA⟩
  rw [if_neg x₁nA,if_neg x₂nA] at hxeq
  have t1:_ := sb_right_inv f g x₁nA
  have t2:_ := sb_right_inv f g x₂nA
  have t3: ∃ x, g x = x₂ := by use invFun g x₂
  have t4: ∃ x, g x = x₁ := by use invFun g x₁
  have := Eq.refl (g (invFun g x₁))
  have t5: g (invFun g x₁) = g (invFun g x₂) := by nth_rewrite 2 [hxeq] at this;exact this
  rw [t1,t2] at t5
  exact t5




#check invFun_eq -- (∃ y, g y = x) → g (invFun g x) = x)
#check invFun_eq_of_injective_of_rightInverse

/-
{f : α → β}
{g : β → α} (hf : Injective f) (hg : RightInverse g f) : invFun f = g
-/




/-
  rw [if_neg xA.1,if_neg xA.2] at hxeq
  rw [invFun,invFun] at hxeq
  have t1:_ := sb_right_inv f g xA.1
  have t2:_ := sb_right_inv f g xA.2
  have t3: ∃ x, g x = x₂ := by use invFun g x₂
  have t4:  ∃ x, g x = x₁ := by use invFun g x₁
  have t5: ∃ x, g x = x₂ := by use invFun g x₂
  have t6:  ∃ x, g x = x₁ := by use invFun g x₁
  obtain ⟨x₁nA,x₂nA⟩ := xA
  rw [dif_pos t4] at hxeq
  rw [dif_pos t3] at hxeq
  obtain ⟨x1,x1eq⟩ := t3
  obtain ⟨x2,x2eq⟩ := t4
  rw [Eq.comm.mp x1eq,Eq.comm.mp x2eq]
-/


theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  have := sb_right_inv (β:=β) f g gyA
  have := hg this
  use g y
  rw [h_def]
  rw [sbFun]
  rw [if_neg gyA]
  exact this





end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
