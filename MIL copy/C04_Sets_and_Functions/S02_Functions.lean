import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

/-
If f : α → β is a function and p is a set of elements of type β, the library defines preimage f p, written f ⁻¹' p, to be {x | f x ∈ p}.

The expression x ∈ f ⁻¹' p reduces to f x ∈ p. This is often convenient, as in the following example:
-/



example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext --x✝ ∈ f ⁻¹' (u ∩ v) ↔ x✝ ∈ f ⁻¹' u ∩ f ⁻¹' , which is really x | f x ∈ u ∩ f x ∈ v , and x | f x ∈ u ∩ x | f x ∈ v
  rfl



/-
If s is a set of elements of type α, the library also defines image f s, written f '' s, to be {y | ∃ x, x ∈ s ∧ f x = y}.

So a hypothesis y ∈ f '' s decomposes to a triple ⟨x, xs, xeq⟩ with x : α satisfying the hypotheses xs : x ∈ s and xeq : f x = y.

The rfl tag in the rintro tactic (see Section 3.2) was made precisely for this sort of situation.
-/
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩ --rfl for the f'' x = f x
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h
    intro h1 h1p
    simp
    have: f h1 ∈ f '' s := ⟨h1,h1p,rfl⟩
    exact h this
  . intro h
    intro h1 h1s
    rcases h1s with ⟨x,xis,xeq⟩
    have: x ∈  f ⁻¹' v := h xis
    simp at this
    rw [xeq] at this
    exact this

#check Injective f
#print Injective

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  simp at hx
  rcases hx with ⟨y,hey⟩
  have: y=x := h hey.2
  rw [Eq.comm.mp this]
  exact hey.1




example : f '' (f ⁻¹' u) ⊆ u := by
  intro x hx
  simp at hx
  rcases hx with ⟨x,fxu,feqx⟩
  rw [Eq.comm.mp feqx]
  exact fxu

#print Surjective
/-
{α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop :=
fun {α} {β} f => ∀ (b : β), ∃ a, f a = b
-/
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by --f ⁻¹' u meaning x: f(x) ∈ u ; y ∈ f'' meaning exists x, such that x in (f(x) ∈ u) and f(x) = y
  intro x
  contrapose!
  intro h1
  intro xu
  simp at h1
  rcases h x with ⟨a,fa⟩
  have := h1 a
  rw  [fa] at this
  have := this xu
  exact this (Eq.refl x)




example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x hf
  rcases hf with ⟨a,as,yfa⟩
  exact ⟨a,(h as),yfa⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
