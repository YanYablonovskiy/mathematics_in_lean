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
  intro x hx
  simp at hx
  simp
  show f x ∈ v
  exact h hx



example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x hfx
  simp at hfx
  simp
  constructor
  . rcases hfx with ⟨x,hxst,xeq⟩
    use x
    constructor
    . exact hxst.1
    . exact xeq
  . rcases hfx with ⟨x,hxst,xeq⟩
    use x
    constructor
    . exact hxst.2
    . exact xeq

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x h3
  simp at h3
  rcases h3 with ⟨h1,h2⟩
  rcases h1 with ⟨x,xs,xeq⟩
  rcases h2 with ⟨y,ys,yeq⟩
  rw [Eq.comm.mp xeq] at yeq
  have := h yeq
  rw [this] at ys
  simp
  use x



example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x h
  simp at h
  rcases h with ⟨h1,h2⟩
  rcases h1 with ⟨x1,x1s,x1eq⟩
  simp
  have h3: x1 ∉ t := fun (t1:x1 ∈ t) ↦ (h2 x1) t1 (x1eq)
  use x1



example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  --x:α ∈ f⁻¹' u (u : Set β) means x | (f x ∈ u) or fun x ↦ u f x
  intro x h
  rcases h with ⟨h1,h2⟩
  simp at h1
  simp at h2
  simp
  constructor
  . exact h1
  . exact h2

#check subset_antisymm
example : f ⁻¹' (u \ v) ⊆ f ⁻¹' u \ f ⁻¹' v := by
intro x h
simp at h
simp
exact h

--my one
example : f ⁻¹' u \ f ⁻¹' v = f ⁻¹' (u \ v) := by
apply subset_antisymm
. intro x h
  rcases h with ⟨h1,h2⟩
  simp at h1
  simp at h2
  simp
  constructor
  . exact h1
  . exact h2
. intro x h
  simp at h
  simp
  exact h


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  . intro h
    simp at h
    rcases h with ⟨h1,h2⟩
    rcases h1 with ⟨x1,x1s,x1eq⟩
    simp
    use x1
    constructor
    constructor
    . exact x1s
    . have: f x1 ∈ v := by rw [Eq.comm.mp x1eq] at h2; exact h2
      exact this
    . exact x1eq
  . intro h
    simp at h
    rcases h with ⟨x1,h1,h2⟩
    simp
    constructor
    . use x1
      exact ⟨h1.1,h2⟩
    . have: x ∈ v := by rw [h2] at h1; exact h1.2
      exact this


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x h
  simp at h
  rcases h with ⟨x1,hx1₁,hx1eq⟩
  rcases hx1₁ with ⟨hx2,hx3⟩
  simp
  constructor
  . use x1
  . rw [hx1eq] at hx3
    exact hx3


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x h
  simp at h
  rcases h with ⟨h1,h2⟩
  simp
  constructor
  . use x
  . exact h2

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x h
  simp at h
  simp
  match h with
  | Or.inl h1 => apply Or.inl; use x
  | Or.inr h2 => exact Or.inr h2


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
 ext x
 constructor
 . intro h
   simp at h
   simp
   rcases h with ⟨x1,hi⟩
   rcases hi with ⟨hi1,x1eq⟩
   rcases hi1 with ⟨i,x1Ai⟩
   use i
   use x1
 . intro h
   simp at h
   rcases h with ⟨i,hi⟩
   rcases hi with ⟨x1,x1Ai,x1eq⟩
   simp
   use x1
   constructor
   . use i
   . exact x1eq


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x h
  simp at h
  rcases h with ⟨x1,hx1,x1eq⟩
  simp
  intro i
  use x1
  constructor
  . exact hx1 i
  . exact x1eq

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x hx
  simp at hx
  have := hx i
  rcases this with ⟨x1,x1Ai,x1eq⟩
  simp
  by_contra!
  apply this x1 _
  . exact x1eq
  . by_contra! fh
    rcases fh with ⟨I,x1ni⟩
    have t1:_ := hx I
    rcases t1 with ⟨t2,t3⟩
    have t4: x1 = t2 := by rw [Eq.comm.mp t3.2] at x1eq;exact injf x1eq
    rw [t4] at x1ni
    exact (x1ni t3.1)


example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro hx
    simp at hx
    rcases hx with ⟨i,fxBi⟩
    simp
    use i
  . intro hx
    simp at hx
    rcases hx with ⟨i,fxBi⟩
    simp
    use i

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  . intro hx
    simp at hx
    simp
    exact hx
  . intro hx
    simp at hx
    simp
    exact hx

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real
/-
The statement Injective f is provably equivalent to InjOn f univ.

Similarly, the library defines range f to be {x | ∃y, f y = x}, so range f is provably equal to f '' univ.

This is a common theme in Mathlib: although many properties of functions are defined relative to their full domain,
there are often relativized versions that restrict the statements to a subset of the domain type.

Here is are some examples of InjOn and range in use:
-/
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

#check sq_sqrt

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro rteq
  calc x = (√x)^2 := Eq.comm.mp (sq_sqrt xnonneg)
       _ = (√y)^2 := by rw [rteq]
       _ = y := sq_sqrt ynonneg


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro powtwoeq
  simp at powtwoeq
  calc x = √(x^2) := Eq.comm.mp (sqrt_sq xnonneg)
       _ = √(y^2) := by rw [powtwoeq]
       _ = y := sqrt_sq ynonneg

#check sqrt_nonneg
#check pow_two_nonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . intro h
    simp at h
    rcases h with ⟨x1,x1nonneg,xeq⟩
    simp
    rw [Eq.comm.mp xeq]
    exact sqrt_nonneg x1
  . intro h
    simp at h
    simp
    use (x^2)
    constructor
    . exact pow_two_nonneg x
    . exact sqrt_sq h


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  . intro h
    simp at h
    simp
    rcases h with ⟨y,hy⟩
    rw [Eq.comm.mp hy]
    exact pow_two_nonneg y
  . intro h
    simp at h
    simp
    use √x
    exact sq_sqrt h



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

#print LeftInverse
/-
 {α : Sort u₁} → {β : Sort u₂} → (g:β → α) → (f:α → β) → Prop :=
fun {α} {β} g f => ∀ (x : α), g (f x) = x --like a normal inverse
-/
#print RightInverse
/-
def Function.RightInverse.{u₁, u₂} : {α : Sort u₁} → {β : Sort u₂} → (g:β → α) → (f:α → β) → Prop :=
fun {α} {β} g f => LeftInverse f g  ( f (g (x)) = x )
-/
#check dif_pos
#print Injective
#check choose
#check choose_spec

example : Injective f ↔ LeftInverse (inverse f) f := by
 rw [Injective,LeftInverse]
 constructor
 . intro h
   intro x
   rw [inverse]
   have t1: ∃ x_1, f x_1 = f x := Exists.intro x rfl
   rw [dif_pos t1]
   have t2: f (choose t1) = f x := by simp [choose_spec t1]
   have := h t2
   exact this
 . intro h a1 a2 hfa
   have t3:_ := h a1
   have t4:_ := Eq.comm.mp (h a2)
   rw [hfa] at t3
   apply Eq.comm.mp
   exact Eq.trans t4 t3


example : Surjective f ↔ RightInverse (inverse f) f := by
 rw [RightInverse,Surjective,LeftInverse]
 constructor
 . intro h
   intro x
   rw [inverse]
   have := h x
   rw [dif_pos this]
   rw [choose_spec this]
 . intro h
   intro b
   use (inverse f b)
   exact h b



end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by --no surjective function from something to its power set
  intro f surjf --need false from Surjective
  let S := { i | i ∉ f i } --define an element of Set α
  rcases surjf S with ⟨j, h⟩ --j is what takes α to S;
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    exact this h'
    --contradiction
  have h₂ : j ∈ S
  exact h₁
  have h₃ : j ∉ S
  rw [h] at h₁
  exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
