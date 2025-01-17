import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

section
variable {α : Type*}
variable (s t u : Set α)
open Set
#check inter_def
#check mem_setOf
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩


/-
In this example, we open the set namespace to have access to the shorter names for the theorems. But, in fact, we can delete the calls to rw and simp entirely:

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
-/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
/-
What is going on here is known as definitional reduction: to make sense of the intro command and the anonymous constructors
Lean is forced to expand the definitions. The following example also illustrate the phenomenon:
-/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left --meaning the left disjunct
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩ --anon contructor, allows | for diff contructors of inductive types
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩



example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x h
  rcases h with ⟨xs,xt⟩|⟨xs,xu⟩
  . exact ⟨xs, (Or.inl xt)⟩
  . exact ⟨xs, (Or.inr xu)⟩


example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u (to get false)
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

--tactic proof
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x ⟨hx,nxtu⟩
  constructor
  use hx
  . intro xt
    exact nxtu (Or.inl xt)
  . intro xu
    exact nxtu (Or.inr xu)








example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

/-
Once again, deleting the line simp only [mem_inter_iff] does not harm the proof.

In fact, if you like inscrutable proof terms, the following one-line proof is for you:
-/

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩ --first one is mp direction, second is mpr

/-
Here is an even shorter proof, using the simplifier:
-/
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

#check Subset.antisymm -- {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b


/-
An alternative to using ext is to use the theorem Subset.antisymm
which allows us to prove an equation s = t between sets by proving s ⊆ t and t ⊆ s.

--(uses propext at some stage)
-/
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩


--term proof
example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨hs,ht⟩ ↦ ⟨ht,hs⟩) (fun x ⟨ht,hs⟩ ↦ ⟨hs,ht⟩)



--tactic proof
example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  . intro ⟨xs,_⟩
    exact xs
  . intro xs
    exact ⟨xs,Or.inl xs⟩

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  . rintro (xs | ⟨xs,xt⟩ ) <;> exact xs
  . intro _; exact _


example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . rintro ( ⟨xs,_⟩ | xt )
    . exact Or.inl xs
    . exact Or.inr xt
  . rintro (xs | xt)
    . by_cases h: x ∈ t
      . exact Or.inr h
      . exact Or.inl ⟨xs,h⟩
    . exact Or.inr xt


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  admit


--set builder notation
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

--same as:
def evens' : Set ℕ :=
  fun n ↦ Even n

def odds' : Set ℕ :=
  fun n ↦ ¬ Even n


example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd] --want to keep ¬Even instead of Odd
  apply Classical.em

/-
In fact, set-builder notation is used to define

s ∩ t as {x | x ∈ s ∧ x ∈ t},

s ∪ t as {x | x ∈ s ∨ x ∈ t},

∅ as {x | False}, and

univ as {x | True}.
-/

variable (a: ℕ )
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial
#check univ a
#print univ



#check Nat.prime_def_lt 
#check IsUnit a
#check isUnit_iff_eq_one.mp

#check mul_two


example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n ⟨h1,h2⟩
  dsimp
  by_contra!
  rcases this with ⟨w,hw⟩
  rw [←mul_two,mul_comm] at hw
  rcases h1  with ⟨nu,h⟩
  have := (h 2 w) hw
  rcases this with h | h
  . contradiction
  . rw [isUnit_iff_eq_one.mp h,mul_one] at hw
    rw [mem_def] at h2
    rw [hw] at h2
    contradiction


  


#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
