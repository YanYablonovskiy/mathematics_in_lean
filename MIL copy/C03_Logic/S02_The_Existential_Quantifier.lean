import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

#check add_le_add


example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
rcases lbf with ⟨z,lbfz⟩
rcases lbg with ⟨y,lngf⟩
use z + y
intro x
apply add_le_add (lbfz x) (lngf x)




--term proof
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x :=
match lbf with
 | ⟨l,lf⟩ => match lbg with
            | ⟨l1,lg⟩ => ⟨l +l1,fun x:ℝ ↦ add_le_add (lf x) (lg x)⟩


--eq compiler proof
example: FnHasLb f → FnHasLb g → FnHasLb fun x ↦ f x + g x
| ⟨l,lf⟩,⟨l1,lg⟩ => ⟨l +l1,fun x:ℝ ↦ add_le_add (lf x) (lg x)⟩

#check mul_le_mul_of_nonneg_left

 --tactic proof (sort of?)
example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  match ubf with
  | ⟨a,ubfa⟩  => exact ⟨c*a, fun x ↦ (mul_le_mul_of_nonneg_left (a:=c) (ubfa x)) h ⟩


example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
 let ⟨a,ubfa⟩ := ubf
 apply Exists.intro (c*a)
 intro x
 dsimp
 apply mul_le_mul_of_nonneg_left (a:=c)
 . exact ubfa x
 . exact h


example {c: ℝ}: FnHasUb f → c ≥ 0  → FnHasUb fun x ↦ c * f x
| ⟨a,ubfa⟩, h => ⟨c*a,  fun x ↦ (mul_le_mul_of_nonneg_left (a:=c) (ubfa x)) h ⟩


example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

end

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa => --only the one case, where there is an upper bound
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa => --next is short for case intro
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring


#check left_distrib
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  match divab with
  | ⟨d, beqad⟩ => match divac with
    | ⟨e,ceqed⟩ => apply Exists.intro (d+e); rw [beqad,ceqed,←left_distrib]


example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, beqad⟩
  rcases divac with ⟨e,ceqed⟩
  use d+e
  rw [beqad,ceqed,←left_distrib]

end

section

open Function

#check Surjective
#print Surjective


example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring;


--tactic proof
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use c⁻¹ * x
  dsimp; field_simp



example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}



--tactic proof
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro y
  rcases (surjg y) with ⟨b,hb⟩
  rcases (surjf b) with ⟨x, hx⟩
  dsimp
  use x
  rw [hx,hb]

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) :=
fun (y:γ) => let  ⟨b,hb⟩ := (surjg y);let  ⟨x, hx⟩ := (surjf b); by apply Exists.intro x;dsimp;rw [hx,hb]

end
