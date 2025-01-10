import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

#check lt_of_lt_of_le
-- {a b c : α} (hab : a < b) (hbc : b ≤ c) : a < c


theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
intro x y e h1 h2 h3 h4
have hl1: |x| < 1 := (@lt_of_lt_of_le ℝ _ |x| e 1 h3 h2)
have h12: |y| < 1 := (@lt_of_lt_of_le ℝ _ |y| e 1 h4 h2)
admit


section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry



#check mul_lt_mul_right
#check mul_le_mul
#check abs_nonneg
#check le_of_lt
#check lt_of_lt_of_le
#check one_pos
#check mul_lt_mul


theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul _ _
    _ ≤ |x| * ε := mul_le_mul (le_refl |x|) (le_of_lt ylt) (abs_nonneg y) (abs_nonneg x)
    _ < 1 * ε := mul_lt_mul (lt_of_lt_of_le xlt ele1) (le_refl ε) epos (le_of_lt one_pos)
    _ = ε := one_mul _



def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb


--term version
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  fun (x:ℝ) => add_le_add (hfa x) (hgb x)


--tactic version
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
 intro x
 dsimp
 apply add_le_add
 apply hfa
 apply hgb



variable (a b c: ℝ)

#check mul_zero 0
#check mul_le_mul (a:=0) (c:=0)

--term proof
example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  have h1:(FnLb (fun x ↦ f x * g x) (0*0)) := (fun (x:ℝ) => (mul_le_mul (a:=0) (c:=0) (nnf x) (nng x) (le_refl 0) (nnf x)))
  show FnLb (fun x ↦ f x * g x) 0 from Eq.subst (mul_zero 0) h1



example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  rw [←mul_zero 0]
  apply mul_le_mul
  . apply nnf
  . apply nng
  . exact le_refl 0
  . apply nnf



#check mul_le_mul

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  fun (x:ℝ) => mul_le_mul (b:=a) (d:=b) (hfa x) (hgb x) (nng x) (nna)





end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)


--this works??
-- example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
--    unfold

--
#check mul_le_mul_left


example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
intro a b haleb
dsimp
cases lt_or_eq_of_le (nnc)
. case inl h0ltc => exact (mul_le_mul_left (h0ltc)).mpr (mf haleb)
. case inr hceq0 => rw [←hceq0,zero_mul,zero_mul]


example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  /-
     need f(g(a)) ≤ f(g(b)); can get it from mg and hleb
  -/
  fun a b haleb ↦ mf (mg haleb)




def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]

variable (a b c: ℝ) (g:ℝ → ℝ)
#check FnOdd g
#check neg_one_sq
#check Eq.subst
#check sq
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x :=
  fun x ↦
   calc f x * g x = -f (-x) * g x := by rw [←(of x)]
   _ = -f (-x) * (-g (-x)) := by rw [←(og x)]
   _ = (f (-x)*(-1:ℝ)) *  (g (-x)*(-1:ℝ)) := by rw [←(mul_neg_one (f (-x))),←(mul_neg_one (g (-x)))]
   _ = f (-x)*-1 * -1 *g (-x) := by rw [mul_comm (g (-x)),←mul_assoc]
   _ = f (-x) *((-1:ℝ) * -1) * g (-x) := by rw [mul_assoc (f (-x))]
   _ = f (-x) * g (-x) := by rw [←sq (-1),neg_one_sq,mul_assoc,one_mul (g (-x))]


/-
   have h1: (f x * g x = -f (-x) * g x) := Eq.subst (FnOdd f x)
   have h2: -f (-x) * g x = -f (-x) * (-g (-x)) := Eq.subst (FnOdd g x)
   have h3: f x * g x  = -f (-x) * (-g (-x)) := Eq.trans h1 h2

-/
#check a

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := 
  fun x ↦ 
    calc f x * g x = f (-x) * g x := Eq.subst (ef x) (motive := fun y ↦ (f x * g x  = y * g x)) (Eq.refl (f x * g x))
    _ = f (-x) *  -g (-x) := Eq.subst (og x) (motive := fun y ↦ (f (-x) * g x  = f (-x) * y)) (Eq.refl (f (-x) * g x))
    _ = f (-x) * (-1*g (-x)) := Eq.subst (Eq.comm.mp (neg_one_mul (g (-x))))  (motive := fun y ↦ (f (-x) * -g (-x)  = f (-x) * y)) (Eq.refl (f (-x) * -g (-x)))
    _ = f (-x) * -1*(g (-x)) := Eq.subst (Eq.comm.mp (mul_assoc (f (-x)) (-1) (g (-x)) )) (motive := fun y ↦ f (-x) * (-1*g (-x))   = y) (Eq.refl (f (-x) * (-1 * g (-x))))
    _ = -(f (-x) * g (-x)) := by rw [mul_comm (f (-x)),mul_assoc,neg_one_mul]



example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
intro x
dsimp
rw [og x,ef (g (-x))]



end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry

end
