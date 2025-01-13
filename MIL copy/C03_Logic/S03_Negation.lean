import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)


#check lt_irrefl
#check lt_asymm



example {a:ℝ} {b:ℝ}:  ¬(a < a) → (a < b) → ¬b < a :=
fun (h1:_) => fun (h:( a < b )) => fun (h2:_) => False.elim (h1 (lt_trans h h2))


example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)
--theirs
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

#check not_le_of_gt
#check [Preorder ℝ]


example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  fun  (hf: FnHasLb f) => hf.elim (fun (b:ℝ) (hfn:FnLb f b) =>  ((h b).elim (fun (x:ℝ) h2 => False.elim ((not_le_of_gt (h2)) (hfn x)))))

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
intro FnLb
rcases FnLb with ⟨b,hgb⟩
rcases (h b) with ⟨x,flua⟩
have _:f x ≥ b := hgb x
linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro FnLb
  rcases FnLb with ⟨b,hgb⟩
  rcases (h b) with ⟨x,flua⟩
  have fxgb:f x ≥ b := hgb x
  apply not_le_of_gt (a:=b)
  . exact flua
  . exact fxgb


-- variable (a1 a2 a3: ℝ) (ha3: a3 > 0) (hk: a3 ≥ 1)

-- #check lt_add_of_le_of_pos (le_refl a1) ha3
#check le_mul_of_one_le_left
#check lt_mul_of_one_lt_left
#check lt_or_eq_of_le
#check le_of_not_lt

example : ¬FnHasUb fun x ↦ x := by
  intro FUb
  rcases FUb with ⟨u,hub⟩
  match (Classical.em (u > 0)) with
  | Or.inl h =>
    let c := (2:ℝ)
    have cge1: c > 1 := by norm_num
    have h1 : 2*u > u := lt_mul_of_one_lt_left (b:=u) h cge1
    have h2: u ≥ 2*u := by exact hub (2*u)
    linarith
  | Or.inr g =>
    have: u ≤ 0 := le_of_not_lt g
    match (lt_or_eq_of_le this) with
    | Or.inl k =>
      let c := (0:ℝ)
      have h2: u ≥ 0 := by exact hub (0)
      linarith
    | Or.inr k2 =>
      have h3: 2 ≤ u := by exact hub 2
      linarith



  -- have cge1: c > 1 := by norm_num
  -- have: 2*u ≥ u :=
  -- exact hub u


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)




example (h : Monotone f) (h' : f a < f b) : a < b := by
  have: ¬(f a ≥ f b) := not_le_of_gt h'
  have: ¬(a ≥ b) := fun hblea:(a ≥ b) ↦ this (h hblea)
  exact lt_of_not_ge this




 example (h : Monotone f):  (f a < f b) → a < b := by
  contrapose
  intro h2
  have: b ≤ a := le_of_not_gt h2
  have: f b ≤ f a := h this
  exact not_lt_of_ge this


--tactic proof
example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hmf
  have: f a ≤ f b := hmf h
  linarith

--term proof
example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f :=
 fun hmf ↦ (not_le_of_gt (h')) (hmf h)


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

#check Preorder

#print Preorder
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by intro x y hlxy; exact le_refl 0
  have h' : f (1:ℝ) ≤ f (0:ℝ) := le_refl _
  have: (1:ℝ) ≤ (0:ℝ) := (h monof) h'
  linarith



example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro posx
  have: x < x := (h x) posx
  linarith


end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

--term proof
example (h : ¬∃ x, P x) : ∀ x, ¬P x :=
  fun (x:α) (hpx:P x) ↦ False.elim (h ⟨x,hpx⟩)

--tactic proof
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
intro x hpx
exact False.elim (h ⟨x,hpx⟩)

--tactic proof
example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro expx
  rcases expx with ⟨x,hpx⟩
  exact (h x) hpx

--term proof
example (h : ∀ x, ¬P x) : ¬∃ x, P x :=
  fun expx ↦ expx.elim (fun x hpx ↦ (h x) hpx)

--term proof, needs LEM
example (h : ¬∀ x, P x) : ∃ x, ¬P x :=
  have: ¬ ¬ ∃ x, ¬P x := fun nexpx:(¬ ∃ x, ¬P x ) ↦
    have hapx: ∀x, P x := fun x ↦ (Classical.em (P x)).elim (fun hpx ↦ hpx) (fun hnpx ↦ False.elim (nexpx ⟨x,hnpx⟩))
    h hapx
  (Classical.em (∃ x, ¬P x)).elim (fun k ↦ k) (fun nk ↦ False.elim (this nk))


example (h : ∃ x, ¬P x) : ¬∀ x, P x :=
 fun hapx ↦ h.elim (fun x hnpx ↦ hnpx (hapx x))


--tactic proof
example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  rcases h with ⟨x,hnpx⟩
  intro hapx
  exact hnpx (hapx x)


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h' --creates ¬ of goal (¬ ∃ x, ¬P x), to get a false
  apply h --unites h with false, needs ∀x, P x
  intro x --intro x to make P x
  show P x --we show P x
  by_contra h'' -- assume ¬P x
  exact h' ⟨x, h''⟩ -- get False from the example of x ¬Px applies to h'

--tactic proof
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

--term proof
example (h : ¬¬Q) : Q :=
 match Classical.em Q with
 | Or.inl HQ => HQ
 | Or.inr HNQ => False.elim (h HNQ)

#check not_not.mp

example (h : ¬¬Q) : Q :=
not_not.mp h

--tactic proof
example (h : Q) : ¬¬Q := by
  intro hnq
  exact hnq h

--term proof
example (h : Q) : ¬¬Q :=
 fun hnq ↦ (hnq h)


end

section
variable (f : ℝ → ℝ)


-- #check (not_le_of_gt : a > b → ¬a ≤ b)
-- #check (not_lt_of_ge : a ≥ b → ¬a < b)
-- #check (lt_of_not_ge : ¬a ≥ b → a < b)
-- #check (le_of_not_gt : ¬a > b → a ≤ b)


--tactic proof
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  have: FnUb f a := by
   intro x; by_contra h''; let H1 := (lt_of_not_ge (α:=ℝ) h'');exact False.elim (h' ⟨x,H1⟩)
  apply h
  exact ⟨a,this⟩




example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
