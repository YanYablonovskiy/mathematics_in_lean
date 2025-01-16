import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε


/-
The notation ∀ ε > 0, ... is a convenient abbreviation for ∀ ε, ε > 0 → ..., and, similarly,
∀ n ≥ N, ... abbreviates ∀ n, n ≥ N →  ....

And remember that ε > 0, in turn, is defined as 0 < ε, and n ≥ N is defined as N ≤ n.
-/

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext --prove equality for any pair of inputs
  ring --use ring to get (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 for each entry, extenstionality of functions implies equality

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring


example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring


#check (mul_lt_mul_right _).2
/-
  0 < a → (b * a < c * a ↔ b < c)
-/

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h --convert goal intro b * a < c * a, i.e 1*a < a*a; also introduce a >0
                                   --this means it creates goals to get the goal (a < a * a) out of 1*a < a*a
  · rw [one_mul]                   --which creates a=1*a .
  exact lt_trans zero_lt_one h --get a > 0 from 1 > 0 and a > 1

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos --for all ε > 0, given such
  use 0 --use 0 for N, so for n ≥ N
  intro n nge --intro n ≥ 0
  rw [sub_self, abs_zero] --now need |a - a| < ε; sub_self to get |0|, and abs_zero to get 0 < ε as equivalent statement
  apply εpos --true by assumption, for any ε>0



#check norm_add_le
#check le_max_left
#check le_max_of_le_left
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩ --cs (ε/2) is ∃N, and hs is ∀n≥Ns ...
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n
  have: |(s n) + (t n) - (a + b)| = |((s n) - a) + ((t n) - b)| := by congr;ring
  have trh:|((s n) - a) + ((t n) - b)| ≤ |(s n) - a| + |(t n) - b| := norm_add_le ((s n) - a) ((t n) - b)
  intro hns
  have h1: n ≥ Ns ∧ n ≥ Nt := by
   constructor
   . exact le_trans (le_max_left Ns Nt) (hns)
   . exact le_trans (le_max_right Ns Nt) (hns)
  have h2: |(s n) - a| < ε/2 ∧ |(t n) - b| < ε/2 := by
   constructor
   . exact (hs n) h1.1
   . exact (ht n) h1.2
  linarith

#check norm_mul

#check mul_lt_mul_of_nonneg -- (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d

/-
|s n - a| < e / (2 * |c|)
|c| * |s n - a| < e
-/
#check inv_pos.mpr
#check mul_pos
#check two_pos
#check mul_lt_mul_of_pos_of_nonneg --(h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d

/-
this : |s n - a| < e / (2 * |c|)
⊢ |c| * |s n - a| < |c| * (e / (2 * |c|))
-/



theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  . have acpos : 0 < |c| := abs_pos.mpr h
    intro e epos
    have: 2*|c| > 0 := mul_pos (two_pos) acpos
    have: ( 2 * |c| )⁻¹ > 0 := inv_pos.mpr this
    have h2:  e / (2 * |c|) > 0 := mul_pos epos this
    rcases cs (e/(2*|c|)) h2 with ⟨Na,ha⟩
    use Na
    intro n nnonneg
    dsimp
    rw [←mul_sub (a:=c) (s n) a]
    have h1:|s n - a| < e / (2 * |c|) := (ha n) nnonneg
    rw [abs_mul]
    have h3: |c| * |s n - a| < |c| * (e / (2*|c|)) := mul_lt_mul_of_pos_of_nonneg (a:=|c|) (le_refl |c|) h1 acpos (le_of_lt h2)
    have: |c| * (e / (2 * |c|)) = e/2 := by field_simp; rw [mul_comm |c|,mul_comm 2,mul_assoc]
    rw [this] at h3
    linarith



#check abs_sub_abs_le_abs_sub
#check lt_of_le_of_lt
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩ --with 1 of a , i.e |s n - a| < 1
  use N, |a| + 1
  intro n hnN
  have h1: |s n - a| < 1 := (h n) hnN
  have h2: |s n| - |a| ≤ |s n - a| := abs_sub_abs_le_abs_sub (s n) a
  have:|s n| - |a| < 1 := lt_of_le_of_lt h2 h1
  linarith






theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
