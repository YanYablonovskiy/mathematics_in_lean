import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic
import Mathlib.Util.Delaborators

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

namespace GaussInt

instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

/-
As noted in Section 6.1, it is a good idea to put all the definitions related to a data type in a namespace with the same name.

Thus in the Lean files associated with this chapter, these definitions are made in the GaussInt namespace.

Notice that here we are defining the interpretations of the notation 0, 1, +, -, and * directly,
rather than naming them GaussInt.zero and the like and assigning the notation to those.

It is often useful to have an explicit name for the definitions, for example, to use with simp and rewrite.
-/


theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl


theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl


#check propext
theorem zero_def' (z : GaussInt): (z = 0) = ((z.re = 0) ∧ (z.im = 0)) := by
 ext
 constructor
 . intro h
   rw [h]
   simp
 . rintro ⟨re0,im0⟩
   rw [zero_def]
   ext <;> simp [re0,im0]


@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl
/-
It is now surprisingly easy to show that the Gaussian integers are an instance of a commutative ring.

We are putting the structure concept to good use. Each particular Gaussian integer is an instance of the GaussInt structure,
whereas the type GaussInt itself, together with the relevant operations, is an instance of the CommRing structure.

The CommRing structure, in turn, extends the notational structures Zero, One, Add, Neg, and Mul.

If you type instance : CommRing GaussInt := _, click on the light bulb that appears in VS Code,
and then ask Lean to fill in a skeleton for the structure definition, you will see a scary number of entries.

Jumping to the definition of the structure, however, shows that many of the fields have default definitions
that Lean will fill in for you automatically.

The essential ones appear in the definition below.

A special case are nsmul and zsmul which should be ignored for now and will be explained in the next chapter.

In each case, the relevant identity is proved by unfolding definitions, using the ext tactic to reduce the
identities to their real and imaginary components, simplifying, and, if necessary,
carrying out the relevant ring calculation in the integers.

Note that we could easily avoid repeating all this code, but this is not the topic of the current discussion.

-/
instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl
/-
Lean’s library defines the class of nontrivial types to be types with at least two distinct elements.

In the context of a ring, this is equivalent to saying that the zero is not equal to the one.

Since some common theorems depend on that fact, we may as well establish it now.
-/
instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp

end GaussInt
/-
We will now show that the Gaussian integers have an important additional property. A Euclidean domain is a ring
(R,+,*,-,1,0) equipped with a norm function N:R→ℕ with the following two properties:

For every a and b ≠ 0 in R, a = bq + r with r = 0 or N(r) < N(b)

For every a and b ≠ 0 in R, N(a) ≤ N(ab)


The ring of integers ℤ with N = | | is an archetypal example of a Euclidean domain.

In that case, we can take q to be the result of integer division of a by b, and
r to be the remainder.

These functions are defined in Lean so that the satisfy the following:
-/
example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt a

namespace Int

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int
#check sq_pos_iff
#check sq_nonneg
#check add_lt_add_of_lt_of_le
#check lt_irrefl

theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  .contrapose!
   intro hxe0
   by_cases h: x = 0
   . have yneq0:_ := hxe0 h
     have := sq_pos_iff.mpr yneq0
     have xsq0: x^2 = 0 := by simp [h]
     rw [xsq0]
     simp [yneq0]
   . have xsqpos:_ := sq_pos_iff.mpr h
     have ysqnoneg:_ := sq_nonneg y
     intro h
     have: x^2 + y^2 > 0+0 := by
      apply add_lt_add_of_lt_of_le (a:= 0) (c:=0)
      . exact xsqpos
      . exact ysqnoneg
     simp at this
     rw [h] at this
     exact lt_irrefl _ this
  . rintro ⟨xsq0,ysq0⟩
    repeat (first|rw [pow_two]|rw [xsq0]|rw [ysq0]|simp_arith)



namespace GaussInt

def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

#check sq_nonneg
#check add_nonneg

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
  rw [norm]
  by_cases hx0: x = 0
  . rw [hx0]
    simp
  . apply add_nonneg <;> exact sq_nonneg _

theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
  rw [norm,zero_def']
  exact sq_add_sq_eq_zero (α := ℤ) x.re x.im

#check le_antisymm

theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
  rw [norm,Ne,zero_def']
  constructor
  . intro lt0
    have := Ne.symm (ne_of_lt lt0)
    by_contra hc
    rw [Ne] at this
    exact this ((sq_add_sq_eq_zero (α := ℤ) x.re x.im).mpr hc)
  . intro h
    by_contra! hc
    have := add_nonneg (sq_nonneg x.re) (sq_nonneg x.im)
    have := le_antisymm this hc
    have := ((sq_add_sq_eq_zero (α := ℤ) x.re x.im).mp this.symm)
    exact h this

theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
  sorry
def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith

theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  exact norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm] ; ring
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime

end GaussInt
