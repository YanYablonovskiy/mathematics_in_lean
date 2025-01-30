import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section


/-
Modern mathematics makes essential use of algebraic structures, which encapsulate patterns that can be instantiated in multiple settings.

The subject provides various ways of defining such structures and constructing particular instances.

Lean therefore provides corresponding ways of defining structures formally and working with them.

You have already seen examples of algebraic structures in Lean, such as rings
and lattices, which were discussed in Chapter 2.

This chapter will explain the mysterious square bracket annotations that you saw there,
[Ring α] and [Lattice α].

It will also show you how to define and use algebraic structures on your own.
-/
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext
/-
The @[ext] annotation tells Lean to automatically generate theorems that can be used to prove that two instances *of a structure are equal when their components are equal,
a property known as extensionality.

here this is a hardcoded instance of point for type ℝ
-/
example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

--another way
def myPoint4: Point := {x := 2, y:= -1,z:=4}

structure Point' where build :: --name the constructor
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  dsimp [add]
  ext
  repeat simp [add_assoc]

def smul (r : ℝ) (a : Point) : Point :=
  match a with
  | p => Point.mk (r*(p.x)) (r*(p.y)) (r*(p.z))

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  dsimp [add,smul]
  ext
  repeat simp [mul_add,add_mul]

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section
#check add_nonneg
#check mul_nonneg
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  {x := lambda*(a.x) + (1-lambda)*(b.x),
   y :=  lambda*(a.y) + (1-lambda)*(b.y),
   z := lambda*(a.z) + (1-lambda)*(b.z)
   x_nonneg := by
    have p1:_ := a.x_nonneg
    have p2:_ := b.x_nonneg
    have p3:(1 - lambda) ≥ 0 := by simp; exact lambda_le
    apply add_nonneg
    . exact mul_nonneg lambda_nonneg p1
    . exact mul_nonneg p3 p2
   y_nonneg := by
    have p1:_ := a.y_nonneg
    have p2:_ := b.y_nonneg
    have p3:(1 - lambda) ≥ 0 := by simp; exact lambda_le
    apply add_nonneg
    . exact mul_nonneg lambda_nonneg p1
    . exact mul_nonneg p3 p2
   z_nonneg := by
    have p1:_ := a.z_nonneg
    have p2:_ := b.z_nonneg
    have p3:(1 - lambda) ≥ 0 := by simp; exact lambda_le
    apply add_nonneg
    . exact mul_nonneg lambda_nonneg p1
    . exact mul_nonneg p3 p2,
   sum_eq := by
    have: lambda * a.x + (1 - lambda) * b.x + (lambda * a.y + (1 - lambda) * b.y) + (lambda * a.z + (1 - lambda) * b.z) = lambda*(a.x + a.y + a.z - (b.x + b.y + b.z)) + (b.x + b.y + b.z) := by
     ring
    rw [this]
    rw [a.sum_eq,b.sum_eq]
    simp
    ;}

end

end StandardTwoSimplex

open BigOperators


/-
Structures can depend on parameters.

For example, we can generalize the standard 2-simplex to the standard-simplex for any n.

At this stage, you don’t have to know anything about the type Fin n except that it has
elements, and that Lean knows how to sum over it.
-/

#check Fin
#check (Fin)
#print Fin
#check Fin.partialSum
structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2 --i is in Fin n
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

/-
As an exercise, see if you can define the weighted average of two points in the standard
-simplex. You can use Finset.sum_add_distrib and Finset.mul_sum to manipulate the relevant sums.
-/

#check Fin.sum_univ_succ
#check Fin.succ
#check Fin.sum_univ_add
#check Finset.sum_add_distrib
#check add_nonneg
#check Fin.sum_univ_castSucc
#check Finset.sum_nonneg
#check Finset.sum_mul
#check Fin.mul_comm
#check Finset.equivFin

def weightedAverage (n: ℕ) (hne1: n ≠ 0) (lambda: Fin n → ℝ) (hpos: ∀i:Fin n, lambda i ≥ 0) (hle1: ∀i:Fin n, lambda i ≤ 1) (hsumeq1: (∑ i:Fin n, lambda i) = 1)
    (simplexes: Fin n → StandardSimplex n) : StandardSimplex n where
  V i := ∑ j:Fin n, ((simplexes j).V i)*(lambda j)
  NonNeg := by
   intro i
   dsimp
   apply Finset.sum_nonneg
   . intro j hj
     apply mul_nonneg
     . exact (simplexes j).NonNeg i
     . exact hpos j
  sum_eq_one := by admit

end StandardSimplex


/-
We have seen that structures can be used to bundle together data and properties.

Interestingly, they can also be used to bundle together properties without the data.

For example, the next structure, IsLinear, bundles together the two components of linearity.
-/
structure IsLinear (f : ℝ → ℝ) where --can be a class with different types (given an add and mul instance)
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
/-
It is worth pointing out that structures are not the only way to bundle together data.

The Point data structure can be defined using the generic type product, and IsLinear can be defined with a simple and.
-/
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

/-
Generic type constructions can even be used in place of structures with dependencies between their components.

For example, the subtype construction combines a piece of data with a property.

You can think of the type PReal in the next example as being the type of positive real numbers.

Any x : PReal has two components: the value, and the property of being positive.

You can access these components as x.val, which has type ℝ, and x.property,
which represents the fact 0 < x.val.
-/


def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end
/-
We could have used subtypes to define the standard 2-simplex, as well as the standard
-simplex for an arbitrary n.
-/

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }
/-
Similarly, Sigma types are generalizations of ordered pairs, whereby the type of the second component depends on the type of the first.
-/
def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2
/-
Given s : StdSimplex, the first component s.fst is a natural number, and the second component is an element of the corresponding simplex StandardSimplex s.fst.

The difference between a Sigma type and a subtype is that the second component of a Sigma type is data rather than a proposition.

But even though we can use products, subtypes, and Sigma types instead of structures, using structures has a number of advantages.

Defining a structure abstracts away the underlying representation and provides custom names for the functions that access the components.

This makes proofs more robust: proofs that rely only on the interface to a structure will generally continue to work when we change the definition,
as long as we redefine the old accessors in terms of the new definition.

Moreover, as we are about to see, Lean provides support for weaving structures together into a rich, interconnected hierarchy,
and for managing the interactions between them.

-/
end
