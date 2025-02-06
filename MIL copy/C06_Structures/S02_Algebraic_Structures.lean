import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

namespace C06S02
/-
To clarify what we mean by the phrase algebraic structure, it will help to consider some examples.

A partially ordered set consists of a set P and a binary relation ≤
on P that is transitive and reflexive.

A group consists of a set G with an associative binary operation, an identity element
1, and a function g ↦ g⁻¹ that returns an inverse for each
g in G. A group is abelian or commutative if the operation is commutative.

A lattice is a partially ordered set with meets (pairwise greatest lower bound) and joins (pairwise least upper bound).

A ring consists of an  (additively written) abelian group (R,+,x ↦ x⁻¹)
together with an associative multiplication operation ⬝ and an identity 1,
such that multiplication distributes over addition. A ring is commutative if the multiplication is commutative.

An ordered ring (R,+,0,-,⬝,1,≤) consists of a ring together with a
partial order on its elements, such that a ≤ b implies a + c ≤ b + c
for every a,b and c in R, 0 ≤ a and 0 ≤ b implies 0 ≤ a⬝b for every a
and b in R.

A metric space consists of a set X and a function
d: X × X → ℝ such that the following hold:
 ⬝ d(x,y) ≥ 0 for every x and y in X.
 . d(x,y) = 0 ↔ x = y.
 . d(x,y) = d(y,x) for all x and y in X.
 . d(x,z) ≤ d(x,y) + d(y,z) for every x, y and z in X

A topological space consists of a set X and a collection
Τ of subsets of X, called the open subsets of,
such that the following hold:

The empty set ∅ and X are open(in T).

The intersection of two open sets is open(in T).

An arbitrary union of open sets is open.

-/
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

/-
It is sometimes useful to bundle the type together with the structure, and Mathlib also
contains a definition of a GroupCat structure that is equivalent to the following:
-/
structure Group₁Cat where
  α : Type*
  str : Group₁ α
/-
The Mathlib version can be found in Mathlib.Algebra.Category.GroupCat.Basic.

For reasons that will become clearer below, it is more often useful to keep the type α separate from the structure Group α.

We refer to the two objects together as a partially bundled structure, since the representation combines most,
but not all, of the components into one structure.

It is common in Mathlib to use capital roman letters like G for a
type when it is used as the carrier type for a group.
-/
section

/-
Let’s construct a group, which is to say, an element of the Group₁ type. For any pair of types α and β, Mathlib defines the type Equiv α β of equivalences between α and β.

Mathlib also defines the suggestive notation α ≃ β for this type. An element f : α ≃ β is a bijection between α and β represented by four components:
a function f.toFun from α to β, the inverse function f.invFun from β to α, and two properties that specify these
functions are indeed inverse to one another.
-/
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α) --instead of equal; related to univalence axiom?
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)


/-
Notice the creative naming of the last three constructions.

We think of the identity function Equiv.refl, the inverse operation Equiv.symm, and the composition operation Equiv.trans
as explicit evidence that the property of being in bijective correspondence is an equivalence relation.

Notice also that f.trans g requires composing the forward functions in reverse order.

Mathlib has declared a coercion from Equiv α β to the function type α → β, so we can omit writing .toFun and have Lean insert it for us.
-/
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl
--transitivity of the equivalence relation creates the product function (also an equivalence)
example (x : α) : (f.trans g) x = g (f x) := --coercion?
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end
--Perm standing for permutations,i.e bijective automorphisms
example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl


variable (α: Type*)
#check Equiv.refl α
#check @Function.id_def α

--shows its the identity
example (α : Type*) :  (Equiv.refl α).toFun = fun x => x :=
  rfl


/-
It should be clear that Equiv.Perm α forms a group under composition of equivalences.

We orient things so that mul f g is equal to g.trans f, whose forward function is f ∘ g.

In other words, multiplication is what we ordinarily think of as composition of the bijections.

Here we define this group:
-/
#check Equiv.symm
#check Equiv.mk
def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f --composition (always compatible since α → α)
  one := Equiv.refl α --one is just  identity map
  inv := Equiv.symm --automatically coerces to function? can be defined as  Equiv.invFun as Fun and vice versa
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm --by dsimp; apply Equiv.trans_assoc
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  (add : α → α → α)
  (zero: α)
  (neg: α → α)
  (zero_add : ∀a:α,add a zero = a)
  (add_zero : ∀a:α,add zero a = a)
  (neg_add_cancel : ∀a:α,add a (neg a) = zero)
  (add_assoc : ∀(a b c:α),add a (add b c) = add (add a b) c)


  -- fill in the rest
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point := {x := -a.x,y := -a.y, z := -a.z}

def zero : Point := ⟨0,0,0⟩

def addGroupPoint : AddGroup₁ Point :=
{
  add := add
  zero := zero
  neg := neg
  zero_add := by
   intro a
   simp [add,zero]
  add_zero := by
   intro a
   simp [zero,add]
  neg_add_cancel := by
   intro a
   simp [add,neg,zero]
  add_assoc := by
   intro a b c
   simp [add,add_assoc]
}
end Point

section
/-
We are making progress. Now we know how to define algebraic structures in Lean, and we know how to define instances of those structures.

But we also want to associate notation with structures so that we can use it with each instance.

Moreover, we want to arrange it so that we can define an operation on a structure and use it with any particular instance,
and we want to arrange it so that we can prove a theorem about a structure and use it with any instance.

In fact, Mathlib is already set up to use generic group notation, definitions, and theorems for Equiv.Perm α.
-/
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare
/-
The #check command shows that Group₂.mul has an implicit argument [Group₂ α] that we expect to be found by class inference,
where α is the type of the arguments to Group₂.mul.

In other words, {α : Type*} is the implicit argument for the type of the group elements and [Group₂ α]
is the implicit argument for the group structure on α.

Similarly, when we define a generic squaring function my_square for Group₂, we use an implicit argument {α : Type*}
for the type of the elements and an implicit argument [Group₂ α] for the Group₂ structure.

In the first example, when we write Group₂.mul f g, the type of f and g tells Lean that in the argument α to Group₂.mul
has to be instantiated to Equiv.Perm β. That means that Lean has to find an element of Group₂ (Equiv.Perm β).

The previous instance declaration tells Lean exactly how to do that. Problem solved!

This simple mechanism for registering information so that Lean can find it when it needs it is remarkably useful.
Here is one way it comes up. In Lean’s foundation, a data type α may be empty.

In a number of applications, however, it is useful to know that a type has at least one element.

For example, the function List.headI, which returns the first element of a list, can return the default value when the list is empty.

 To make that work, the Lean library defines a class Inhabited α,
 which does nothing more than store a default value. We can show that the Point type is an instance:
-/
section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
/-
As a similarly artificial exercise, define a class AddGroup₂ in analogy to Group₂.

Define the usual notation for addition, negation, and zero on any AddGroup₂ using the classes Add, Neg, and Zero.

Then show Point is an instance of AddGroup₂.

Try it out and make sure that the additive group notation works for elements of Point.
-/
class AddGroup₂ (α : Type*) where
  add : α → α → α
  -- fill in the rest
  (zero: α)
  (neg: α → α)
  (zero_add : ∀a:α,add a zero = a)
  (add_zero : ∀a:α,add zero a = a)
  (neg_add_cancel : ∀a:α,add a (neg a) = zero)
  (add_assoc : ∀(a b c:α),add a (add b c) = add (add a b) c)

instance: AddGroup₂ Point where
 add := Point.add
 zero := default
 neg := Point.neg
 zero_add := by rw [default,instInhabitedPoint];simp [Point.add]
 add_zero := by rw [default,instInhabitedPoint];simp [Point.add]
 neg_add_cancel := by simp [Point.neg,Point.add]; rfl
 add_assoc := by simp [Point.add,add_assoc]

variable (x y: Point)

#check x+y


instance : Neg Point where neg := Point.neg
instance : Zero Point where zero := default

#check x+0
#check x+(-y)+-0
