import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

/-
So far in this chapter, we discussed how to create a hierarchy of mathematical structures.

But defining structures is not really completed until we have morphisms.

There are two main approaches here. The most obvious one is to define a predicate on functions.
-/
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'

--Monoid is semigroup with a unit, magma with associativity and neutral

/-
In this definition, it is a bit unpleasant to use a conjunction.

In particular users will need to remember the ordering we chose when they want to access the two conditions.

So we could use a structure instead.
-/

structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

#check isMonoidHom₂  --{G : Type u_1} → {H : Type u_2} → [inst : Monoid G] → [inst : Monoid H] → (G → H) → Prop
--with auto implicit true, G and H are auto populated; the structure lives in Prop

structure isMonoidHom₂' [Monoid G] [Monoid H] (f : G → H) where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

#check isMonoidHom₂' --isMonoidHom₂'.{u_1, u_2} {G : Type u_1} {H : Type u_2} [Monoid G] [Monoid H] (f : G → H) : Type ; no longer Prop

/-
Once we are here, it is even tempting to make it a class and use the type class instance resolution procedure to automatically infer isMonoidHom₂
for complicated functions out of instances for simpler functions.

For instance a composition of monoid morphisms is a monoid morphism and this seems like a useful instance.

However such an instance would be very tricky for the resolution procedure since it would need to hunt down g ∘ f everywhere.

Seeing it failing in g (f x) would be very frustrating. --fail to apply because cant find instance; which isnt helpful

More generally one must always keep in mind that recognizing which function is applied in a given expression is a very difficult problem,
called the “higher-order unification problem”.

So Mathlib does not use this class approach.

A more fundamental question is whether we use predicates as above (using either a def or a structure) or use structures bundling a function and predicates.

--i.e whether the function itself is part of the structure or an input to it


This is partly a psychological issue.

It is extremely rare to consider a function between monoids that is not a morphism.

It really feels like “monoid morphism” is not an adjective you can assign to a bare function, it is a noun.

On the other hand one can argue that a continuous function between topological spaces is really a function that happens to be continuous.

This is one reason why Mathlib has a Continuous predicate.

For instance you can write:
-/

example : Continuous (id : ℝ → ℝ) := continuous_id
/-
We still have bundles of continuous functions, which are convenient for instance to put a topology on a space of continuous functions,
but they are not the primary tool to work with continuity.

By contrast, morphisms between monoids (or other algebraic structures) are bundled as in:
-/

@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

/-
Of course we don’t want to type toFun everywhere so we register a coercion using the CoeFun type class.

Its first argument is the type we want to coerce to a function.

The second argument describes the target function type.

In our case it is always G → H for every f : MonoidHom₁ G H. We also tag MonoidHom₁.toFun with
the coe attribute to make sure it is displayed almost invisibly in the tactic state, simply
by a ↑ prefix.
-/

instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

section
variable [Monoid G] [Monoid H] (h: MonoidHom₁ G H) (g: G)

#check h
#check h.toFun
#check h g -- h.toFun g : H


end


attribute [coe] MonoidHom₁.toFun --so it can have the ↑ notation


section
variable [Monoid G] [Monoid H] (h: MonoidHom₁ G H) (g: G)

#check h
#check h.toFun
#check h g -- ↑h g : H


end
/-
Let us check we can indeed apply a bundled monoid morphism to an element.
-/

example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one --↑f 1 = 1

/-
We can do the same with other kind of morphisms until we reach ring morphisms.
-/

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'


instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun


--doesnt work due to some random technical reason (need to be forgetful?)

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

/-
There are a couple of issues about this approach.

A minor one is we don’t quite know where to put the coe attribute since the RingHom₁.toFun does not exist,
the relevant function is MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁ which is not a declaration that can be
tagged with an attribute (but we could still define a CoeFun  (RingHom₁ R S) (fun _ ↦ R → S) instance).

A much more important one is that lemmas about monoid morphisms won’t directly apply to ring morphisms.

This leaves the alternative of either juggling with RingHom₁.toMonoidHom₁ each time we want to apply a
monoid morphism lemma or restate every such lemmas for ring morphisms.

Neither option is appealing so Mathlib uses a new hierarchy trick here.

The idea is to define a type class for objects that are at least monoid morphisms,
instantiate that class with both monoid morphisms and ring morphisms and use it to state every lemma.

In the definition below, F could be MonoidHom₁ M N, or RingHom₁ M N if M and N have a ring structure.
-/


class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where --depends on F
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

/-
However there is a problem with the above implementation. We haven’t registered a coercion to function instance yet. Let us try to do it now.
-/

def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun

/-

-/

class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun


instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul


lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h



class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul


@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
  := sorry
