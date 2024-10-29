#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred

def funk: Nat -> Nat := fun (x: Nat) ↦ x
#eval funk 5

#eval (λ x : Nat => x + 5) 10    -- 15

-- Creating a function from another expression is a process known as lambda abstraction.
--  Suppose you have the variable x : α and you can construct an expression t : β,
--  then the expression fun (x : α) => t, or, equivalently, λ (x : α) => t, is an object of type α → β.
--  Think of this as the function from α to β which maps any value x to the value t.

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

-- Lean interprets the final three examples as the same expression; in the last expression,
--  Lean infers the type of x and y from the expression if not y then x + 1 else x + 2.

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool

-- Think about what these expressions mean. The expression fun x : Nat => x denotes the identity function on Nat,
--  the expression fun x : Nat => true denotes the constant function that always returns true, and fun
--  x : Nat => g (f x) denotes the composition of f and g.
--  You can, in general, leave off the type annotation and let Lean infer it for you. So, for example,
--  you can write fun x => g (f x) instead of fun x : Nat => g (f x).
