-- Lean Project Types
-- Standalone : A standalone Lean project is a simple project that contains only a single Lean file and does not depend on any external lib.
import Mathlib.Data.Real.Basic
#eval 1 + 2

example (x y z : ℚ)
        (h1 : 2 * x < 3 * y)
        (h2 : -4 * x + 2 * z < 0)
        (h3 : 12 * y - 4 * z < 0) : False := by
  sorry

--exercise
theorem T₁ : ∀ x : ℝ, 0 ≤ x ^ 2 := by sorry

-- Type Checking
-- L∃∀N is based on type theory.
-- This means that every term has a very well-defined type. To find the type of an expression, use #check. The result will show up in the Infoview.

#check 1  --ℕ
#check "1" -- "1" : String
#check ∃ (x : Nat), x < 0 -- ∃ (x : Nat), x < 0 : Prop
#check fun x => x+1  -- fun x => x + 1 : Nat → Nat

--Exercise
#check (4, 5) -- (4, 5) : ℕ × ℕ

#check ℕ × ℕ -- ℕ × ℕ : Type

#check Type -- Type : Type 1

-- check is doing something like not only checking the type of an expression, but also inferring the type of the expression.

-- like why ℕ × ℕ  is Type, because ℕ is Type, and the product of two types is also a type.
