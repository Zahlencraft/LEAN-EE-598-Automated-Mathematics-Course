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
theorem T₁ : ∀ x : ℝ, 0 ≤ x ^ 2 := by
  intro x
  simpa [pow_two] using sq_nonneg x

-- Type Checking
-- L∃∀N is based on type theory.
-- This means that every term has a very well-defined type. To find the type of an expression, use #check. The result will show up in the Infoview.

#check 1
#check "1"
#check ∃ (x : Nat), x < 0
#check fun x => x+1

--Exercise
#check (4, 5) --
#check ℕ × ℕ
#check Type
