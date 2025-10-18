/-
GitHub Copilot:
Write the complete proof in Lean 4 for the commutativity of addition
on the natural numbers (Nat).
The proof should be done by induction on the first variable 'n'.
You will need to use the `add_succ` theorem (`n + (Nat.succ m) = Nat.succ (n + m)`)
or related properties, and the basic definitions:
- n + 0 = n
- n + (m + 1) = (n + m) + 1

Prove the theorem `Nat.add_comm`.
-/

import Lean.Data.Nat.Basic -- Imports basic Nat definitions if needed

-- Define the theorem statement
theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  -- Start the proof strategy: induction on n
  induction n with
  | zero =>
    -- Base case: 0 + m = m + 0
    -- Hint: Use the definition of addition
    sorry -- Copilot should fill this in
  | succ n ih =>
    -- Inductive step: (n + 1) + m = m + (n + 1)
    -- The inductive hypothesis `ih` is n + m = m + n
    sorry -- Copilot should fill this in

-- Expected result format:
-- theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
--   ... complete proof using induction on n ...
