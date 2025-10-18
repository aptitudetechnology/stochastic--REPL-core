/-
Complete proof of commutativity of addition on natural numbers.
This demonstrates the proof pattern you'll use for stochastic computing theorems.
-/
import Lean.Data.Nat.Basic

-- Helper lemma: 0 + n = n (already in Lean, but shown for clarity)
theorem Nat.zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [Nat.add_succ]
    rw [ih]

-- Helper lemma: (n + 1) + m = n + (m + 1)
theorem Nat.succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, Nat.add_succ]
    rw [ih]

-- Main theorem: addition is commutative
theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    -- Base case: 0 + m = m + 0
    rw [Nat.zero_add]
    rw [Nat.add_zero]
  | succ n ih =>
    -- Inductive step: (n + 1) + m = m + (n + 1)
    -- ih : n + m = m + n
    rw [Nat.succ_add]  -- (n + 1) + m = (n + m) + 1
    rw [ih]            -- (n + m) + 1 = (m + n) + 1
    rw [Nat.add_succ]  -- (m + n) + 1 = m + (n + 1)