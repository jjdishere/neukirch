import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open Filter

theorem tens (b : ℝ) : ∃ a : ℕ → ℝ, (∀ n, (b : ℝ) < a n) ∧ Tendsto a atTop (nhds b) := by
  use fun n ↦ b + 1 / (n + 1)
  constructor 
  · intro n
    simp only [one_div, lt_add_iff_pos_right, inv_pos]
    have npos : 0 < n + 1 := by exact Nat.succ_pos n
    exact Nat.cast_add_one_pos n
  · sorry
