import Mathlib.Topology.Algebra.ValuedField
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Rat.NNRat
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


variable {K : Type _} [Monoid K]

theorem commK (x y : K) : x * y = y * x := sorry 


#check le_trans

theorem aa {a : ℕ} (h : 1 ≤ a) : 0  < 1 / (a : ℚ) := by 
  have this : ∃ (b : ℕ), a = (b : ℚ) + 1 := by apply?
  rcases this with ⟨b, this'⟩
  rw [this']
  exact Nat.one_div_pos_of_nat