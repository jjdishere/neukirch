import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion

variable {p : ℕ} [Fact p.Prime]

-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. 
#check  PadicInt
#check  ℤ_[p]
#check  ℚ_[p]
