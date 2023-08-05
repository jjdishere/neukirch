import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.ZMod.Basic

variable {p : ℕ} [Fact p.Prime]

-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. 
#check  PadicInt
#check  ℤ_[p]
#check  ℚ_[p]

-- The ring homomorphism from ℤ_[p] to ℤ⧸p^nℤ.
#check PadicInt.toZMod
#check PadicInt.toZModPow

-- The universal property of ℤ_[p] as projective limit. (Commutative Diagram)
#check PadicInt.lift_unique
#check PadicInt.lift_spec

