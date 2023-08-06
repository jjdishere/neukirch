import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Basic

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

/- Proposition 1.2 : The residue classes a mod p^n ∈ ℤ⧸p^nℤ can be uniquely
represented in the form 
   
-/
#check PadicInt.lift_spec


/- Proposition 1.4 : The F (x_1, … , x_n) be a polynomial with integer coeffients,
  and fix a prime number 
-/

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl



#check Subring.mk

theorem Prop1_4 (f : Type _) (f : Polynomial ℤ ) : (∀ v : ℕ, ∃ u : ℤ, (↑(p^v) : ℤ) ∣ Polynomial.eval u f) 
  ↔ ∃ y : ℤ_[p], Polynomial.eval y (f.ofSubring (fun xs => sorry)) = 0 := sorry

