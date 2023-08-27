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
import Mathlib.Deprecated.Subring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

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

-- lemma Zsubring {_ : Set ℤ_[p]} : IsSubring ℤ := sorry
-- ≡ 

-- theorem Prop1_4 (f : Type _) (f : Polynomial ℤ): (∀ v : ℕ, ∃ u : ℤ, (↑(p^v) : ℤ) ∣ Polynomial.eval u f) 
--   ↔ ∃ y : ℤ_[p], Polynomial.eval y (Polynomial.ofSubring ℤ f) = 0 := sorry


theorem prop1_4
  (F : Polynomial ℤ) : ∀v : ℕ, Polynomial.eval x F = (0 : ZMod (p ^ v)) 
  ↔ ∃x : ℤ_[p], Polynomial.eval x (Polynomial.map (Int.castRingHom ℤ_[p]) F) = 0 
  := by sorry 