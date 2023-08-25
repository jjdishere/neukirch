/- Seems like everything in this file goes well. For now. (I'm still defing things irrelavant to `ℤ_[p]`.)

Current goal: 
Define morphisms of type `R⟦X⟧ → S`, denoted `aux_eval₂` for the function version and `aux_eval₂hom` for the ring-hom version.
Then use `aux_eval₂hom` to define `ℤ⟦X⟧ → ℤ/p^n`, mapping `X → p`.
I want to replace `aux_` with `PowerSeries.`. Is that ok?
-/


import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Nilpotent

open PadicInt
open BigOperators


variable {p : ℕ} [Fact p.Prime]

section Prop_2_6


open PowerSeries

/- Question: can I define the notation for powerseries as bellow? 
As this notation haven't been defined but the similar one for Polynomial IS defined, I think there is some reason behind...
-/
-- scoped[PowerSeries] notation:9000 R "⟦X⟧ " => PowerSeries R

variable {R : Type u0} [CommRing R] {S : Type u1} [CommRing S]


-- For a nilpotent element `s : S`, assignment `X ↦ s` defines a ring homomorphism `R⟦X⟧ → S`
def aux_eval₂ (f : R →+* S) (s : nilradical S) (p : PowerSeries R) : S := by
  rcases s with ⟨s, s_prop⟩
  choose n sn0 using s_prop
  -- TODO : define `aux_eval₂ f s` as the sum of terms lower than `n`
  


def aux_eval₂hom (f : R →+* S) (s : nilradical S) : PowerSeries R →+* S where
  toFun := aux_eval₂ f s
  map_one' := _
  map_mul' := _
  map_zero' := _
  map_add' := _


-- `a` is nilpotent in `ℤ ⧸ a ^ n`.
lemma aux3 {a n : ℕ} : (a : ZMod (a ^ n)) ∈ nilradical (ZMod (a ^ n)) := by
  rw [mem_nilradical]; use n; exact Trans.trans (Nat.cast_pow a n).symm (ZMod.nat_cast_self (a ^ n))

-- The homomorphism `ℤ⟦X⟧ → ℤ⧸a^n` mapping `X` to `a`.
def ZMod.pow_ofPowerSeriesZ {a : ℕ} : (n : ℕ) → PowerSeries ℤ →+* ZMod (a ^ n) := 
  fun n ↦ aux_eval₂hom (Int.castRingHom (ZMod (a^n))) {
    val := a
    property := aux3
  }

lemma ZMod.pow_ofPowerSeriesZ_compat : 
  ∀ (m n : ℕ) (mlen : m ≤ n), 
    RingHom.comp (ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m))) (ZMod.pow_ofPowerSeriesZ n) = (ZMod.pow_ofPowerSeriesZ m) := by
  sorry

-- Define the canonical isomorphism `ℤ⟦X⟧ ⧸ (X - p) ≃ ℤ_[p]` using the universal property of `ℤ_[p]`.
def PadicInt.ofPowerSeriesZ : PowerSeries ℤ →+* ℤ_[p] := lift ZMod.pow_ofPowerSeriesZ_compat

theorem PadicInt.ofPowerSeriesZ_surjective : Function.Surjective (ofPowerSeriesZ : PowerSeries ℤ → ℤ_[p]) := by
  sorry

theorem PadicInt.ker_ofPowerSeries :
  RingHom.ker (ofPowerSeriesZ : PowerSeries ℤ →+* ℤ_[p]) = Ideal.span {(X : PowerSeries ℤ) - p} := by
  ext f
  constructor
  · sorry
  · sorry



end Prop_2_6



