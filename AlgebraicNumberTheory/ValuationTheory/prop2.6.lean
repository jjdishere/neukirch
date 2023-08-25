/- 
Current goal: show that `eval₂` is a ring morphism, i.e. `eval₂hom`
maybe i shouldn't use `trunc` in the def of `eval₂`? 
-/


import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Nilpotent

open PadicInt
open BigOperators


variable {p : ℕ} [Fact p.Prime]

noncomputable section Prop_2_6
-- can't def `PowerSeries.finsum` without the `noncomputable`


namespace PowerSeries

/- Question: can I define the notation for powerseries as bellow? 
As this notation haven't been defined but the similar one for Polynomial IS defined, I think there is some reason behind...
-/
scoped[PowerSeries] notation:9000 R "⟦X⟧ " => PowerSeries R

variable {R : Type u0} [CommRing R] {S : Type u1} [CommRing S]

def finsum (n : ℕ) (φ : R⟦X⟧) (f : ℕ → R → S) : S := (φ.trunc n).sum f

-- For a nilpotent element `s : S`, assignment `X ↦ s` defines a ring homomorphism `R⟦X⟧ → S`

variable (f : R →+* S) (s : nilradical S)

def eval₂ (φ : R⟦X⟧) : S := by
  rcases s with ⟨s, s_prop⟩
  choose n _ using s_prop
  exact (φ.trunc n).eval₂ f s


theorem eval₂_zero : eval₂ f s 0 = 0 := by
  simp only [eval₂, Submodule.zero_eq_bot, Ideal.mem_bot, trunc_zero, Polynomial.eval₂_zero]



theorem eval₂_one : eval₂ f s 1 = 1 := by
  simp only [eval₂]
  -- the goal turns into a term with  `classical.choose` in it. how to deal with?
  sorry


def eval₂hom : R⟦X⟧ →+* S where
  toFun := eval₂ _ _
  map_one' := eval₂_one f s
  map_mul' := _
  map_zero' := eval₂_zero f s
  map_add' := _



end PowerSeries


open PowerSeries

-- `a` is nilpotent in `ℤ ⧸ a ^ n`.
lemma aux3 {a n : ℕ} : (a : ZMod (a ^ n)) ∈ nilradical (ZMod (a ^ n)) := by
  rw [mem_nilradical]
  use n
  exact Trans.trans (Nat.cast_pow a n).symm (ZMod.nat_cast_self (a ^ n))


-- The homomorphism `ℤ⟦X⟧ → ℤ ⧸ a ^ n` mapping `X` to `a`.
def ZMod.pow_ofPowerSeriesZ {a : ℕ} : (n : ℕ) → PowerSeries ℤ →+* ZMod (a ^ n) := 
  fun n ↦ eval₂hom (Int.castRingHom (ZMod (a^n))) {
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


