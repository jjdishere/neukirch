/- 
Current goal: show that `eval₂` is a ring morphism, i.e. `eval₂RingHom`
-/


import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Nilpotent

open PadicInt


variable {p : ℕ} [Fact p.Prime]

noncomputable section Prop_2_6



namespace PowerSeries


/- This notation may not be used. -/
scoped[PowerSeries] notation:9000 R "⟦X⟧ " => PowerSeries R

section

open Classical

variable {R : Type _} [CommRing R] {S : Type _} [CommRing S]

def sum (n : ℕ) (φ : R⟦X⟧) (F : ℕ → R → S) : S := (φ.trunc n).sum F

variable (f : R →+* S) (s : nilradical S)

def eval₂ (φ : R⟦X⟧) : S := (φ.trunc (choose s.property)).eval₂ f s.val

theorem eval₂_eq_sum (φ : R⟦X⟧) : φ.eval₂ f s = φ.sum (choose s.2) fun e r ↦ f r * s.1 ^ e := by
  simp only [sum, eval₂, Polynomial.eval₂_eq_sum]

theorem eval₂_congr {f g : R →+* S} {s t : nilradical S} {φ ψ : R⟦X⟧} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl

-- @[simp]
-- theorem eval₂_at_zero : φ.eval₂ f ({0 IsNilpotent.zero} : nilradical S) = f (φ.coeff 0) := by

@[simp]
theorem eval₂_zero : (0 : R⟦X⟧).eval₂ f s = 0 := by
  simp only [eval₂, Submodule.zero_eq_bot, Ideal.mem_bot, trunc_zero, Polynomial.eval₂_zero]

@[simp]
theorem eval₂_C (a : R) : (C R a).eval₂ f s = f a := by
  simp only [eval₂]
  rw [trunc_C]
  -- how? `choose` is not necessarily `≥ 1`.
  -- possible solution: use `choose s.2 + 1` instead in the def
  sorry

@[simp]
theorem eval₂_X : X.eval₂ f s = s := by
  sorry
  -- similar porblem as the previous

@[simp]
theorem eval₂_monomial {n : ℕ} {a : R} : (monomial R n a).eval₂ f s = f a * s.1 ^ n := by
  simp [eval₂_eq_sum]
  sorry

@[simp]
theorem eval₂_X_pow {n : ℕ} : (X ^ n : R⟦X⟧).eval₂ f s = s.1 ^ n := by
  sorry

@[simp]
theorem eval₂_add {ψ : R⟦X⟧}: (φ + ψ).eval₂ f s = φ.eval₂ f s + ψ.eval₂ f s := by
  sorry

def eval₂AddMonoidHom : R⟦X⟧ →+ S where
  toFun := eval₂ f s
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

@[simp]
theorem eval₂_one : eval₂ f s 1 = 1 := by
  sorry

@[simp]
theorem eval₂_mul {ψ : R⟦X⟧} : (φ * ψ).eval₂ f s = φ.eval₂ f s * ψ.eval₂ f s := by
  sorry

-- For a nilpotent element `s : S`, assignment `X ↦ s` defines a ring homomorphism `R⟦X⟧ → S`
def eval₂RingHom : R⟦X⟧ →+* S := {
  eval₂AddMonoidHom f s with
  map_one' := eval₂_one _ _
  map_mul' := fun _ _ ↦ eval₂_mul _ _
}

end

end PowerSeries


open PowerSeries

-- `a` is nilpotent in `ℤ ⧸ a ^ n`.
lemma aux3 {a n : ℕ} : (a : ZMod (a ^ n)) ∈ nilradical (ZMod (a ^ n)) := by
  use n
  exact Trans.trans (Nat.cast_pow a n).symm (ZMod.nat_cast_self (a ^ n))


-- The homomorphism `ℤ⟦X⟧ → ℤ ⧸ a ^ n` mapping `X` to `a`.
def ZMod.pow_ofPowerSeriesZ {a : ℕ} : (n : ℕ) → PowerSeries ℤ →+* ZMod (a ^ n) := 
  fun n ↦ eval₂RingHom (Int.castRingHom (ZMod (a^n))) {
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

