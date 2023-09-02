/- 
Current goal: show that `eval₂` is a ring morphism, i.e. `eval₂RingHom`
QUESTION: on `line 89`
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
variable (f : R →+* S) (s : nilradical S) (φ : R⟦X⟧)

def trunc_X (n : ℕ) : trunc (n + 2) (X : R⟦X⟧) = Polynomial.X := by
  rw [← Polynomial.coeff_inj]
  ext k
  rw [coeff_trunc _ _ _]
  sorry


def truncAddMonoidHom (n : ℕ): R⟦X⟧ →+ Polynomial R where
  toFun := trunc n
  map_zero' := trunc_zero _
  map_add' := trunc_add _

#check lt_or_eq_of_le

theorem trunc_sub {φ : R⟦X⟧} {m n : ℕ} (h : m ≤ n) : φ.trunc n - φ.trunc m = (Finset.Ico m n).sum fun k ↦ Polynomial.monomial k (coeff R k φ) := by
  apply Polynomial.coeff_inj.mp
  ext k
  rw [Polynomial.coeff_sub, Polynomial.finset_sum_coeff] 
  -- rw [Polynomial.coeff_monomial]
  -- how to rw a term in a finsum?
  rw [coeff_trunc, coeff_trunc]
  by_cases hkm : k < m
  · simp only [lt_of_lt_of_le hkm h, ite_true, hkm, sub_self, ge_iff_le]
    -- show the poly on the right has no terms of deg < m
    sorry
    

  by_cases hkn : k < n
  · simp only [hkn, ite_true, hkm, ite_false, sub_zero, ge_iff_le]
    sorry
  · simp only [hkn, ite_false, hkm, sub_self, ge_iff_le]
    sorry

#check sub_eq_iff_eq_add
#check sub_eq_iff_eq_add'
theorem trunc_sub' {φ : R⟦X⟧} {m n : ℕ} (h : m ≤ n) : φ.trunc n = φ.trunc m + (Finset.Ico m n).sum fun k ↦ Polynomial.monomial k (coeff R k φ) := by
  apply sub_eq_iff_eq_add'.mp
  exact trunc_sub h

-- theorem aux4 (k : ℕ) : (Polynomial.monomial k) ((coeff R k) φ) = ((coeff R k) φ) * (Polynomial.X : Polynomial R)^k := by

def sum (n : ℕ) (φ : R⟦X⟧) (F : ℕ → R → S) : S := (φ.trunc n).sum F

def eval₂ (f : R →+* S) (s : nilradical S) (φ : R⟦X⟧) : S := (φ.trunc (choose s.2)).eval₂ f s.1

#check self_eq_add_right
#check Polynomial.eval₂_add
theorem eval₂_eq_sum {f : R →+* S} {s : nilradical S} {φ : R⟦X⟧} {n : ℕ} :
  φ.eval₂ f s = φ.sum (choose s.2) fun e a ↦ f a * s.1 ^ e := by
  sorry

theorem eval₂_eq_sum' {f : R →+* S} {s : nilradical S} {φ : R⟦X⟧} {n : ℕ} (hn : n ≥ (choose s.2)) :
  φ.eval₂ f s = φ.sum n fun e a ↦ f a * s.1 ^ e := by
  rw [eval₂, sum, ← Polynomial.eval₂_eq_sum, trunc_sub' hn,
      Polynomial.eval₂_add, self_eq_add_right]
  -- rw [Polynomial.eval₂_eq_sum]
  sorry

-- can i use `(n : ℕ) {h : a hypothesis on n}`?
theorem eval₂_eq_Polynomial_eval₂ {f : R →+* S} {s : nilradical S} {φ : R⟦X⟧} {n : ℕ} (hn : n ≥ (choose s.2)) :
  φ.eval₂ f s = (φ.trunc n).eval₂ f s.1 := by
  sorry
  

theorem eval₂_congr {f g : R →+* S} {s t : nilradical S} {φ ψ : R⟦X⟧} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl

@[simp]
theorem eval₂_at_zero {φ : R⟦X⟧} : φ.eval₂ f ⟨0, IsNilpotent.zero⟩ = f (coeff R 0 φ) := by
  simp [eval₂]

@[simp]
theorem eval₂_zero : (0 : R⟦X⟧).eval₂ f s = 0 := by
  simp only [eval₂, Submodule.zero_eq_bot, Ideal.mem_bot, trunc_zero, Polynomial.eval₂_zero]

example (n : ℕ) : n + 1 ≥ n := Nat.le_add_right n 1

#check Polynomial.eval₂_C
@[simp]
theorem eval₂_C {a : R} : (C R a).eval₂ f s = f a := by
  rw [eval₂_eq_sum' (Nat.le_add_right (choose s.2) 1), sum, trunc_C]
  simp only [map_zero, pow_zero, mul_one, Polynomial.sum_C_index]

@[simp]
theorem eval₂_X : X.eval₂ f s = s := by
  rw [eval₂_eq_sum' (Nat.le_add_right (choose s.2) 2), sum, trunc_X]
  simp only [map_zero, pow_one, zero_mul, Polynomial.sum_X_index, map_one, one_mul]

@[simp]
theorem eval₂_monomial {n : ℕ} {a : R} : (monomial R n a).eval₂ f s = f a * s.1 ^ n := by
  -- simp [eval₂_eq_sum]
  sorry

@[simp]
theorem eval₂_X_pow {n : ℕ} : (X ^ n : R⟦X⟧).eval₂ f s = s.1 ^ n := by
  sorry

@[simp]
theorem eval₂_add (ψ : R⟦X⟧): (φ + ψ).eval₂ f s = φ.eval₂ f s + ψ.eval₂ f s := by
  rw [eval₂, eval₂, eval₂,
      ← Polynomial.eval₂_add, trunc_add]

def eval₂AddMonoidHom : R⟦X⟧ →+ S where
  toFun := eval₂ f s
  map_zero' := eval₂_zero _ _
  map_add' := eval₂_add _ _

#check PowerSeries.C R (1 : R)
#check Polynomial.C (1 : R)
@[simp]
theorem eval₂_one : (1 : R⟦X⟧).eval₂ f s = 1 := by
  have : (1 : R⟦X⟧) = C R (1 : R) := by rfl
  rw [this, eval₂_C, f.map_one]

@[simp]
theorem eval₂_mul {ψ : R⟦X⟧} : (φ * ψ).eval₂ f s = φ.eval₂ f s * ψ.eval₂ f s := by
  sorry

-- For a nilpotent element `s : S`, assignment `X ↦ s` defines a ring homomorphism `R⟦X⟧ → S`
def eval₂RingHom : R⟦X⟧ →+* S := {
  eval₂AddMonoidHom f s with
  map_one' := eval₂_one _ _
  map_mul' := eval₂_mul _ _
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

