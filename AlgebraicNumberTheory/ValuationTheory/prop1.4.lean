-- GOAL : Prove `aux1`, i.e., find `y n ∈ ℤ/p^n` forming an inverse limit s.t. `F (y n) = 0`.

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown

variable {p : ℕ} [Fact p.Prime]

-- The universal property of `ℤ_[p]` as projective limit. (Commutative Diagram)
#check PadicInt.lift_unique
#check PadicInt.lift_spec


open PadicInt
open BigOperators


section Prop_1_4_weaker

open Polynomial

lemma aux0
    {F : Polynomial ℤ} {x : ℕ → ℤ} {n : ℕ} {y : ZMod (p ^ n)} {k : ℕ} :
  F.eval₂ (Int.castRingHom (ZMod (p ^ n))) (x k : ZMod (p ^ n)) = 0 → Int.castRingHom (ZMod (p ^ n)) (x k : ZMod (p ^ n)) = y
  → (
    ∃z : ZMod (p ^ (n + 1)),
    ∃ι : ℕ → ℕ, -- x ∘ ι is a subseq of x
    Monotone ι ∧
    F.eval₂ (Int.castRingHom (ZMod (p ^ (n + 1)))) (x (ι k) : ZMod (p ^ (n + 1))) = 0 ∧ Int.castRingHom (ZMod (p ^ (n + 1))) (x (ι k) : ZMod (p ^ (n + 1))) = z
  ) := by sorry

lemma aux1
    {F : Polynomial ℤ} (h : ∀n : ℕ, ∃x : ZMod (p ^ n), F.eval₂ (Int.castRingHom (ZMod (p ^ n))) x = 0) :
  ∃y : (n : ℕ) → ZMod (p ^ n), (
      ∀n : ℕ,
        F.eval₂ (Int.castRingHom (ZMod (p ^ n))) (y n) = 0 
    ) ∧ (
      ∀(m n : ℕ) (mlen : m ≤ n), 
        ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m)) (y n) = y m
    ) := by
  sorry

example (m n : ℕ) (mlen : m ≤ n) : p^m ∣ p^n := pow_dvd_pow p mlen

-- A ring homomorphism `ℤ[X] → R` is determined by its value on `X`.
theorem aux2 {R : Type _} [Semiring R] {f g : Polynomial ℤ →+* R} (h : f X = g X) : f = g :=
  ringHom_ext' (RingHom.ext_int (RingHom.comp f C) (RingHom.comp g C)) h


theorem prop1_4_weaker
    {F : Polynomial ℤ} : 
  (∃x : ℤ_[p], F.eval₂ (Int.castRingHom ℤ_[p]) x = 0) ↔ (∀m : ℕ, ∃x : ZMod (p ^ m), F.eval₂ (Int.castRingHom (ZMod (p ^ m))) x = 0) := by
  constructor
  · rintro ⟨x, Fx⟩ m
    use (toZModPow m) x
    let Fxm := ext_of_toZModPow.mpr Fx m
    rw [(toZModPow m).map_zero, hom_eval₂,
      ← RingHom.ext_int (Int.castRingHom (ZMod (p ^ m))) (RingHom.comp (toZModPow m) (Int.castRingHom ℤ_[p]))] at Fxm
    exact Fxm
  · intro h
    -- use `aux1`
    rcases aux1 h with ⟨y, ⟨Fy, cpt⟩⟩ 
    let g : (n : ℕ) → Polynomial ℤ →+* ZMod (p ^ n) :=
      fun n ↦ eval₂RingHom (Int.castRingHom (ZMod (p ^ n))) (y n)
    have g_cpt : ∀ (m n : ℕ) (mlen : m ≤ n), RingHom.comp (ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m))) (g n) = g m := by
      intro m n mlen
      apply aux2
      simp only [RingHom.coe_comp, coe_eval₂RingHom, Function.comp_apply, eval₂_X, ZMod.castHom_apply]
      exact cpt m n mlen
    -- use PadicInt.limNthHom on `ℤ[X]`
    use lift g_cpt X
    rw [← ext_of_toZModPow]
    intro n
    rw [(toZModPow n).map_zero, hom_eval₂,
      ← RingHom.ext_int (Int.castRingHom (ZMod (p ^ n))) (RingHom.comp (toZModPow n) (Int.castRingHom ℤ_[p])),
      ← Fy n]
    congr
    have : y n = (g n) X := by simp only [coe_eval₂RingHom, eval₂_X]
    rw [this, (lift_spec g_cpt n).symm]
    simp only [RingHom.coe_comp, Function.comp_apply]




end Prop_1_4_weaker