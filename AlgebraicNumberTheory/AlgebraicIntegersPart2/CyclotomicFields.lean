/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.RingTheory.DedekindDomain.Factorization

import AlgebraicNumberTheory.AlgebraicIntegersPart2.ExtensionOfDedekindDomains

set_option autoImplicit false

set_option maxHeartbeats 0



open Ideal Polynomial NumberField

-- Proposition 10.1
#check IsCyclotomicExtension.discr_prime_pow_ne_two

-- Proposition 10.2
#check IsPrimitiveRoot.integralPowerBasis



variable (n p : ℕ+) (hpp : p.Prime)

variable {K : Type _} [Field K] [Algebra ℚ K] [IsCyclotomicExtension {n} ℚ K]

#check ord_proj[p] n

#check ord_compl[p] n

#check Nat.totient n

#check Nat.ModEq.pow_totient

lemma orderOf_MOD_eq_one {n} (a : ℕ) (ha : Nat.coprime a n) :
    a ^ orderOf (ZMod.unitOfCoprime a ha) ≡ 1 [MOD n] := by
  have h : ((a ^ orderOf (ZMod.unitOfCoprime a ha)) : ZMod n) = ((1 : ℕ) : (ZMod n)) := by calc
    _ = ↑(ZMod.unitOfCoprime a ha ^ orderOf (ZMod.unitOfCoprime a ha)) := by
      rw[Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]
    _ = _ := by rw[pow_orderOf_eq_one (ZMod.unitOfCoprime a ha), Units.val_one, Nat.cast_one]
  apply (ZMod.nat_cast_eq_nat_cast_iff _ 1 n).mp h

instance Nat.Prime_toMaximal : IsMaximal (Submodule.span ℤ {↑p}) :=
  PrincipalIdealRing.isMaximal_of_irreducible <|
    PrincipalIdealRing.irreducible_iff_prime.mpr (Nat.prime_iff_prime_int.mp hpp)

-- Proposition 10.3
theorem ramificationIdx_in_CyclotomicField (P : Ideal (𝓞 K))
  (hp : (Submodule.span ℤ {(p : ℤ)}) = comap (algebraMap ℤ (𝓞 K)) P) :
  ramificationIdx (algebraMap ℤ (𝓞 K)) (Submodule.span ℤ {(p : ℤ)}) P = 
  Nat.totient (ord_proj[p] n) := sorry

theorem inertiaDeg_in_CyclotomicField (P : Ideal (𝓞 K))
  (hp : (Submodule.span ℤ {(p : ℤ)}) = comap (algebraMap ℤ (𝓞 K)) P) :
  @inertiaDeg _ _ _ _ (algebraMap ℤ (𝓞 K)) (Submodule.span ℤ {(p : ℤ)}) P (Nat.Prime_toMaximal p hpp)
  = orderOf (ZMod.unitOfCoprime p (Nat.coprime_ord_compl hpp (PNat.ne_zero n))) := sorry

theorem TotallySplit_in_CyclotomicField (hp2 : p ≠ 2) :
  @TotallySplit _ _ _ _ (algebraMap ℤ (𝓞 K)) (Submodule.span ℤ {(p : ℤ)}) (Nat.Prime_toMaximal p hpp)
  ↔ p ≡ 1 [MOD n] := sorry

theorem ramified_in_CyclotomicField :
  @IsUnramified _ _ _ _ (algebraMap ℤ (𝓞 K)) (Submodule.span ℤ {(p : ℤ)}) (Nat.Prime_toMaximal p hpp) ↔
  ¬ p ∣n ∨ (p = 2 ∧ (padicValNat 2 n) = 1) := sorry

lemma prime_span_nonzero : (Submodule.span ℤ {(p : ℤ)}) ≠ 0 := by 
  simp only [submodule_span_eq, Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, 
    Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true]

theorem TotallySplit_iff_splits_into_even_primes (hpn : n.Prime) (hp2 : p ≠ 2) (hn2 : n ≠ 2) :
  @TotallySplit _ _ _ _ (algebraMap ℤ (𝓞 (SplittingField (X ^ 2 - ((ZMod.χ₄ p) * p : ℚ[X])))))
  (Submodule.span ℤ {(p : ℤ)}) (Nat.Prime_toMaximal p hpp) ↔
  Even (Finset.card (Set.Finite.toFinset (finite_factors (prime_span_nonzero p)))) := sorry
