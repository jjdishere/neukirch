/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

open Ideal NumberField IsDedekindDomain



-- Proposition 8.1
#check integralClosure.isDedekindDomain

-- Proposition 8.2
#check sum_ramification_inertia

-- Proposition 8.3
#check KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk

#check finprod_heightOneSpectrum_factorization



#check map_le_of_le_comap
#check le_comap_of_map_le

variable {R : Type _} [CommRing R] {S : Type _} [CommRing S] (f : R →+* S)

class Ideal.IsUnramified (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdxeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  separable: ∀ P : Ideal S, P.IsMaximal → (h : p ≤ comap f P) →
    @IsSeparable (R ⧸ p) (S ⧸ P) _ _ (Quotient.algebraQuotientOfLeComap h)

class Ideal.TotallySplit (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdx_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  inertiaDeg_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → inertiaDeg f p P = 1

class Ideal.Nonsplit (p : Ideal R) : Prop where
  nonsplit : ∀ P1 P2 : Ideal S, p = comap f P1 → p = comap f P2 → P1 = P2



#check IsIntegralClosure.isNoetherian

-- Proposition 8.4
theorem OnlyFinitelyManyPrimeidealsRamified (R : Type _) [CommRing R] [IsDomain R]
  {S : Type _} [CommRing S] [IsDomain S] [Algebra R S] [IsDedekindDomain R]
  (K L : Type _) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsSeparable K L]
  [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [IsIntegralClosure S R L] :
  Set.Finite { p : HeightOneSpectrum R | ¬ (p.asIdeal).IsUnramified (algebraMap R S) } := sorry



#check legendreSym

instance {p : ℕ} [hpp : Fact (Nat.Prime p)] : IsMaximal (Submodule.span ℤ {(p : ℤ)}) :=
  PrincipalIdealRing.isMaximal_of_irreducible
  (Iff.mpr PrincipalIdealRing.irreducible_iff_prime ((Iff.mp Nat.prime_iff_prime_int (Fact.elim hpp))))

open Polynomial

-- Proposition 8.5
theorem IsQuadratic_iff_TotallySplit {a : ℤ} {p : ℕ} (ha : Squarefree a) (hp : p ≠ 2) [Fact (Nat.Prime p)]
(hpa : IsCoprime a p) : legendreSym p a = 1 ↔
TotallySplit (algebraMap ℤ (𝓞 (SplittingField (X ^ 2 - (a : ℚ[X]))))) (Submodule.span ℤ {(p : ℤ)}) := sorry



-- Theorem 8.6
#check legendreSym.quadratic_reciprocity

#check legendreSym.at_neg_one

#check legendreSym.at_two

