import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

--set_option maxHeartbeats 0

open Ideal

open NumberField

open IsDedekindDomain

-- Extension of Dedekind Domains

-- Proposition 8.1
#check integralClosure.isDedekindDomain

-- Proposition 8.2
#check sum_ramification_inertia

-- Proposition 8.3
#check KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk



#check map_le_of_le_comap
#check le_comap_of_map_le

variable {R : Type _} [CommRing R] {S : Type _} [CommRing S] (f : R →+* S)

variable {K : Type _} [Field K] [NumberField K] {L : Type _} [Field L][NumberField L] [Algebra K L]

class Ideal.IsUnramified (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdxeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  separable: ∀ P : Ideal S, P.IsMaximal → (h : p ≤ comap f P) →
    @IsSeparable (R ⧸ p) (S ⧸ P) _ _ (Quotient.algebraQuotientOfLeComap h)

class Ideal.TotallySplit (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdx_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  inertiaDeg_eq_one : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → inertiaDeg f p P = 1

class Ideal.Nonsplit (p : Ideal R) [p.IsMaximal] : Prop where
  nonsplit : ∀ P1 P2 : Ideal S, p = comap f P1 → p = comap f P2 → P1 = P2



attribute [local instance] NumberField.ringOfIntegersAlgebra

-- Proposition 8.4
theorem OnlyFinitelyManyPrimeidealsRamified [IsSeparable K L] :
  Set.Finite { p : Ideal (𝓞 K) | ∀ h : p.IsMaximal, ¬ p.IsUnramified (algebraMap (𝓞 K) (𝓞 L)) } := sorry



#check legendreSym

instance {p : ℕ} [hpp : Fact (Nat.Prime p)] : IsMaximal (Submodule.span ℤ {(p : ℤ)}) :=
  PrincipalIdealRing.isMaximal_of_irreducible
  (Iff.mpr PrincipalIdealRing.irreducible_iff_prime ((Iff.mp Nat.prime_iff_prime_int (Fact.elim hpp))))

namespace Polynomial

-- Proposition 8.5
theorem IsQuadratic_iff_TotallySplit {a : ℤ} {p : ℕ} (ha : Squarefree a) (hp : p ≠ 2) [Fact (Nat.Prime p)]
  (hpa : IsCoprime a p) : legendreSym p a = 1 ↔
  TotallySplit (algebraMap ℤ (𝓞 (SplittingField (X ^ 2 - (a : ℚ[X]))))) (Submodule.span ℤ {(p : ℤ)}) := sorry

end Polynomial

-- Theorem 8.6
#check legendreSym.quadratic_reciprocity

#check legendreSym.at_neg_one

#check legendreSym.at_two



-- Hilbert's Ramification Theory
#check L ≃ₐ[K] L -- Gal(L/K)

def GalRingMap (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L)  := {
  toFun := fun x ↦ ⟨σ x, RingOfIntegers.map_mem (σ.toAlgHom).toRatAlgHom x⟩
  map_one' := by simp only [OneMemClass.coe_one, map_one]; rfl
  map_mul' := by simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring,
    _root_.map_mul, Submonoid.mk_mul_mk, Subtype.forall, implies_true, forall_const]
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero]; rfl
  map_add' := by simp only [Subsemiring.coe_add, Subalgebra.coe_toSubsemiring, map_add,
    AddMemClass.mk_add_mk, Subtype.forall, implies_true, forall_const]
}

-- Propsition 9.1
theorem PrimeIdealsAreConjugatesOfEachother [IsGalois K L] {p : Ideal (𝓞 K)} {P1 P2 : Ideal (𝓞 L)} [P1.IsPrime]
  [P2.IsPrime] (h1 : p = comap (algebraMap (𝓞 K) (𝓞 L)) P1) (h2 : p = comap (algebraMap (𝓞 K) (𝓞 L)) P2) :
  ∃ σ : L ≃ₐ[K] L, map (GalRingMap σ) P1 = P2  := sorry



-- A finite extension of a number field is a number field.
theorem FiniteExtensionOfANumberFieldIsANumberField (K : Type _) [Field K] [NumberField K]
    (L : Type _) [Field L] [Algebra K L][FiniteDimensional K L]: NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional := by
    have := charZero_of_injective_algebraMap (algebraMap K L).injective
    apply Module.Finite.trans K L

-- Any Extension between Number Fields is Finite
theorem ExtensionBetweenNumberFieldsIsFinite (K : Type _) [Field K] [NumberField K] (L : Type _) [Field L]
    [NumberField L] [Algebra K L] : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L

-- Any Extension between Ring Of Integers is Integral
theorem ExtensionBetweenringOfIntegersIsIntegral (K : Type _) [Field K] [NumberField K] (L : Type _)
    [Field L] [NumberField L] [Algebra K L] : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  fun x ↦ @isIntegral_tower_top_of_isIntegral ℤ (𝓞 K) (𝓞 L) _ _ _ _ _ _
  (IsScalarTower.of_ring_hom (RingHom.toIntAlgHom (algebraMap (𝓞 K) (𝓞 L)))) _ (integralClosure.isIntegral x)


def PrimeIdealBelow (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
  (P : Ideal (𝓞 L)) : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P

theorem PrimeIdealBelow_le_Comap (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
    (P : Ideal (𝓞 L)) : PrimeIdealBelow K P ≤ comap (algebraMap (𝓞 K) (𝓞 L)) P := by
  simp only [PrimeIdealBelow, le_refl]

instance PrimeIdealBelow_IsPrime (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
    (P : Ideal (𝓞 L)) [P.IsPrime] : IsPrime (PrimeIdealBelow K P) :=
  Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))

instance MaximalIdealBelow_IsMaximal (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] : IsMaximal (PrimeIdealBelow K P) :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (ExtensionBetweenringOfIntegersIsIntegral K L) P

theorem exists_ideal_over_maximal_of_ringOfIntegers (L : Type _) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (p : Ideal (𝓞 K)) [p.IsMaximal] : ∃ (P : Ideal (𝓞 L)),
    IsMaximal P ∧ comap (algebraMap (𝓞 K) (𝓞 L)) P = p := by
  refine' Ideal.exists_ideal_over_maximal_of_isIntegral (ExtensionBetweenringOfIntegersIsIntegral K L) p _
  have hkl: RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ := by
    refine' (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr _
    intro x hx
    have h: (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
    rw[hx] at h; dsimp at h
    rw[← RingHom.map_zero (algebraMap K L)] at h
    exact (Subalgebra.coe_eq_zero (𝓞 K)).mp ((NoZeroSMulDivisors.algebraMap_injective K L) h)
  simp only [hkl, bot_le]

noncomputable def ramificationIdx_of_IsGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type _) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : ℕ := by
  have h : ∃ n : ℕ, ∃ P : Ideal (𝓞 L), PrimeIdealBelow K P = p ∧ n = ramificationIdx _ p P := by
    rcases exists_ideal_over_maximal_of_ringOfIntegers L p with ⟨P, _ ,hp⟩
    exact ⟨ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P, P, hp, rfl⟩
  exact @Nat.find _ (Classical.decPred _) h

theorem ramificationIdx_eq_ramificationIdx_of_IsGalois (K : Type _) [Field K] [NumberField K]
  [Algebra K L] [IsGalois K L] (P : Ideal (𝓞 L)) [P.IsMaximal] :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (PrimeIdealBelow K P) P =
    ramificationIdx_of_IsGalois (PrimeIdealBelow K P) L := sorry

noncomputable def inertiaDeg_of_IsGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type _) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : ℕ := by
  have h : ∃ n : ℕ, ∃ P : Ideal (𝓞 L), PrimeIdealBelow K P = p ∧ n = inertiaDeg _ p P := by
    rcases exists_ideal_over_maximal_of_ringOfIntegers L p with ⟨P, _ ,hp⟩
    exact ⟨inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P, P, hp, rfl⟩
  exact @Nat.find _ (Classical.decPred _) h

theorem inertiaDeg_eq_inertiaDeg_of_IsGalois (K : Type _) [Field K] [NumberField K]
  [Algebra K L] [IsGalois K L] (P : Ideal (𝓞 L)) [P.IsMaximal] :
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) (PrimeIdealBelow K P) P =
    inertiaDeg_of_IsGalois (PrimeIdealBelow K P) L := sorry



-- Definition 9.2
variable (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]

def DecompositionGroup [IsGalois K L] (P : Ideal (𝓞 L)): Subgroup (L ≃ₐ[K] L) := {
  carrier := { σ : L ≃ₐ[K] L | map (GalRingMap σ) P = P}
  mul_mem' := by
    intro σ τ hs ht; dsimp
    have hmul: GalRingMap (σ * τ) = RingHom.comp (GalRingMap σ) (GalRingMap τ) := rfl
    rw[hmul, ← map_map, ht, hs]
  one_mem' := map_id P
  inv_mem' := by
    intro σ hs
    calc
      _ = map (GalRingMap σ⁻¹) (map (GalRingMap σ) P) := by rw[hs]
      _ = map ((GalRingMap (σ⁻¹ * σ))) P := by apply map_map
      _ = map (GalRingMap 1) P := by rw[mul_left_inv σ]
      _ = P := map_id P
}

def DecompositionField (P : Ideal (𝓞 L)) : IntermediateField K L :=
  IntermediateField.fixedField (DecompositionGroup K P)

-- DecompositionField is a Number Field
instance DecompositionField.NumberField (P : Ideal (𝓞 L)): NumberField (DecompositionField K P) := by
  have := ExtensionBetweenNumberFieldsIsFinite K L
  have := IntermediateField.finiteDimensional_left (DecompositionField K P)
  apply FiniteExtensionOfANumberFieldIsANumberField K (DecompositionField K P)

def DecompositionIdeal (P : Ideal (𝓞 L)) : Ideal (𝓞 (DecompositionField K P)) :=
  PrimeIdealBelow (DecompositionField K P) P

instance DecompositionFieldIdealIsMaximal (P : Ideal (𝓞 L)) [P.IsMaximal] :
    IsMaximal ((DecompositionIdeal K P)) := by apply MaximalIdealBelow_IsMaximal



-- Proposition 9.3
theorem DecompositionIdeal.Nonsplit (P : Ideal (𝓞 L)) [P.IsMaximal] :
  @Nonsplit _ _ _ _ (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) (DecompositionIdeal K P)
  (DecompositionFieldIdealIsMaximal K P) := sorry

theorem ramificationIdx_of_DecompositionIdeal (P : Ideal (𝓞 L)) [P.IsMaximal] :
  ramificationIdx (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) (DecompositionIdeal K P) P =
  ramificationIdx_of_IsGalois (PrimeIdealBelow K P) L := sorry

theorem inertiaDeg_of_DecompositionIdeal (P : Ideal (𝓞 L)) [P.IsMaximal] :
  @inertiaDeg _ _ _ _ (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) (DecompositionIdeal K P) P
  (DecompositionFieldIdealIsMaximal K P) =
  inertiaDeg_of_IsGalois (PrimeIdealBelow K P) L := sorry

theorem DecompositionIdeal.TotallySplit (P : Ideal (𝓞 L)) [P.IsMaximal] :
  TotallySplit (algebraMap (𝓞 K) (𝓞 (DecompositionField K P))) (PrimeIdealBelow K P) := sorry



instance (P : Ideal (𝓞 L)) : Algebra ((𝓞 K) ⧸ PrimeIdealBelow K P) ((𝓞 L) ⧸ P) :=
  Quotient.algebraQuotientOfLeComap (PrimeIdealBelow_le_Comap K P)

noncomputable instance (p : Ideal R) [p.IsMaximal] : Field (R ⧸ p) := Quotient.field p

-- Proposition 9.4
instance ExtensionOfResidueFieldsIsNormal (P : Ideal (𝓞 L)) [P.IsMaximal] :
  Normal ((𝓞 K) ⧸ (PrimeIdealBelow K P)) ((𝓞 L) ⧸ P) := sorry
