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

open Ideal

open NumberField

open IsDedekindDomain

#check integralClosure.isDedekindDomain

#check sum_ramification_inertia

#check KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk

#check map_le_of_le_comap
#check le_comap_of_map_le

variable {R : Type _} [CommRing R] {S : Type _} [CommRing S] (f : R →+* S)

variable {K : Type _} [Field K] [NumberField K] {L : Type _} [Field L][NumberField L] [Algebra K L]

class Ideal.IsUnramified (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdxeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  separable: ∀ P : Ideal S, P.IsMaximal → (h : p ≤ comap f P) →
    @IsSeparable (R ⧸ p) (S ⧸ P) _ _ (Quotient.algebraQuotientOfLeComap h)

class Ideal.SplitCompletely (p : Ideal R) [p.IsMaximal] : Prop where
  ramificationIdxeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → ramificationIdx f p P = 1
  inertiaDegeqOne : ∀ P : Ideal S, P.IsMaximal → p ≤ comap f P → inertiaDeg f p P = 1

class Ideal.Nonsplit (p : Ideal R) [p.IsMaximal] : Prop where
  nonsplit : ∀ P1 P2 : Ideal S, p = comap f P1 → p = comap f P2 → P1 = P2

attribute [local instance] NumberField.ringOfIntegersAlgebra

theorem OnlyFinitelyManyPrimeidealsRamified [IsSeparable K L] :
  Set.Finite { p : Ideal (𝓞 K) | ∀ h : p.IsMaximal, ¬ p.IsUnramified (algebraMap (𝓞 K) (𝓞 L)) }
  := sorry

#check L ≃ₐ[K] L -- Gal(L/K)

#check NumberField.RingOfIntegers.map_mem

#check isIntegral_algEquiv

def GalRingMap (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L) := {
  toFun := by
    intro ⟨x, hx⟩
    have hsx: σ x ∈ 𝓞 L := by sorry
    exact ⟨σ x, hsx⟩
  map_one' := by simp only[OneMemClass.coe_one, map_one]; rfl
  map_mul' := by simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring,
    _root_.map_mul, Submonoid.mk_mul_mk, Subtype.forall, implies_true, forall_const]
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero]; rfl
  map_add' := by simp only [Subsemiring.coe_add, Subalgebra.coe_toSubsemiring, map_add,
    AddMemClass.mk_add_mk, Subtype.forall, implies_true, forall_const]
}

theorem PrimeIdealsAreConjugatesOfEachother [IsGalois K L] {p : Ideal (𝓞 K)} {P1 P2 : Ideal (𝓞 L)}
  [P1.IsPrime] [P2.IsPrime] (h1 : p = comap (algebraMap (𝓞 K) (𝓞 L)) P1) 
  (h2 : p = comap (algebraMap (𝓞 K) (𝓞 L)) P2) :
  ∃ σ : L ≃ₐ[K] L, map (GalRingMap σ) P1 = P2  := sorry

def DecompositionGroup [IsGalois K L] (P : Ideal (𝓞 L)) [P.IsPrime]  : Subgroup (L ≃ₐ[K] L) := {
  carrier := { σ : L ≃ₐ[K] L | map (GalRingMap σ) P = P}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry
}

def DecompositionField (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
  (P : Ideal (𝓞 L)) [P.IsPrime] : IntermediateField K L :=
  IntermediateField.fixedField (DecompositionGroup P)

#check IntermediateField.toField

#check IntermediateField.toSubfield

#check Subfield.toIntermediateField

#check IntermediateField.finiteDimensional_left


instance DecompositionFieldIsNumberField (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
  [IsGalois K L] (P : Ideal (𝓞 L)) [P.IsPrime] :
  @NumberField (DecompositionField K P) (IntermediateField.toField (DecompositionField K P)) where
  to_charZero := algebraRat.charZero { x // x ∈ DecompositionField K P }
  to_finiteDimensional := sorry


def DecompositionFieldIdeal (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L][IsGalois K L]
  (P : Ideal (𝓞 L)) [P.IsPrime] :
  Ideal (𝓞 (DecompositionField K P)) := comap (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) P

instance DecompositionFieldIdealIsPrime (K : Type _) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]
  [IsGalois K L] (P : Ideal (𝓞 L)) [P.IsPrime] :
  IsPrime (DecompositionFieldIdeal K P) := Ideal.IsPrime.comap (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L))