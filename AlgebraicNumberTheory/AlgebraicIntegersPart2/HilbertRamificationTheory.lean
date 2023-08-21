/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.FieldTheory.Galois
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.FieldTheory.IntermediateField
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.Factorization

import AlgebraicNumberTheory.AlgebraicIntegersPart2.ExtensionOfDedekindDomains

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option synthInstance.maxHeartbeats 100000

section Galois

open IntermediateField Subgroup AlgEquiv MonoidHom

variable {K : Type _} [Field K] {L : Type _} [Field L] [Algebra K L] [FiniteDimensional K L]


#check L ≃ₐ[K] L -- Gal(L/K)

#check IsGalois.intermediateFieldEquivSubgroup --Galois correspondence

#check IsGalois.tfae -- Equivalent characterizations of a Galois extension of finite degree

noncomputable instance (H : Subgroup (L ≃ₐ[K] L)) : DecidablePred (· ∈ H) := Classical.decPred _

-- For a subgroup H of Gal(L/K), H ≃* Gal(L/Inv(H))
instance Subgroup_eq_fixingSubgroup (H : Subgroup (L ≃ₐ[K] L)) :
H ≃* (L ≃ₐ[fixedField H] L) := by
  have h := fixingSubgroupEquiv (fixedField H)
  rw[fixingSubgroup_fixedField H] at h
  exact h

-- If H is a Normal Subgroup of Gal(L/K), then the Fixed Field of H is Galois over K
instance IsGalois.Normal_Subgroup_tower_bot_intermediateField [IsGalois K L]
  (H : Subgroup (L ≃ₐ[K] L)) [Normal H] : IsGalois K (fixedField H) := sorry

-- Furthermore, if E is the Fixed Field of H, then Gal(L/K)/H ≃* Gal(E/K)
theorem IsGalois.Normal_Galois_Group [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) [Normal H] :
    (L ≃ₐ[K] L) ⧸ H ≃* ((fixedField H) ≃ₐ[K] (fixedField H)) := by
  have h : H = ker (restrictNormalHom (fixedField H)) := by
    apply (Eq.symm (fixingSubgroup_fixedField H)).trans
    ext σ
    refine' (((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).trans _).trans AlgEquiv.ext_iff.symm).trans 
      (mem_ker (restrictNormalHom (fixedField H))).symm
    constructor
    intro h ⟨x, hx⟩
    apply Subtype.val_inj.mp
    apply (restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩).trans (h x hx)
    intro h x hx
    dsimp
    have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ x :=
      restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
    rw[← hs]
    apply Subtype.val_inj.mpr (h ⟨x, hx⟩)
  apply (QuotientGroup.quotientMulEquivOfEq h).trans
  apply QuotientGroup.quotientKerEquivOfSurjective (restrictNormalHom (fixedField H))
    (@restrictNormalHom_surjective K (fixedField H) _ _ _ L _ _ _ _ _ _)



-- A MulEquiv maps a Normal Subgroup to a Normal Subgroup
lemma Subgroup.map_equiv_normal {G G': Type _} [Group G] [Group G'] (f : G ≃* G')
    (H : Subgroup G) [hn: Normal H] : Normal (map f.toMonoidHom H) := by
  have h : map f.toMonoidHom ⊤ = ⊤ := map_top_of_surjective f (MulEquiv.surjective f)
  refine' normalizer_eq_top.mp _
  rw[← h, ← normalizer_eq_top.mpr hn, map_equiv_normalizer_eq H f]

end Galois



open Ideal Algebra

open scoped BigOperators

variable {R ι : Type _} [CommRing R]

noncomputable instance : DecidableEq ι := Classical.decEq ι

theorem Ideal.IsPrime.prod_mem {p : Ideal R} [hp : p.IsPrime] {s : Finset ι} {x : ι → R}
    (h : ∏ i in s, x i ∈ p) : ∃ i : s, x i ∈ p := by
  induction' s using Finset.induction_on with n s nns hn
  · rw[Finset.prod_empty] at h
    rw[IsEmpty.exists_iff]
    exact IsPrime.ne_top hp ((eq_top_iff_one p).mpr h)
  · rw[Finset.prod_insert nns] at h
    rcases IsPrime.mem_or_mem hp h with h|h
    use ⟨n, Finset.mem_insert_self n s⟩
    rcases hn h with ⟨i, hi⟩
    use ⟨i, Finset.mem_insert_of_mem i.2⟩
  
  

variable (K : Type _) [Field K] [NumberField K] (L : Type _) [Field L] [Algebra K L]

namespace NumberField



-- A finite extension of a number field is a number field.
theorem FiniteExtensionOfANumberFieldIsANumberField [FiniteDimensional K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional := by
    have := charZero_of_injective_algebraMap (algebraMap K L).injective
    apply Module.Finite.trans K L

variable [NumberField L]

-- Any Extension between Number Fields is Finite
instance Extension.FiniteDimensional : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

instance Extension_ringOfIntegers.isIntegralClosure : IsIntegralClosure (𝓞 L) (𝓞 K) L where
  algebraMap_injective' := IsFractionRing.injective (𝓞 L) L
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have hz : Algebra.IsIntegral ℤ (𝓞 K) := IsIntegral.of_finite
      exact CanLift.prf x (isIntegral_trans hz x hx)
    · intro ⟨⟨y,hy⟩, hxy⟩
      rw[← hxy]
      apply isIntegral_tower_top_of_isIntegral hy



attribute [local instance] NumberField.ringOfIntegersAlgebra

instance : Module (𝓞 K) (𝓞 L) := toModule

instance : SMul (𝓞 K) (𝓞 L) := toSMul

instance : IsScalarTower (𝓞 K) (𝓞 L) L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)



-- Any Extension between Ring Of Integers is Integral
instance Extension_ringOfIntegers.isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L

instance Extension_ringOfIntegers.isNoetherian : IsNoetherian (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)



variable {L : Type _} [Field L] [Algebra K L] (P : Ideal (𝓞 L))

abbrev PrimeIdealBelow : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P

lemma PrimeIdealBelow_le_Comap : PrimeIdealBelow K P ≤ comap (algebraMap (𝓞 K) (𝓞 L)) P := by
  simp only [PrimeIdealBelow, le_refl]

instance PrimeIdealBelow.IsPrime [P.IsPrime] : IsPrime (PrimeIdealBelow K P) :=
  IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))

variable [P.IsMaximal]

instance PrimeIdealBelow.IsMaximal [NumberField L]: IsMaximal (PrimeIdealBelow K P) :=
  isMaximal_comap_of_isIntegral_of_isMaximal (Extension_ringOfIntegers.isIntegral K L) P



noncomputable instance (p : Ideal R) [p.IsMaximal] : Field (R ⧸ p) := Quotient.field p

noncomputable instance [NumberField L] : Field ((𝓞 K) ⧸ (PrimeIdealBelow K P)) :=
  Quotient.field (PrimeIdealBelow K P)

noncomputable instance : Field ((𝓞 L) ⧸ P) := Quotient.field P

instance : Algebra ((𝓞 K) ⧸ PrimeIdealBelow K P) ((𝓞 L) ⧸ P) :=
  Quotient.algebraQuotientOfLeComap (PrimeIdealBelow_le_Comap K P)

instance : Module ((𝓞 K) ⧸ PrimeIdealBelow K P) ((𝓞 L) ⧸ P) := toModule

instance : SMul (𝓞 K) ((𝓞 K) ⧸ PrimeIdealBelow K P) :=
  Submodule.Quotient.instSMul (PrimeIdealBelow K P)

instance : Algebra (𝓞 K) ((𝓞 L) ⧸ P) := Quotient.algebra (𝓞 K)

instance : Module (𝓞 K) ((𝓞 L) ⧸ P) := toModule



variable [NumberField L] (P : Ideal (𝓞 L)) [P.IsMaximal]

instance : @IsScalarTower (𝓞 K) ((𝓞 K) ⧸ PrimeIdealBelow K P) ((𝓞 L) ⧸ P) _
  toSMul toSMul := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

instance : FiniteDimensional ((𝓞 K) ⧸ (PrimeIdealBelow K P)) ((𝓞 L) ⧸ P) :=
  IsNoetherian.iff_fg.mp <| isNoetherian_of_tower (𝓞 K) <|
    isNoetherian_of_surjective (𝓞 L) (Ideal.Quotient.mkₐ (𝓞 K) P).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective



variable {K}

-- Hilbert's Ramification Theory
def GalAlgEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) where
  toFun x := ⟨σ x, RingOfIntegers.map_mem σ.toAlgHom.toRatAlgHom x⟩
  invFun x := ⟨σ⁻¹ x, RingOfIntegers.map_mem σ⁻¹.toAlgHom.toRatAlgHom x⟩
  left_inv x := by
    have hs: (σ⁻¹ * σ) x = x := by rw[mul_left_inv, AlgEquiv.one_apply]
    exact SetCoe.ext hs
  right_inv x := by
    have hs: (σ * σ⁻¹) x = x := by rw[mul_right_inv, AlgEquiv.one_apply]
    exact SetCoe.ext hs
  map_mul' := by simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, Submonoid.mk_mul_mk,
    Subalgebra.coe_toSubsemiring, _root_.map_mul, Subtype.forall, implies_true, forall_const]
  map_add' := by simp only [Subsemiring.coe_add, Subalgebra.coe_toSubsemiring, map_add,
    AddMemClass.mk_add_mk, Subtype.forall, implies_true, forall_const]
  commutes' x := SetCoe.ext (AlgEquiv.commutes σ x)

def GalRingHom (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L) := (GalAlgEquiv σ).toAlgHom.toRingHom



-- Propsition 9.1
theorem IsMaximal_conjugates [IsGalois K L] {P : Ideal (𝓞 L)} [P.IsMaximal]
    {Q : Ideal (𝓞 L)} [hqm : Q.IsMaximal] (h : PrimeIdealBelow K P = PrimeIdealBelow K Q) :
    ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q := sorry



lemma exists_ideal_over_maximal_of_ringOfIntegers (L : Type _) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (p : Ideal (𝓞 K)) [p.IsMaximal] : ∃ (P : Ideal (𝓞 L)),
    IsMaximal P ∧ comap (algebraMap (𝓞 K) (𝓞 L)) P = p := by
  apply Ideal.exists_ideal_over_maximal_of_isIntegral (Extension_ringOfIntegers.isIntegral K L) p
  have hkl: RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ := by
    apply (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr
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

noncomputable def inertiaDeg_of_IsGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type _) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : ℕ := by
  have h : ∃ n : ℕ, ∃ P : Ideal (𝓞 L), PrimeIdealBelow K P = p ∧ n = inertiaDeg _ p P := by
    rcases exists_ideal_over_maximal_of_ringOfIntegers L p with ⟨P, _ ,hp⟩
    exact ⟨inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P, P, hp, rfl⟩
  exact @Nat.find _ (Classical.decPred _) h

variable (K)

#check IsDedekindDomain.ramificationIdx_eq_factors_count

#check finprod_count

#check finprod_heightOneSpectrum_factorization

open UniqueFactorizationMonoid

-- In the case of Galois extension, all ramification indices are equal.
theorem ramificationIdx_eq_ramificationIdx_of_IsGalois [IsGalois K L] :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (PrimeIdealBelow K P) P =
    ramificationIdx_of_IsGalois (PrimeIdealBelow K P) L := sorry

-- In the case of Galois extension, all inertia degrees are equal.
theorem inertiaDeg_eq_inertiaDeg_of_IsGalois [IsGalois K L]:
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) (PrimeIdealBelow K P) P =
    inertiaDeg_of_IsGalois (PrimeIdealBelow K P) L := sorry



-- Definition 9.2
def DecompositionGroup : Subgroup (L ≃ₐ[K] L) := {
  carrier := { σ : L ≃ₐ[K] L | map (GalRingHom σ) P = P}
  mul_mem' := by
    intro σ τ hs ht
    have hmul: GalRingHom (σ * τ) = RingHom.comp (GalRingHom σ) (GalRingHom τ) := rfl
    rw[Set.mem_setOf_eq, hmul, ← Ideal.map_map, ht, hs]
  one_mem' := map_id P
  inv_mem' := by
    intro σ hs
    calc
      _ = map (GalRingHom σ⁻¹) (map (GalRingHom σ) P) := by rw[hs]
      _ = map ((GalRingHom (σ⁻¹ * σ))) P := by apply Ideal.map_map
      _ = map (GalRingHom 1) P := by rw[mul_left_inv σ]
      _ = P := map_id P
}

variable (P : Ideal (𝓞 L))

def DecompositionField : IntermediateField K L := IntermediateField.fixedField (DecompositionGroup K P)

instance (priority := high) : Field (DecompositionField K P) :=
  SubfieldClass.toField (IntermediateField K L) (DecompositionField K P)

-- DecompositionField is a Number Field
instance (priority := high) DecompositionField_NumberField : NumberField (DecompositionField K P) :=
  FiniteExtensionOfANumberFieldIsANumberField K (DecompositionField K P)

def DecompositionIdeal : Ideal (𝓞 (DecompositionField K P)) :=
  PrimeIdealBelow (DecompositionField K P) P

variable [IsGalois K L] [P.IsMaximal]

instance DecompositionFieldIdealIsMaximal : IsMaximal ((DecompositionIdeal K P)) := by
  apply PrimeIdealBelow.IsMaximal



-- Proposition 9.3
theorem DecompositionIdeal.Nonsplit : Nonsplit (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L))
(DecompositionIdeal K P) := sorry

theorem ramificationIdx_of_DecompositionIdeal :
  ramificationIdx (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) (DecompositionIdeal K P) P =
  ramificationIdx_of_IsGalois (PrimeIdealBelow K P) L := sorry

theorem inertiaDeg_of_DecompositionIdeal :
  @inertiaDeg _ _ _ _ (algebraMap (𝓞 (DecompositionField K P)) (𝓞 L)) (DecompositionIdeal K P) P
  (DecompositionFieldIdealIsMaximal K P) = inertiaDeg_of_IsGalois (PrimeIdealBelow K P) L := sorry

theorem Extension_degree_over_DecompositionField : FiniteDimensional.finrank (DecompositionField K P) L
= (ramificationIdx_of_IsGalois (PrimeIdealBelow K P) L) *
(inertiaDeg_of_IsGalois (PrimeIdealBelow K P) L) := sorry

theorem DecompositionIdeal.TotallySplit :
  TotallySplit (algebraMap (𝓞 K) (𝓞 (DecompositionField K P))) (PrimeIdealBelow K P) := sorry



-- Proposition 9.4
instance Extension_of_Residue_Fields_is_Galois : IsGalois ((𝓞 K) ⧸ (PrimeIdealBelow K P)) ((𝓞 L) ⧸ P)
  := sorry


def DecompositionGaloisHom : MonoidHom (DecompositionGroup K P)
(((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ (PrimeIdealBelow K P)] ((𝓞 L) ⧸ P)) where
  toFun := fun ⟨σ, hs⟩ ↦ { quotientEquiv P P (GalAlgEquiv σ) (Eq.symm hs) with
    commutes' := by
      rintro ⟨x⟩
      calc
        _ = Quotient.mk (Submodule.quotientRel P) ((GalAlgEquiv σ) ((algebraMap (𝓞 K) (𝓞 L)) x)) := rfl
        _ = _ := by rw[AlgEquiv.commutes (GalAlgEquiv σ) x]; rfl
  }
  map_one' := by ext ⟨_⟩; rfl
  map_mul' := fun _ _ ↦ by ext ⟨_⟩; rfl

theorem DecompositionGaloisHom_surjective : Function.Surjective (DecompositionGaloisHom K P) := sorry



-- Definition 9.5
abbrev InertiaGroup' : Subgroup (DecompositionGroup K P) := MonoidHom.ker (DecompositionGaloisHom K P)

instance : Subgroup.Normal (InertiaGroup' K P) := by apply MonoidHom.normal_ker

def InertiaGroup : Subgroup (L ≃ₐ[DecompositionField K P] L) :=
  Subgroup.map (Subgroup_eq_fixingSubgroup (DecompositionGroup K P)).toMonoidHom (InertiaGroup' K P)

-- InertiaGroup is a Normal Subgroup of Gal(L/(DecompositionField K P))
instance InertiaGroup_Normal : Subgroup.Normal (InertiaGroup K P) :=
  Subgroup.map_equiv_normal (Subgroup_eq_fixingSubgroup (DecompositionGroup K P)) (InertiaGroup' K P)

def InertiaField : IntermediateField (DecompositionField K P) L :=
  IntermediateField.fixedField (InertiaGroup K P)

instance : Field (InertiaField K P) :=
  SubfieldClass.toField (IntermediateField (DecompositionField K P) L) (InertiaField K P)

-- InertiaField is a Number Field
instance InertiaField_NumberField : NumberField (InertiaField K P) :=
  @FiniteExtensionOfANumberFieldIsANumberField (DecompositionField K P) _ _ (InertiaField K P) _
  (IntermediateField.algebra (InertiaField K P)) _

instance : Algebra (DecompositionField K P) (InertiaField K P) :=
  Subalgebra.algebra (InertiaField K P).toSubalgebra

instance : Module (DecompositionField K P) (InertiaField K P) := toModule

def InertiaIdeal : Ideal (𝓞 (InertiaField K P)) := PrimeIdealBelow (InertiaField K P) P

instance : IsMaximal (InertiaIdeal K P) := PrimeIdealBelow.IsMaximal (InertiaField K P) P