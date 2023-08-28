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

set_option synthInstance.maxHeartbeats 120000

attribute [local instance] NumberField.ringOfIntegersAlgebra



section Galois

open IntermediateField AlgEquiv MonoidHom QuotientGroup

variable {K :Type _} [Field K] {L :Type _} [Field L] [Algebra K L] [FiniteDimensional K L]

#check L ≃ₐ[K] L -- Gal(L/K)

@[local instance]
noncomputable instance (H : Subgroup (L ≃ₐ[K] L)) : DecidablePred (· ∈ H) := Classical.decPred _

/- For a subgroup `H` of `Gal(L/K)`, `H ≃* Gal(L/Inv(H))`. -/
instance IntermediateField.Subgroup_eq_fixingSubgroup (H : Subgroup (L ≃ₐ[K] L)) : 
    H ≃* (L ≃ₐ[fixedField H] L) := by
  have h := fixingSubgroupEquiv (fixedField H)
  rw[fixingSubgroup_fixedField H] at h
  exact h

/- The `AlgEquiv` induced by an `AlgHom` from the domain of definition to the `fieldRange`. -/
noncomputable def AlgHom.fieldRange_toAlgEquiv {E : IntermediateField K L} (σ : E →ₐ[K] L) : 
    E ≃ₐ[K] σ.fieldRange where
  toFun x := ⟨σ x, by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]⟩
  invFun y := Classical.choose (AlgHom.mem_fieldRange.mp y.2)
  left_inv x := by
    have h : σ x ∈ σ.fieldRange := by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]
    have hs : Function.Injective σ := RingHom.injective σ
    exact hs (Classical.choose_spec (AlgHom.mem_fieldRange.mp h))
  right_inv y := Subtype.val_inj.mp (Classical.choose_spec (mem_fieldRange.mp y.2))
  map_mul' x y := by simp only [_root_.map_mul, fieldRange_toSubalgebra, Submonoid.mk_mul_mk]
  map_add' x y := by simp only [_root_.map_add, fieldRange_toSubalgebra, AddMemClass.mk_add_mk]
  commutes' x := Subtype.val_inj.mp (by simp only [AlgHom.commutes]; rfl)

theorem normalClosure.eq_bot_of_invariant_under_embedding [Normal K L] (E : IntermediateField K L) 
    (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : normalClosure K E L = ⊥ := by
  refine' le_antisymm _ bot_le
  intro x hx
  rw[normalClosure, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring, mem_toSubfield] at hx 
  apply (mem_restrictScalars K).mp
  rw[restrictScalars_bot_eq_self E]
  apply iSup_le (fun σ ↦ Eq.le (h σ)) hx

/- If `E` is an intermediateField of a normal extension `K/L`, and `E` remains invariant 
under every `K`-algebra embedding `E →ₐ[K] L`, then `E/K` is normal. -/
instance Normal.of_intermediateField_invariant_under_embedding [Normal K L] 
    (E : IntermediateField K L) (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : Normal K E := by
  have hn := normalClosure.normal K E L
  rw[normalClosure.eq_bot_of_invariant_under_embedding E h] at hn
  rw[← restrictScalars_bot_eq_self E]
  apply restrictScalars_normal.mpr hn

/- If `E` is an intermediateField of a normal extension `K/L`, and every element in `E` 
remains in `E` after the action of every element in the Galois group, then `E/K` is normal. -/
instance Normal.of_intermediateField_mem_invariant_under_embedding [Normal K L] 
    (E : IntermediateField K L) (h : ∀ σ : L ≃ₐ[K] L, ∀ x : E, σ x.1 ∈ E) : Normal K E := by
  apply Normal.of_intermediateField_invariant_under_embedding E
  intro σ
  apply le_antisymm
  · intro y hy
    rcases AlgHom.mem_fieldRange.mp hy with ⟨x, hx⟩
    refine' Set.mem_of_eq_of_mem _ (h (liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L) x)
    have h : x.1 = algebraMap E L x := rfl
    rw[← hx, h, liftNormal_commutes]
    rfl
  · intro y hy
    let τ := liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L
    let x : E := ⟨τ⁻¹ y, Set.mem_of_eq_of_mem rfl (h τ⁻¹ ⟨y, hy⟩)⟩
    rw[AlgHom.mem_fieldRange]
    use x
    have hx : σ x = algebraMap (σ.fieldRange) L ((AlgHom.fieldRange_toAlgEquiv σ) x) := rfl
    have hxt : (algebraMap E L) x = τ⁻¹ y := rfl
    have ht : τ (τ⁻¹ y) = (τ * τ⁻¹) y := rfl
    rw[hx, ← liftNormal_commutes, hxt, ht, mul_right_inv]
    rfl

/- If `H` is a Normal Subgroup of `Gal(L/K)`, then `fixedField H` is Galois over `K`. -/
instance IsGalois.of_fixedField_Normal_Subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply Normal.of_intermediateField_mem_invariant_under_embedding (fixedField H)
    intro σ x τ
    calc _ = (σ * σ⁻¹ * τ.1 * σ) x.1 := by rw[mul_right_inv]; rfl
      _ = _ := by nth_rw 3 [← x.2 ⟨_ , (Subgroup.Normal.conj_mem hn τ.1 τ.2 σ⁻¹)⟩]; rfl

/- If `H` is a Normal Subgroup of `Gal(L/K)`, then `Gal(L/K)⧸H ≃* Gal(fixedField H/K)`. -/
theorem IsGalois.Normal_Galois_Group [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    (L ≃ₐ[K] L) ⧸ H ≃* ((fixedField H) ≃ₐ[K] (fixedField H)) := by
  refine' (quotientMulEquivOfEq ((fixingSubgroup_fixedField H).symm.trans _)).trans <|
    quotientKerEquivOfSurjective (restrictNormalHom (fixedField H)) <|
      @restrictNormalHom_surjective K (fixedField H) _ _ _ L _ _ _ _ _ _
  ext σ
  refine' (((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).trans _).trans AlgEquiv.ext_iff.symm).trans 
    (mem_ker (restrictNormalHom (fixedField H))).symm
  constructor
  · exact fun h ⟨x, hx⟩ ↦ Subtype.val_inj.mp <|
      (restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩).trans (h x hx)
  · intro h x hx
    dsimp
    have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ x :=
      restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
    rw[← hs]
    apply Subtype.val_inj.mpr (h ⟨x, hx⟩)



/- A `MulEquiv` maps a Normal Subgroup to a Normal Subgroup. -/
theorem Subgroup.map_equiv_normal {G G':Type _} [Group G] [Group G'] (f : G ≃* G')
    (H : Subgroup G) [hn: Normal H] : Normal (map f.toMonoidHom H) := by
  have h : map f.toMonoidHom ⊤ = ⊤ := map_top_of_surjective f (MulEquiv.surjective f)
  refine' normalizer_eq_top.mp _
  rw[← h, ← normalizer_eq_top.mpr hn, map_equiv_normalizer_eq H f]

end Galois



open Ideal Algebra

open scoped BigOperators

section preparation

variable {R ι :Type _} [CommRing R]

@[local instance]
noncomputable instance : DecidableEq ι := Classical.decEq ι

/- If the product of a finite number of elements in the commutative ring `R` lies in the 
prime ideal `p`, then at least one of those elements is in `p`. -/
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
  
  

variable (K :Type _) [Field K] [NumberField K] (L :Type _) [Field L] [Algebra K L]

namespace NumberField



/- A finite extension of a number field is a number field. -/
theorem FiniteExtensionOfANumberFieldIsANumberField [FiniteDimensional K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional := by
    have := charZero_of_injective_algebraMap (algebraMap K L).injective
    apply Module.Finite.trans K L

variable [NumberField L]

/- Any Extension between Number Fields is Finite. -/
instance Extension.FiniteDimensional : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

instance : Module (𝓞 K) (𝓞 L) := toModule

instance : SMul (𝓞 K) (𝓞 L) := toSMul

instance : IsScalarTower (𝓞 K) (𝓞 L) L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/- `𝓞 L` is the integral closure of `𝓞 K` in `L`. -/
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

/- Any Extension between ring of integers is integral. -/
instance Extension_ringOfIntegers.isIntegral : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L

/- In particular, Any Extension between ring of integers is noetherian. -/
instance Extension_ringOfIntegers.isNoetherian : IsNoetherian (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

/- The kernel of the algebraMap between ring of integers is `⊥`. -/
theorem algebraMap_ker_eq_bot : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ := by
  apply (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr
  intro x hx
  have h: (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  rw[hx] at h; dsimp at h
  rw[← RingHom.map_zero (algebraMap K L)] at h
  exact (Subalgebra.coe_eq_zero (𝓞 K)).mp ((NoZeroSMulDivisors.algebraMap_injective K L) h)
  
/- The algebraMap between ring of integers is injective. -/
theorem algebraMap.Injective : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (algebraMap_ker_eq_bot K L)

variable {L :Type _} [Field L] [NumberField L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))

/- The ideal of `𝓞 K` below `P`. -/
abbrev IdealBelow : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P

instance IdealBelow.IsPrime [P.IsPrime] : IsPrime (IdealBelow K P) :=
  IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))

variable {K}

class ideal_lies_over (p : Ideal (𝓞 K)) : Prop where over : p = comap (algebraMap (𝓞 K) (𝓞 L)) P

infix : 50 "lies_over" => ideal_lies_over

instance over_IdealBelow : P lies_over (IdealBelow K P) where over := rfl

theorem over_def {p : Ideal (𝓞 K)} {P : Ideal (𝓞 L)} (h : p = IdealBelow K P) :
  P lies_over p where over := h

end NumberField

end preparation

open NumberField

variable {K :Type _} [Field K] [NumberField K] {L :Type _} [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) [p.IsMaximal] (P : Ideal (𝓞 L)) [hpm : P.IsMaximal] [hp : P lies_over p]

/- If `P` is a maximal ideal, then the ideal of `𝓞 K` below `P` is also maximal. -/
instance IdealBelow.IsMaximal: IsMaximal (IdealBelow K P) :=
  isMaximal_comap_of_isIntegral_of_isMaximal (Extension_ringOfIntegers.isIntegral K L) P

/- Maximal Ideals in the ring of integers are non-zero. -/
theorem ne_bot_of_isMaximal : P ≠ ⊥ := 
  Ring.ne_bot_of_isMaximal_of_not_isField hpm (RingOfIntegers.not_isField L)

/- The image of a maximal ideal under the algebraMap between ring of integers is non-zero. -/
theorem map_isMaximal_ne_bot (L :Type _) [Field L] [Algebra K L] : 
    map (algebraMap (𝓞 K) (𝓞 L)) p ≠ ⊥ := 
  fun h ↦ (ne_bot_of_isMaximal p) ((map_eq_bot_iff_of_injective (algebraMap.Injective K L)).mp h)

@[local instance]
noncomputable instance : Field ((𝓞 L) ⧸ P) := Quotient.field P

noncomputable instance : Field ((𝓞 K) ⧸ (IdealBelow K P)) := Quotient.field (IdealBelow K P)

instance : Algebra ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) := Quotient.algebraQuotientOfLeComap (le_of_eq hp.over)

instance : Module ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) := toModule

instance : SMul (𝓞 K) ((𝓞 K) ⧸ p) := Submodule.Quotient.instSMul p

instance : Algebra (𝓞 K) ((𝓞 L) ⧸ P) := Quotient.algebra (𝓞 K)

instance : Module (𝓞 K) ((𝓞 L) ⧸ P) := toModule

instance : @IsScalarTower (𝓞 K) ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) _ toSMul toSMul := 
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

instance : FiniteDimensional ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  IsNoetherian.iff_fg.mp <| isNoetherian_of_tower (𝓞 K) <|
    isNoetherian_of_surjective (𝓞 L) (Ideal.Quotient.mkₐ (𝓞 K) P).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

 

-- Hilbert's Ramification Theory

/- The `AlgEquiv` of elements of Galois group `Gal(K/L)` restricted to `𝓞 L`. -/
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


/- Consider `GalAlgEquiv σ` as a ring homomorphism. -/
def GalRingHom (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L) := (GalAlgEquiv σ).toAlgHom.toRingHom

theorem GalRingHom_mul (σ τ : L ≃ₐ[K] L) : 
  (GalRingHom σ).comp (GalRingHom τ) = GalRingHom (σ * τ) := rfl

theorem GalRingHom_one : GalRingHom (1 : L ≃ₐ[K] L) = RingHom.id (𝓞 L) := rfl

theorem GalRingHom_mul_left_inv (σ : L ≃ₐ[K] L) : (GalRingHom σ⁻¹).comp (GalRingHom σ) 
  = RingHom.id (𝓞 L) := by rw[GalRingHom_mul, mul_left_inv, GalRingHom_one]

theorem GalRingHom_mul_left_inv_mem (σ : L ≃ₐ[K] L) (x : 𝓞 L): 
    GalRingHom σ⁻¹ (GalRingHom σ x) = x := by
  calc _ = (GalRingHom σ⁻¹).comp (GalRingHom σ) x := rfl
    _ = _ := by rw[GalRingHom_mul_left_inv, RingHom.id_apply]


/- A new theorem in `Mathlib.Algebra.Ring.Equiv` -/
theorem MulEquiv.isField {A : Type _} (B : Type _) [Semiring A] [Semiring B] (hB : IsField B)
    (e : A ≃* B) : IsField A where
  exists_pair_ne := have ⟨x, y, h⟩ := hB.exists_pair_ne; ⟨e.symm x, e.symm y, e.symm.injective.ne h⟩
  mul_comm := fun x y => e.injective <| by rw [_root_.map_mul, _root_.map_mul, hB.mul_comm]
  mul_inv_cancel := fun h => by
    obtain ⟨a', he⟩ := hB.mul_inv_cancel ((e.injective.ne h).trans_eq <| map_zero e)
    exact ⟨e.symm a', e.injective <| by rw [_root_.map_mul, map_one, e.apply_symm_apply, he]⟩

/- The `GalRingHom σ` will send a maximal ideal to a maximal ideal. -/
instance GalRingHom_map.isMaximal (σ : L ≃ₐ[K] L) : IsMaximal (map (GalRingHom σ) P) :=
  Quotient.maximal_of_isField _ <| MulEquiv.isField _ (Field.toIsField ((𝓞 L) ⧸ P)) 
    (quotientEquiv P (map (GalRingHom σ) P) (GalAlgEquiv σ) rfl).symm.toMulEquiv

-- Propsition 9.1

/- The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals `P` of `𝓞 L` 
lying above `p`, i.e., these prime ideals are all conjugates of each other. -/
theorem IsMaximal_conjugates (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [hq : Q lies_over p] 
    [IsGalois K L] : ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q := by
  by_contra hs
  push_neg at hs
  let s : Finset (L ≃ₐ[K] L) := Finset.univ
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ in s, map (GalRingHom σ) P)).mp <| 
    sup_prod_eq_top <| fun σ _ ↦ IsMaximal.coprime_of_ne hqm (GalRingHom_map.isMaximal P σ) 
      (hs σ).symm with ⟨x, hx, y, hy, hxy⟩
  let n : 𝓞 L := ∏ σ in s, (GalRingHom σ) x
  have hnx : n = (algebraMap (𝓞 K) (𝓞 L)) (RingOfIntegers.norm K x) := by
    apply Subtype.val_inj.mp
    rw[RingOfIntegers.coe_algebraMap_norm K x, norm_eq_prod_automorphisms K x.1]
    exact Submonoid.coe_finset_prod (𝓞 L).toSubsemiring.toSubmonoid _ s
  have hnk : RingOfIntegers.norm K x ∈ IdealBelow K P := by
    rw[IdealBelow, ← hp.over, hq.over]
    apply mem_comap.mpr
    rw[← hnx]
    refine' (span_singleton_le_iff_mem Q).mp _
    rw[← prod_span_singleton]
    exact prod_le_inf.trans <| (@Finset.inf_le _ _ _ _ s (fun σ ↦ span {(GalRingHom σ) x}) _ 
      (@Finset.mem_univ (L ≃ₐ[K] L) _ 1)).trans (Iff.mpr (span_singleton_le_iff_mem Q) hx)
  have hnp : n ∈ P := Eq.mpr (_root_.id (hnx ▸ Eq.refl (n ∈ P))) hnk
  rcases IsPrime.prod_mem hnp with ⟨⟨σ, _⟩, hs⟩
  have hxp : x ∈ map (GalRingHom σ⁻¹) P := Eq.mpr 
    ((GalRingHom_mul_left_inv_mem σ x).symm ▸ Eq.refl _) (mem_map_of_mem (GalRingHom σ⁻¹) hs)
  have h := Ideal.add_mem (map (GalRingHom σ⁻¹) P) hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ⁻¹))) hy
  rw[hxy] at h
  exact IsMaximal.ne_top (GalRingHom_map.isMaximal P σ⁻¹) ((eq_top_iff_one _).mpr h) 

theorem IsMaximal_conjugates' {P : Ideal (𝓞 L)} [P.IsMaximal] {Q : Ideal (𝓞 L)} [Q.IsMaximal] 
    [IsGalois K L] (h : IdealBelow K P = IdealBelow K Q) : 
    ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q := let_fun _ := over_def h
  IsMaximal_conjugates (IdealBelow K P) P Q



open UniqueFactorizationMonoid IsDedekindDomain

instance : Ring.DimensionLEOne (𝓞 L) := Ring.DimensionLEOne.integralClosure ℤ L

theorem prime_iff_isMaximal (P : Ideal (𝓞 L)) : Prime P ↔ IsMaximal P := 
  ⟨fun hp ↦ IsPrime.isMaximal (isPrime_of_prime hp) (Prime.ne_zero hp),
    fun hp ↦ prime_of_isPrime (ne_bot_of_isMaximal P) (IsMaximal.isPrime hp)⟩

/- The function normalizedFactors commutes with the function `map (GalRingHom σ)`. -/
theorem normalizedFactors_map_GalRingHom_commutes {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) (σ : L ≃ₐ[K] L) : 
    normalizedFactors (map (GalRingHom σ) I) = 
    Multiset.map (map (GalRingHom σ)) (normalizedFactors I) := by
  nth_rw 1 [← prod_normalizedFactors_eq_self hI]
  have h := Multiset.prod_hom (normalizedFactors I) (mapHom (GalRingHom σ))
  simp only [mapHom_apply] at h 
  rw[← h, normalizedFactors_prod_of_prime]
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨p, hp, hpq⟩
  have hpm : IsMaximal p := (prime_iff_isMaximal p).mp (prime_of_normalized_factor p hp)
  rw[← hpq]
  exact (prime_iff_isMaximal (map (GalRingHom σ) p)).mpr (GalRingHom_map.isMaximal p σ)

/- The image of an ideal under the algebraMap between ring of integers remains invariant 
under the action of `GalRingHom σ`. -/
theorem Ideal_map_invariant_under_GalRingHom (p : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) : 
    (map (GalRingHom σ)) (map (algebraMap (𝓞 K) (𝓞 L)) p) = map (algebraMap (𝓞 K) (𝓞 L)) p := by
  apply le_antisymm <| map_le_iff_le_comap.mpr <| map_le_iff_le_comap.mpr <|
    fun _ h ↦ by simp only [GalRingHom, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, 
      mem_comap, RingHom.coe_coe, AlgHom.commutes, mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h]
  apply map_le_iff_le_comap.mpr
  intro x h
  rw[mem_comap, map_map]
  apply Set.mem_of_eq_of_mem _ (mem_map_of_mem ((GalRingHom σ).comp (algebraMap (𝓞 K) (𝓞 L))) h)
  rw[GalRingHom, ← AlgEquiv.commutes (GalAlgEquiv σ) x]
  rfl

/- The map induced by `GalRingHom σ` on the ideals of `𝓞 L` is injective. -/
theorem GalRingHom_IdealMap.injective (σ : L ≃ₐ[K] L): Function.Injective (map (GalRingHom σ)) :=
  fun I J h ↦ by rw[← map_id I, ← GalRingHom_mul_left_inv σ, ← map_map, h, map_map, 
    GalRingHom_mul_left_inv σ, map_id]

/- In the case of Galois extension, all the `ramificationIdx` are the same. -/
theorem ramificationIdx_eq_of_isGalois (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [Q lies_over p] 
    [IsGalois K L] : ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P = 
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw[ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) (IsMaximal.isPrime hpm)
    (ne_bot_of_isMaximal P), ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) 
    (IsMaximal.isPrime hqm) (ne_bot_of_isMaximal Q), ← hs]
  nth_rw 2 [← Ideal_map_invariant_under_GalRingHom p σ]
  rw[normalizedFactors_map_GalRingHom_commutes (map_isMaximal_ne_bot p L) σ]
  rw[Multiset.count_map_eq_count' _ _ (GalRingHom_IdealMap.injective σ) _]

theorem ramificationIdx_eq_of_isGalois' [IsGalois K L] {P : Ideal (𝓞 L)} [P.IsMaximal]
    {Q : Ideal (𝓞 L)} [hqm : Q.IsMaximal] (h : IdealBelow K P = IdealBelow K Q) :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (IdealBelow K P) P =
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (IdealBelow K Q) Q := by
  have := over_def h
  rw[← h]
  exact ramificationIdx_eq_of_isGalois (IdealBelow K P) P Q

theorem IdealBelow_invariant_under_GalRingHom (σ : L ≃ₐ[K] L) : 
    p = IdealBelow K (map (GalRingHom σ) P) := by
  ext x
  rw[mem_comap, hp.over, mem_comap]
  refine' ⟨fun h ↦ Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ).commutes' x]; rfl)
    (mem_map_of_mem (GalRingHom σ) h), fun h ↦ _⟩
  have h := mem_map_of_mem (GalRingHom σ⁻¹) h
  rw[map_map, GalRingHom_mul_left_inv, map_id] at h
  exact Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ⁻¹).commutes' x]; rfl) h

theorem GalRingHom_map_lies_over (σ : L ≃ₐ[K] L) : (map (GalRingHom σ) P) lies_over p := 
  over_def (IdealBelow_invariant_under_GalRingHom p P σ)

instance (σ : L ≃ₐ[K] L) : Algebra ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ map (GalRingHom σ) P) :=
  Quotient.algebraQuotientOfLeComap (le_of_eq (IdealBelow_invariant_under_GalRingHom p P σ))

instance (σ : L ≃ₐ[K] L) : Module ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ map (GalRingHom σ) P) := Algebra.toModule

/- The algebra equiv `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ map (GalRingHom σ) P)` 
induced by an algebra equiv `σ : L ≃ₐ[K] L`. -/
def residueField_GalAlgEquiv {P : Ideal (𝓞 L)} [P.IsMaximal] [P lies_over p] {Q : Ideal (𝓞 L)} 
    [Q.IsMaximal] [Q lies_over p] {σ : L ≃ₐ[K] L} (hs: map (GalRingHom σ) P = Q) :
    ((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ Q) := { 
  quotientEquiv P Q (GalAlgEquiv σ) (by rw[← hs]; rfl) with 
  commutes' := by
    rintro ⟨x⟩
    calc _ = Quotient.mk 
          (Submodule.quotientRel Q) ((GalAlgEquiv σ) ((algebraMap (𝓞 K) (𝓞 L)) x)) := rfl
      _ = _ := by rw[AlgEquiv.commutes (GalAlgEquiv σ) x]; rfl        
}

/- In the case of Galois extension, all the `inertiaDeg` are the same. -/
theorem inertiaDeg_eq_of_isGalois (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q lies_over p] [IsGalois K L] : 
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw[inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  exact LinearEquiv.finrank_eq (residueField_GalAlgEquiv p hs).toLinearEquiv

/- For any maximal idela `p` in `𝓞 K`, there exists a maximal ideal in `𝓞 L` lying over `p`. -/
theorem exists_ideal_over_maximal_of_ringOfIntegers (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L :Type _) [Field L] [NumberField L] [Algebra K L] : 
    ∃ (P : Ideal (𝓞 L)), IsMaximal P ∧ P lies_over p := by
  rcases exists_ideal_over_maximal_of_isIntegral (Extension_ringOfIntegers.isIntegral K L) p 
    (by simp only [algebraMap_ker_eq_bot K L, bot_le]) with ⟨P, hpm, hp⟩
  exact ⟨P, hpm, over_def hp.symm⟩

/- In the case of Galois extension, it can be seen from the Theorem `ramificationIdx_eq_of_IsGalois`
that all `ramificationIdx` are the same, which we define as the `ramificationIdx_of_isGalois`. -/
noncomputable def ramificationIdx_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L :Type _) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : ℕ := 
  ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p <| 
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/- In the case of Galois extension, it can be seen from the Theorem `inertiaDeg_eq_of_IsGalois`
that all `inertiaDeg` are the same, which we define as the `inertiaDeg_of_isGalois`. -/
noncomputable def inertiaDeg_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L :Type _) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] : ℕ := 
  inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p <| 
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/- In the case of Galois extension, all ramification indices are equal to the 
`ramificationIdx_of_isGalois`. This completes the property mentioned in our previous definition. -/
theorem ramificationIdx_eq_ramificationIdx_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P = ramificationIdx_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [ramificationIdx_of_isGalois]
  exact ramificationIdx_eq_of_isGalois p P _

/- In the case of Galois extension, all inertia degrees are equal to the `inertiaDeg_of_isGalois`.
This completes the property mentioned in our previous definition. -/
theorem inertiaDeg_eq_inertiaDeg_of_isGalois [IsGalois K L]:
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [inertiaDeg_of_isGalois]
  exact inertiaDeg_eq_of_isGalois p P _



-- Definition 9.2

/- The `Finset` consisting of all primes lying over `p : Ideal (𝓞 K)`. -/
noncomputable abbrev primes_over {K :Type _} [Field K] [NumberField K] (p : Ideal (𝓞 K)) 
    (L :Type _) [Field L] [NumberField L] [Algebra K L] : Finset (Ideal (𝓞 L)) :=
  (factors (map (algebraMap (𝓞 K) (𝓞 L)) p)).toFinset

theorem primes_over_mem (p : Ideal (𝓞 K)) [hm : p.IsMaximal] (P : Ideal (𝓞 L)) :
    P ∈ primes_over p L ↔ P.IsMaximal ∧ P lies_over p := by
  constructor
  · intro hp
    have hp := Multiset.mem_toFinset.mp hp
    have hpm := (prime_iff_isMaximal P).mp (prime_of_factor P hp)
    exact ⟨hpm, over_def <| IsMaximal.eq_of_le hm (comap_ne_top _ (IsMaximal.ne_top hpm))
      (le_comap_of_map_le (le_of_dvd (dvd_of_mem_factors hp)))⟩
  . intro ⟨hpm, hp⟩
    have hd := dvd_iff_le.mpr (map_le_of_le_comap (le_of_eq hp.over))
    have hir := irreducible_iff_prime.mpr ((prime_iff_isMaximal P).mpr hpm)
    rcases exists_mem_factors_of_dvd (map_isMaximal_ne_bot p L) hir hd with ⟨_, hq, he⟩
    rw[Multiset.mem_toFinset, associated_iff_eq.mp he]
    exact hq

instance (Q : primes_over p L) : IsMaximal Q.1 := ((primes_over_mem p Q.1).mp Q.2).1

instance (Q : primes_over p L) : Q.1 lies_over p := ((primes_over_mem p Q.1).mp Q.2).2

instance (Q : primes_over p L) (σ : L ≃ₐ[K] L) : map (GalRingHom σ) Q.1 lies_over p :=
  GalRingHom_map_lies_over p Q.1 σ

def primes_over.mk : primes_over p L := ⟨P, (primes_over_mem p P).mpr ⟨hpm, hp⟩⟩

theorem primes_over.coe_mk : (primes_over.mk p P).1 = P := rfl 

/- The `Finset` consisting of all primes lying over `IdealBelow K P`, i.e., all the primes `Q` such
that `IdealBelow K Q = IdealBelow K P`. -/
noncomputable abbrev primes_same_bleow : Finset (Ideal (𝓞 L)) := primes_over (IdealBelow K P) L

instance Gal_MulAction_primes : MulAction (L ≃ₐ[K] L) (primes_over p L) where
  smul σ Q := primes_over.mk p (map (GalRingHom σ) Q.1)
  one_smul Q := have h : primes_over.mk p (map (GalRingHom (1 : L ≃ₐ[K] L)) Q.1) = Q := (by 
    rw[← Subtype.val_inj, primes_over.coe_mk, GalRingHom_one, map_id])
    h  
  mul_smul σ τ Q := have := GalRingHom_map_lies_over p (map (GalRingHom τ) Q.1) σ
    have h : primes_over.mk p (map (GalRingHom (σ * τ)) Q.1) = 
        primes_over.mk p (map (GalRingHom σ) (primes_over.mk p (map (GalRingHom τ) Q.1)).1) := by
      simp only [← Subtype.val_inj, primes_over.coe_mk, map_map, GalRingHom_mul]  
    h

def DecompositionGroup : Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer _ (primes_over.mk p P)

def DecompositionGroup' : Subgroup (L ≃ₐ[K] L) := {
  carrier := { σ : L ≃ₐ[K] L | map (GalRingHom σ) P = P}
  mul_mem' := by
    intro σ τ hs ht
    have hmul: GalRingHom (σ * τ) = RingHom.comp (GalRingHom σ) (GalRingHom τ) := rfl
    rw[Set.mem_setOf_eq, hmul, ← Ideal.map_map, ht, hs]
  one_mem' := map_id P
  inv_mem' := by
    intro σ hs
    calc _ = map (GalRingHom σ⁻¹) (map (GalRingHom σ) P) := by rw[hs]
      _ = map ((GalRingHom (σ⁻¹ * σ))) P := by apply Ideal.map_map
      _ = map (GalRingHom 1) P := by rw[mul_left_inv σ]
      _ = P := map_id P
}



def DecompositionField : IntermediateField K L := IntermediateField.fixedField (DecompositionGroup p P)

instance : Field (DecompositionField p P) :=
  SubfieldClass.toField (IntermediateField K L) (DecompositionField p P)

-- DecompositionField is a Number Field
instance DecompositionField_NumberField : NumberField (DecompositionField p P) :=
  FiniteExtensionOfANumberFieldIsANumberField K (DecompositionField p P)

def DecompositionIdeal : Ideal (𝓞 (DecompositionField p P)) :=
  IdealBelow (DecompositionField p P) P

variable [IsGalois K L] [P.IsMaximal]

instance DecompositionFieldIdealIsMaximal : IsMaximal ((DecompositionIdeal p P)) := by
  apply IdealBelow.IsMaximal



-- Proposition 9.3
theorem DecompositionIdeal.Nonsplit : Nonsplit (algebraMap (𝓞 (DecompositionField p P)) (𝓞 L))
(DecompositionIdeal p P) := sorry

theorem ramificationIdx_of_DecompositionIdeal :
  ramificationIdx (algebraMap (𝓞 (DecompositionField p P)) (𝓞 L)) (DecompositionIdeal p P) P =
  ramificationIdx_of_isGalois p L := sorry

theorem Extension_degree_over_DecompositionField : FiniteDimensional.finrank (DecompositionField p P) L
= (ramificationIdx_of_isGalois p L )*
(inertiaDeg_of_isGalois p L) := sorry

theorem DecompositionIdeal.TotallySplit :
  TotallySplit (algebraMap (𝓞 K) (𝓞 (DecompositionField p P))) p := sorry



-- Proposition 9.4
instance Extension_of_Residue_Fields_is_Galois : IsGalois ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)
  := sorry


def DecompositionGaloisHom : MonoidHom (DecompositionGroup p P)
(((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) := sorry

theorem DecompositionGaloisHom_surjective : Function.Surjective (DecompositionGaloisHom p P) := sorry



open IntermediateField IsGalois

-- Definition 9.5
abbrev InertiaGroup' : Subgroup (DecompositionGroup p P) := MonoidHom.ker (DecompositionGaloisHom p P)

instance : Subgroup.Normal (InertiaGroup' p P) := by apply MonoidHom.normal_ker

def InertiaGroup : Subgroup (L ≃ₐ[DecompositionField p P] L) :=
  Subgroup.map (Subgroup_eq_fixingSubgroup (DecompositionGroup p P)).toMonoidHom (InertiaGroup' p P)

-- InertiaGroup is a Normal Subgroup of Gal(L/(DecompositionField p P))
instance InertiaGroup_Normal : Subgroup.Normal (InertiaGroup p P) :=
  Subgroup.map_equiv_normal (Subgroup_eq_fixingSubgroup (DecompositionGroup p P)) (InertiaGroup' p P)

def InertiaField : IntermediateField (DecompositionField p P) L := fixedField (InertiaGroup p P)

instance : Field (InertiaField p P) :=
  SubfieldClass.toField (IntermediateField (DecompositionField p P) L) (InertiaField p P)

-- InertiaField is a Number Field
instance InertiaField_NumberField : NumberField (InertiaField p P) :=
  @FiniteExtensionOfANumberFieldIsANumberField (DecompositionField p P) _ _ (InertiaField p P) _
  (IntermediateField.algebra (InertiaField p P)) _

instance : Algebra (DecompositionField p P) (InertiaField p P) :=
  Subalgebra.algebra (InertiaField p P).toSubalgebra

instance : Module (DecompositionField p P) (InertiaField p P) := toModule

def InertiaIdeal : Ideal (𝓞 (InertiaField p P)) := IdealBelow (InertiaField p P) P

instance : IsMaximal (InertiaIdeal p P) := IdealBelow.IsMaximal P



-- Proposition 9.6
instance : @IsGalois (DecompositionField p P) _ (InertiaField p P) _ (IntermediateField.algebra _)
  := IsGalois.of_fixedField_Normal_Subgroup (InertiaGroup p P)

theorem Galois_group_of_InertiaField_below_eq_Galois_group_of_ResidueField :
  ((InertiaField p P) ≃ₐ[(DecompositionField p P)] (InertiaField p P)) ≃*
  (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) := 
    (Normal_Galois_Group (InertiaGroup p P)).symm.trans <|
      (QuotientGroup.congr (InertiaGroup' p P) (InertiaGroup p P)
        (Subgroup_eq_fixingSubgroup (DecompositionGroup p P))  rfl).symm.trans <|
          QuotientGroup.quotientKerEquivOfSurjective (DecompositionGaloisHom p P) <|
            DecompositionGaloisHom_surjective p P

theorem Galois_group_of_InertiaField_above_eq_InertiaGroup :
  (InertiaGroup p P) ≃* (L ≃ₐ[InertiaField p P] L) := Subgroup_eq_fixingSubgroup (InertiaGroup p P)

noncomputable instance (priority := high) (K L :Type _) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]: Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L

theorem Extension_degree_of_InertiaField_over_DecompositionField :
  FiniteDimensional.finrank (DecompositionField p P) (InertiaField p P) =
  inertiaDeg_of_isGalois p L := sorry

theorem Extension_degree_over_InertiaField : FiniteDimensional.finrank (InertiaField p P) L =
ramificationIdx_of_isGalois p L := sorry

theorem card_of_InertiaGroup : Fintype.card (InertiaGroup p P) =
ramificationIdx_of_isGalois p L := sorry

theorem ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_isGalois :
ramificationIdx (algebraMap (𝓞 (InertiaField p P)) (𝓞 L)) (InertiaIdeal p P) P =
ramificationIdx_of_isGalois p L := sorry

theorem InertiaDeg_over_InertiaIdeal_eq_one :
inertiaDeg (algebraMap (𝓞 (InertiaField p P)) (𝓞 L)) (InertiaIdeal p P) P = 1 := sorry

theorem ramificationIdx_below_InertiaIdeal_eq_one :
ramificationIdx (algebraMap (𝓞 (DecompositionField p P)) (𝓞 (InertiaField p P)))
(DecompositionIdeal p P) (InertiaIdeal p P) = 1 := sorry

theorem InertiaDeg_below_InertiaIdeal_eq_inertiaDeg_of_isGalois : inertiaDeg
(algebraMap (𝓞 (DecompositionField p P)) (𝓞 (InertiaField p P))) (DecompositionIdeal p P)
(InertiaIdeal p P) = inertiaDeg_of_isGalois p L := sorry
