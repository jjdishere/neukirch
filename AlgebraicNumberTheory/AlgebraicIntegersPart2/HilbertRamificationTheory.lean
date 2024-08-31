/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia

import AlgebraicNumberTheory.AlgebraicIntegersPart2.ExtensionOfDedekindDomains

set_option autoImplicit false



open Algebra

open scoped BigOperators

section Galois

open IntermediateField AlgEquiv QuotientGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- If `H` is a subgroup of `Gal(L/K)`, then `Gal(L / fixedField H)` is isomorphic to `H`. -/
def IntermediateField.subgroup_equiv_aut (H : Subgroup (L ≃ₐ[K] L)) :
    (L ≃ₐ[fixedField H] L) ≃* H where
  toFun ϕ := ⟨ϕ.restrictScalars _, le_of_eq (fixingSubgroup_fixedField H) ϕ.commutes⟩
  invFun ϕ := { toRingEquiv (ϕ : L ≃ₐ[K] L) with
    commutes' := (ge_of_eq (fixingSubgroup_fixedField H)) ϕ.mem }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The `AlgEquiv` induced by an `AlgHom` from the domain of definition to the `fieldRange`. -/
noncomputable def AlgHom.fieldRange_toAlgEquiv {E : IntermediateField K L} (σ : E →ₐ[K] L) :
    E ≃ₐ[K] σ.fieldRange where
  toFun x := ⟨σ x, by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]⟩
  invFun y := Classical.choose (AlgHom.mem_fieldRange.mp y.2)
  left_inv x := have hs : Function.Injective σ := RingHom.injective σ
    have h : σ x ∈ σ.fieldRange := by simp only [AlgHom.mem_fieldRange, exists_apply_eq_apply]
    hs (Classical.choose_spec (AlgHom.mem_fieldRange.mp h))
  right_inv y := Subtype.val_inj.mp (Classical.choose_spec (mem_fieldRange.mp y.2))
  map_mul' x y := Subtype.val_inj.mp (σ.toRingHom.map_mul x y)
  map_add' x y := Subtype.val_inj.mp (σ.toRingHom.map_add x y)
  commutes' x := Subtype.val_inj.mp (commutes σ x)

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}

theorem AlgHom.fieldRange_toAlgEquiv_apply (σ : E →ₐ[K] L) (x : E) :
  (AlgHom.fieldRange_toAlgEquiv σ) x = σ x := rfl

theorem AlgEquiv.liftNormal_intermediateField_commutes [Normal K L] {E F : IntermediateField K L}
    (σ : E ≃ₐ[K] F) (x : E) : (AlgEquiv.liftNormal σ L) x = σ x := by
  have h : x.1 = algebraMap E L x := rfl
  rw [h, liftNormal_commutes]
  rfl

theorem normalClosure.eq_self_of_invariant_under_embedding {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Normal K L] (E : IntermediateField K L)
    (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : normalClosure K E L = E := by
  refine le_antisymm ?_ ((h (val E)).symm.trans_le (le_iSup AlgHom.fieldRange (val E)))
  intro x hx
  rw [normalClosure, mem_mk, Subalgebra.mem_toSubsemiring, mem_toSubalgebra] at hx
  exact iSup_le (fun σ ↦ (h σ).le) hx

/-- If `E` is an intermediateField of a normal extension `K/L`, and `E` remains invariant
under every `K`-algebra embedding `E →ₐ[K] L`, then `E/K` is normal. -/
theorem Normal.of_intermediateField_invariant_under_embedding [Normal K L]
    (E : IntermediateField K L) (h : ∀ σ : E →ₐ[K] L, σ.fieldRange = E) : Normal K E := by
  have hn := normalClosure.normal K E L
  rw [normalClosure.eq_self_of_invariant_under_embedding E h] at hn
  exact hn

/-- If `E` is an intermediateField of a normal extension `K/L`, and every element in `E`
remains in `E` after the action of every element in the Galois group, then `E/K` is normal. -/
theorem Normal.of_intermediateField_mem_invariant_under_embedding [Normal K L]
    (E : IntermediateField K L) (h : ∀ σ : L ≃ₐ[K] L, ∀ x : E, σ x.1 ∈ E) : Normal K E := by
  apply Normal.of_intermediateField_invariant_under_embedding E
  intro σ
  apply le_antisymm
  · intro y hy
    rcases AlgHom.mem_fieldRange.mp hy with ⟨x, hx⟩
    apply Set.mem_of_eq_of_mem _ (h (liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L) x)
    have h : x.1 = algebraMap E L x := rfl
    rw [← hx, h, liftNormal_commutes]
    rfl
  · intro y hy
    let τ := liftNormal (AlgHom.fieldRange_toAlgEquiv σ) L
    let x : E := ⟨τ⁻¹ y, Set.mem_of_eq_of_mem rfl (h τ⁻¹ ⟨y, hy⟩)⟩
    rw [AlgHom.mem_fieldRange]
    use x
    have hx : σ x = algebraMap (σ.fieldRange) L ((AlgHom.fieldRange_toAlgEquiv σ) x) := rfl
    have hxt : (algebraMap E L) x = τ⁻¹ y := rfl
    have ht : τ (τ⁻¹ y) = (τ * τ⁻¹) y := rfl
    rw [hx, ← liftNormal_commutes, hxt, ht, mul_inv_cancel]
    rfl

/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `fixedField H` is Galois over `K`. -/
instance IsGalois.of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply Normal.of_intermediateField_mem_invariant_under_embedding (fixedField H)
    intro σ x τ
    calc _ = (σ * σ⁻¹ * τ.1 * σ) x.1 := by rw [mul_inv_cancel]; rfl
      _ = _ := by nth_rw 2 [← x.2 ⟨_ , (Subgroup.Normal.conj_mem hn τ.1 τ.2 σ⁻¹)⟩]; rfl

/-- If `H` is a normal Subgroup of `Gal(L/K)`, then `Gal(fixedField H/K)` is isomorphic to
`Gal(L/K)⧸H`. -/
noncomputable def IsGalois.normal_aut_equiv_quotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [Subgroup.Normal H] :
    ((fixedField H) ≃ₐ[K] (fixedField H)) ≃* (L ≃ₐ[K] L) ⧸ H := by
  apply MulEquiv.symm <| (quotientMulEquivOfEq ((fixingSubgroup_fixedField H).symm.trans _)).trans
    <| quotientKerEquivOfSurjective (restrictNormalHom (fixedField H)) <|
      restrictNormalHom_surjective L
  ext σ
  apply (((mem_fixingSubgroup_iff (L ≃ₐ[K] L)).trans ⟨fun h ⟨x, hx⟩ ↦ Subtype.val_inj.mp <|
    (restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩).trans (h x hx) , _⟩).trans
      AlgEquiv.ext_iff.symm).trans (MonoidHom.mem_ker (restrictNormalHom (fixedField H))).symm
  intro h x hx
  dsimp
  have hs : ((restrictNormalHom (fixedField H)) σ) ⟨x, hx⟩ = σ x :=
    restrictNormal_commutes σ (fixedField H) ⟨x, hx⟩
  rw [← hs]
  exact Subtype.val_inj.mpr (h ⟨x, hx⟩)

end Galois



namespace Polynomial

variable {R : Type*} (S L : Type*) [CommRing R] [CommRing S] [IsDomain S] [CommRing L] [IsDomain L]
[Algebra R L] [Algebra S L] [Algebra R S] [IsScalarTower R S L] [IsIntegralClosure S R L]


open Multiset

/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the roots of `p`in `L`
are equal to the roots of `p` in the integral closure of `R` in `L`. -/
theorem isIntegralClosure_root_eq_ofMonic {p : R[X]} (hp : p.Monic):
    (map (algebraMap R S) p).roots.map (algebraMap S L) = (map (algebraMap R L) p).roots := by
  classical
  ext x
  by_cases hx : ∃ y : S, algebraMap S L y = x
  · rcases hx with ⟨y, h⟩
    have hc : algebraMap R L = (algebraMap S L).comp (algebraMap R S) :=
      IsScalarTower.algebraMap_eq R S L
    have hi : Function.Injective (algebraMap S L) := IsIntegralClosure.algebraMap_injective S R L
    rw [← h, count_map_eq_count' _ _ hi _]
    rw [count_roots, count_roots, hc, ← map_map, ← eq_rootMultiplicity_map hi]
  · have h : count x ((p.map (algebraMap R S)).roots.map (algebraMap S L)) = 0 := by
      simp only [mem_map, mem_roots', ne_eq, IsRoot.def, Subtype.exists, not_exists,
        not_and, and_imp, count_eq_zero]
      intro y _ _ h
      exact hx ⟨y, h⟩
    rw [h]
    exact Decidable.byContradiction fun h ↦ hx <| IsIntegralClosure.isIntegral_iff.mp
      ⟨p, hp, (eval₂_eq_eval_map (algebraMap R L)).trans <|
        (mem_roots (hp.map (algebraMap R L)).ne_zero).1 (count_ne_zero.mp (Ne.symm h))⟩

/-- If `L` be an extension of `R`, then for a monic polynomial `p : R[X]`, the number of roots
of `p` in `L` is equal to the number of roots of `p` in the integral closure of `R` in `L`. -/
theorem isIntegralClosure_root_card_eq_ofMonic {p : R[X]} (hp : p.Monic) :
    card (map (algebraMap R S) p).roots = card (map (algebraMap R L) p).roots := by
  rw [← isIntegralClosure_root_eq_ofMonic S L hp, card_map]

/-- A variant of the theorem `roots_map_of_injective_of_card_eq_natDegree` that replaces the
injectivity condition with the condition `Polynomial.map f p ≠ 0`. -/
theorem roots_map_of_card_eq_natDegree {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0)
    (hroots : card p.roots = p.natDegree) : p.roots.map f  = (map f p).roots := by
  apply eq_of_le_of_card_le (map_roots_le h)
  simpa only [card_map, hroots] using (card_roots' (map f p)).trans (natDegree_map_le f p)

end Polynomial



namespace Ideal

/-- If the product of a finite number of elements in the commutative semiring `R` lies in the
prime ideal `p`, then at least one of those elements is in `p`. -/
theorem IsPrime.prod_mem {R ι : Type*} [CommSemiring R] {p : Ideal R} [hp : p.IsPrime]
    {s : Finset ι} {x : ι → R} (h : ∏ i in s, x i ∈ p) : ∃ i : s, x i ∈ p := by
  classical
  induction' s using Finset.induction_on with n s nns hn
  · rw [Finset.prod_empty] at h
    rw [IsEmpty.exists_iff]
    exact IsPrime.ne_top hp ((eq_top_iff_one p).mpr h)
  · rw [Finset.prod_insert nns] at h
    rcases IsPrime.mem_or_mem hp h with h|h
    use ⟨n, Finset.mem_insert_self n s⟩
    rcases hn h with ⟨i, hi⟩
    use ⟨i, Finset.mem_insert_of_mem i.2⟩

open Module Module.Finite

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite R S] (p : Ideal S)

instance : IsScalarTower R (R ⧸ comap (algebraMap R S) p) (S ⧸ p) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- If `S` is a finite `R`-module, then `S ⧸ p` is a finite
`R ⧸ comap (algebraMap R S) p`-module. -/
instance quotient_finite_quotient_comap : Finite (R ⧸ comap (algebraMap R S) p) (S ⧸ p) :=
  of_restrictScalars_finite R (R ⧸ comap (algebraMap R S) p) (S ⧸ p)

end Ideal



open Ideal

attribute [local instance] Ideal.Quotient.field

/-- If `p` is a non-zero ideal of the `ℤ`, then `ℤ ⧸ p` is finite. -/
noncomputable def Int.Quotient.Fintype_of_ne_bot {p : Ideal ℤ} (hp : p ≠ ⊥) :
    Fintype (ℤ ⧸ p) := by
  have h := Int.quotientSpanEquivZMod (Submodule.IsPrincipal.generator p)
  rw [span_singleton_generator p] at h
  have : NeZero (Int.natAbs (Submodule.IsPrincipal.generator p)) := ⟨fun eq ↦
    hp ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr (Int.natAbs_eq_zero.mp eq))⟩
  exact Fintype.ofEquiv (ZMod (Int.natAbs (Submodule.IsPrincipal.generator p))) h.symm

/-- In particular, if `p` is a maximal ideal of the `ℤ`, then `ℤ ⧸ p` is a finite field. -/
noncomputable instance Int.Quotient.Fintype_ofIsMaximal (p : Ideal ℤ) [hpm : p.IsMaximal] :
    Fintype (ℤ ⧸ p) :=
  Fintype_of_ne_bot (Ring.ne_bot_of_isMaximal_of_not_isField hpm Int.not_isField)



namespace NumberField

section preparation

variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]

/-- A finite extension of a number field is a number field. -/
theorem of_finite_extension [FiniteDimensional K L] : NumberField L where
  to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
  to_finiteDimensional :=
    letI := charZero_of_injective_algebraMap (algebraMap K L).injective
    Module.Finite.trans K L

variable [NumberField L]

/-- Any extension of a Number Field is a finite extension. -/
instance Extension.FiniteDimensional : FiniteDimensional K L :=
  Module.Finite.of_restrictScalars_finite ℚ K L

instance of_IntermediateField {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (E : IntermediateField K L) : NumberField E := of_finite_extension K E

theorem of_tower (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] :
    NumberField E :=
  letI := FiniteDimensional.left K E L
  of_finite_extension K E

variable (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]

instance : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

lemma ringOfIntegers_algebra_isIntegral (K : Type*) [Field K] : Algebra.IsIntegral ℤ (𝓞 K) :=
  IsIntegralClosure.isIntegral_algebra ℤ K

lemma isIntegral_tower {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (x : L)
    (hx : IsIntegral (𝓞 K) x) : IsIntegral ℤ x :=
  letI := ringOfIntegers_algebra_isIntegral K
  isIntegral_trans x hx

/-- The instance form of theorem `ringOfIntegers_eq_integralClosure`. -/
instance extension_ringOfIntegers.isIntegralClosure [NumberField L] : IsIntegralClosure (𝓞 L) (𝓞 K) L where
  algebraMap_injective' := IsFractionRing.injective (𝓞 L) L
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      use ⟨x, isIntegral_tower x hx⟩
      rfl
    · intro ⟨⟨y,hy⟩, hxy⟩
      rw [← hxy]
      exact IsIntegral.tower_top hy

/-- Any Extension between ring of integers is integral. -/
instance extension_ringOfIntegers.isIntegral [NumberField L] : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  IsIntegralClosure.isIntegral_algebra (𝓞 K) L

/-- In particular, any Extension between ring of integers is noetherian. -/
instance extension_ringOfIntegers.isNoetherian [NumberField K] [NumberField L] :
  IsNoetherian (𝓞 K) (𝓞 L) := IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)

/-- The kernel of the algebraMap between ring of integers is `⊥`. -/
theorem algebraMap_ker_eq_bot :
    RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) = ⊥ := by
  apply (RingHom.ker_eq_bot_iff_eq_zero (algebraMap (𝓞 K) (𝓞 L))).mpr
  intro x hx
  have h: (algebraMap K L) x = (algebraMap (𝓞 K) (𝓞 L)) x := rfl
  simp only [hx, map_zero, map_eq_zero, RingOfIntegers.coe_eq_zero_iff] at h
  exact h

/-- The algebraMap between ring of integers is injective. -/
theorem algebraMap.injective : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
  (RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 K) (𝓞 L))).mpr (algebraMap_ker_eq_bot K L)

instance instIsScalarTower_IntermediateField_ringOfIntegers (E : IntermediateField K L) :
  IsScalarTower (𝓞 K) (𝓞 E) (𝓞 L) := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

instance instIsScalarTower_ringOfIntegers (E L : Type*) [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] :
    IsScalarTower (𝓞 K) (𝓞 E) (𝓞 L) := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  apply Subtype.val_inj.mp
  calc _ = algebraMap K L x.1 := rfl
    _ = _ := by
      rw [IsScalarTower.algebraMap_eq K E L]
      rfl

variable {L : Type*} [Field L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))

/-- The ideal obtained by intersecting `𝓞 K` and `P`. -/
abbrev IdealBelow : Ideal (𝓞 K) := comap (algebraMap (𝓞 K) (𝓞 L)) P

theorem IdealBelow_def : IdealBelow K P = comap (algebraMap (𝓞 K) (𝓞 L)) P := rfl

instance IdealBelow.IsPrime [P.IsPrime] : IsPrime (IdealBelow K P) :=
  IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (P : Ideal (𝓞 L)) (p : Ideal (𝓞 K))

/-- We say `P` lies over `p` if `p` is the preimage of `P` under the `algebraMap`. -/
class ideal_lies_over : Prop where over : p = comap (algebraMap (𝓞 K) (𝓞 L)) P

infix : 50 "lies_over" => ideal_lies_over

instance over_IdealBelow : P lies_over (IdealBelow K P) where over := rfl

theorem over_def {p : Ideal (𝓞 K)} {P : Ideal (𝓞 L)} (h : p = IdealBelow K P) :
  P lies_over p where over := h

class ideal_unique_lies_over extends ideal_lies_over P p : Prop where
  unique : ∀ Q : Ideal (𝓞 L), [Q.IsMaximal] → [Q lies_over p] → Q = P

infix : 50 "unique_lies_over" => ideal_unique_lies_over

variable [NumberField L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
[P lies_over p]

/-- If `P` is a maximal ideal of `𝓞 L`, then the intersection of `P` and `𝓞 K` is also
a maximal ideal. -/
instance IdealBelow.IsMaximal : IsMaximal (IdealBelow K P) :=
  isMaximal_comap_of_isIntegral_of_isMaximal P

/-- In particular, if `p` is a maximal ideal of `ringOfIntegers`, then
the intersection of `p` and `ℤ` is also a maximal ideal. -/
instance Ideal_comap_int.IsMaximal [NumberField K] (p : Ideal (𝓞 K)) [p.IsMaximal] :
  IsMaximal (comap (algebraMap ℤ (𝓞 K)) p) := isMaximal_comap_of_isIntegral_of_isMaximal p

/-- For any maximal idela `p` in `𝓞 K`, there exists a maximal ideal in `𝓞 L` lying over `p`. -/
theorem exists_ideal_over_maximal_of_ringOfIntegers (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    ∃ (P : Ideal (𝓞 L)), IsMaximal P ∧ P lies_over p := by
  rcases exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) p
    (by simp only [algebraMap_ker_eq_bot K L, bot_le]) with ⟨P, hpm, hp⟩
  exact ⟨P, hpm, over_def hp.symm⟩

/-- Maximal Ideals in the ring of integers are non-zero. -/
theorem ne_bot_ofIsMaximal [NumberField K] : p ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)

/-- The image of a maximal ideal under the algebraMap between ring of integers is non-zero. -/
theorem map_isMaximal_ne_bot [NumberField K] (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [Algebra K L] : map (algebraMap (𝓞 K) (𝓞 L)) p ≠ ⊥ :=
  fun h ↦ (ne_bot_ofIsMaximal p) ((map_eq_bot_iff_of_injective (algebraMap.injective K L)).mp h)

theorem prime_iff_isMaximal (P : Ideal (𝓞 L)) : Prime P ↔ IsMaximal P :=
  ⟨fun hp ↦ IsPrime.isMaximal (isPrime_of_prime hp) (Prime.ne_zero hp),
    fun hp ↦ prime_of_isPrime (ne_bot_ofIsMaximal P) (IsMaximal.isPrime hp)⟩

/-- The `Finset` consists of all primes lying over `p : Ideal (𝓞 K)`. -/
noncomputable abbrev primes_over {K : Type*} [Field K] (p : Ideal (𝓞 K))
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : Finset (Ideal (𝓞 L)) := by
  classical exact (UniqueFactorizationMonoid.factors (map (algebraMap (𝓞 K) (𝓞 L)) p)).toFinset

open UniqueFactorizationMonoid

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]

theorem primes_over_mem :
    P ∈ primes_over p L ↔ P.IsMaximal ∧ P lies_over p := by
  constructor
  · intro hp
    classical have hp := Multiset.mem_toFinset.mp hp
    have hpm := (prime_iff_isMaximal P).mp (prime_of_factor P hp)
    exact ⟨hpm, over_def <| IsMaximal.eq_of_le inferInstance (comap_ne_top _ (IsMaximal.ne_top hpm))
      (le_comap_of_map_le (le_of_dvd (dvd_of_mem_factors hp)))⟩
  · intro ⟨hpm, hp⟩
    have hd := dvd_iff_le.mpr (map_le_of_le_comap (le_of_eq hp.over))
    have hir := irreducible_iff_prime.mpr ((prime_iff_isMaximal P).mpr hpm)
    rcases exists_mem_factors_of_dvd (map_isMaximal_ne_bot p L) hir hd with ⟨_, hq, he⟩
    classical rw [Multiset.mem_toFinset, associated_iff_eq.mp he]
    exact hq

instance primes_over_instIsMaximal (Q : primes_over p L) : IsMaximal Q.1 :=
  ((primes_over_mem p Q.1).mp Q.2).1

instance primes_over_inst_lies_over (Q : primes_over p L) : Q.1 lies_over p :=
  ((primes_over_mem p Q.1).mp Q.2).2

/-- Given a maximal ideal `P lies_over p` in `𝓞 L`, `primes_over.mk` sends `P` to an element of
the subset `primes_over p L` of `Ideal (𝓞 L)`.  -/
abbrev primes_over.mk [P.IsMaximal] [P lies_over p] : primes_over p L :=
  ⟨P, (primes_over_mem p P).mpr ⟨inferInstance, inferInstance⟩⟩

theorem primes_over_card_ne_zero (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    Finset.card (primes_over p L) ≠ 0 := by
  rcases exists_ideal_over_maximal_of_ringOfIntegers p L with ⟨P, hp⟩
  exact Finset.card_ne_zero_of_mem ((primes_over_mem p P).mpr hp)

/-- The `Finset` consists of all primes lying over `IdealBelow K P`, i.e., all the primes `Q` such
that `IdealBelow K Q = IdealBelow K P`. -/
noncomputable abbrev primes_same_bleow : Finset (Ideal (𝓞 L)) := primes_over (IdealBelow K P) L

theorem Nonsplit_iff_primes_over_card_eq_one :
    Nonsplit (algebraMap (𝓞 K) (𝓞 L)) p ↔ Finset.card (primes_over p L) = 1 := by
  have h : Finset.card (primes_over p L) = 1 ↔ Finset.card (primes_over p L) ≤ 1 :=
    ⟨fun h ↦ Nat.le_of_eq h ,
      fun h ↦ Nat.le_antisymm h (Nat.one_le_iff_ne_zero.mpr (primes_over_card_ne_zero p L))⟩
  simp only [h, Finset.card_le_one, primes_over_mem, and_imp]
  exact ⟨fun h P hpm hp Q hqm hq ↦ h.nonsplit P hpm hp.over Q hqm hq.over,
    fun h ↦ {nonsplit := fun P hpm hp Q hqm hq ↦ h P hpm (over_def hp) Q hqm (over_def hq)}⟩

theorem unique_lies_over.Nonsplit {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hp : P unique_lies_over p] :
    Nonsplit (algebraMap (𝓞 K) (𝓞 L)) p where
  nonsplit Q1 _ hq1 Q2 _ hq2 := by
    letI := over_def hq1
    letI := over_def hq2
    rw [hp.unique Q1, hp.unique Q2]

/-- Another form of the property `unique_lies_over`. -/
theorem unique_primes_over_card_eq_one (P : Ideal (𝓞 L)) [P unique_lies_over p]:
    Finset.card (primes_over p L) = 1 :=
  (Nonsplit_iff_primes_over_card_eq_one p).mp (unique_lies_over.Nonsplit p P)



variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {E : Type*} [Field E]
[NumberField E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
(p : Ideal (𝓞 K)) (𝔓 : Ideal (𝓞 E)) (P : Ideal (𝓞 L))

theorem ideal_lies_over.trans [hp : 𝔓 lies_over p] [hP : P lies_over 𝔓] : P lies_over p where
  over := by rw [hp.over, hP.over, comap_comap, ← IsScalarTower.algebraMap_eq]

theorem ideal_lies_over_tower_bot [hp : P lies_over p] [hP : P lies_over 𝔓] : 𝔓 lies_over p where
  over := by rw [hp.over, hP.over, comap_comap, ← IsScalarTower.algebraMap_eq]

theorem ideal_unique_lies_over.trans [hp : 𝔓 unique_lies_over p] [hP : P unique_lies_over 𝔓] :
  P unique_lies_over p := { ideal_lies_over.trans p 𝔓 P with
    unique := fun Q _ _ ↦
      letI := ideal_lies_over_tower_bot p (IdealBelow E Q) Q
      letI := over_def (hp.unique (IdealBelow E Q)).symm
      hP.unique Q
}

theorem ideal_unique_lies_over_tower_bot [hp : P unique_lies_over p] [hP : P lies_over 𝔓] :
  𝔓 unique_lies_over p := { ideal_lies_over_tower_bot p 𝔓 P with
    unique := by
      intro 𝔔 _ _
      rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔔 L with ⟨Q, ⟨hqm ,hq⟩⟩
      letI := ideal_lies_over.trans p 𝔔 Q
      letI := hp.unique Q
      rw [hq.over, hp.unique Q, hP.over]
}

theorem ideal_unique_lies_over_tower_top [𝔓.IsMaximal] [hP : P unique_lies_over p]
  [𝔓 lies_over p] : P unique_lies_over 𝔓 where
    over := by
      rcases exists_ideal_over_maximal_of_ringOfIntegers 𝔓 L with ⟨Q, ⟨_ ,hq⟩⟩
      letI := ideal_lies_over.trans p 𝔓 Q
      rw [← hP.unique Q, hq.over]
    unique := fun Q _ _ ↦
      letI := ideal_lies_over.trans p 𝔓 Q
      hP.unique Q

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P lies_over p] (E : IntermediateField K L)

instance IntermediateField_ideal_lies_over : (IdealBelow E P) lies_over p :=
  ideal_lies_over_tower_bot p (IdealBelow E P) P

theorem Ideal_comap_IntermediateField : p = comap (algebraMap (𝓞 K) (𝓞 E)) (IdealBelow E P) :=
  (IntermediateField_ideal_lies_over p P E).over

instance IntermediateField_ideal_unique_lies_over (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [P unique_lies_over p] (E : IntermediateField K L) : (IdealBelow E P) unique_lies_over p :=
  ideal_unique_lies_over_tower_bot p (IdealBelow E P) P

end preparation



section decomposition

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
[p.IsMaximal] [hpm : P.IsMaximal] [hp : P lies_over p]

/-- If `P` lies over `p`, then the residue class field of `p` has a canonical map to
the residue class field of `P`. -/
instance residue_field_instAlgebra : Algebra ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hp.over)

instance : IsScalarTower (𝓞 K) ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- The extension between residue class fields is finite. -/
instance residue_field_instFiniteDimensional {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [P lies_over p] : FiniteDimensional ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  Module.Finite.of_restrictScalars_finite (𝓞 K) ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)

theorem inertiaDeg_pos {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [P lies_over p]: inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P > 0 := by
  rw [inertiaDeg_algebraMap]
  letI : NoZeroSMulDivisors (𝓞 K ⧸ p) (𝓞 L ⧸ P) := NoZeroSMulDivisors.Algebra.noZeroSMulDivisors
  exact FiniteDimensional.finrank_pos


-- Hilbert's Ramification Theory

def RingOfIntegers.mapRingHom {K L F : Type*} [Field K] [Field L] [FunLike F K L]
    [RingHomClass F K L] (f : F) : (𝓞 K) →+* (𝓞 L) where
  toFun k := ⟨f k, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [RingOfIntegers.map_mk, map_zero]
  map_one' := by ext; simp only [RingOfIntegers.map_mk, map_one]
  map_add' x y:= by ext; simp only [RingOfIntegers.map_mk, map_add]
  map_mul' x y := by ext; simp only [RingOfIntegers.map_mk, _root_.map_mul]

def RingOfIntegers.mapAlgHom {k K L F : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FunLike F K L] [AlgHomClass F k K L] (f : F) : (𝓞 K) →ₐ[𝓞 k] (𝓞 L) where
  toRingHom := mapRingHom f
  commutes' x := SetCoe.ext (AlgHomClass.commutes ((f : K →ₐ[k] L).restrictScalars (𝓞 k)) x)

/-- The `AlgEquiv` of elements of Galois group `Gal(K/L)` restricted to `𝓞 L`. -/
def GalAlgEquiv (σ : L ≃ₐ[K] L) : (𝓞 L) ≃ₐ[𝓞 K] (𝓞 L) :=
  AlgEquiv.ofAlgHom (RingOfIntegers.mapAlgHom σ) (RingOfIntegers.mapAlgHom σ.symm)
    (by ext; simp [RingOfIntegers.mapAlgHom, RingOfIntegers.mapRingHom])
      (by ext; simp [RingOfIntegers.mapAlgHom, RingOfIntegers.mapRingHom])

theorem GalAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) : (GalAlgEquiv σ x).1 = σ x.1 := rfl

/-- Consider `GalAlgEquiv σ` as a ring homomorphism. -/
def GalRingHom (σ : L ≃ₐ[K] L) : RingHom (𝓞 L) (𝓞 L) := RingOfIntegers.mapRingHom σ

theorem GalAlgEquiv_toAlgHom_toRingHom_eq_GalRingHom (σ : L ≃ₐ[K] L) : (GalAlgEquiv σ).toAlgHom.toRingHom = GalRingHom σ := rfl

theorem GalRingHom_mul (σ τ : L ≃ₐ[K] L) :
  (GalRingHom σ).comp (GalRingHom τ) = GalRingHom (σ * τ) := rfl

theorem GalRingHom_one : GalRingHom (1 : L ≃ₐ[K] L) = RingHom.id (𝓞 L) := rfl

theorem GalRingHom_inv_mul_cancel (σ : L ≃ₐ[K] L) : (GalRingHom σ⁻¹).comp (GalRingHom σ)
  = RingHom.id (𝓞 L) := by rw [GalRingHom_mul, inv_mul_cancel, GalRingHom_one]

theorem GalRingHom_inv_mul_cancel_mem (σ : L ≃ₐ[K] L) (x : 𝓞 L):
    GalRingHom σ⁻¹ (GalRingHom σ x) = x := by
  calc _ = (GalRingHom σ⁻¹).comp (GalRingHom σ) x := rfl
    _ = _ := by rw [GalRingHom_inv_mul_cancel, RingHom.id_apply]

theorem GalRingHom_mul_inv_cancel (σ : L ≃ₐ[K] L) : (GalRingHom σ).comp (GalRingHom σ⁻¹)
  = RingHom.id (𝓞 L) := by rw [GalRingHom_mul, mul_inv_cancel, GalRingHom_one]

theorem GalRingHom_mul_inv_cancel_mem (σ : L ≃ₐ[K] L) (x : 𝓞 L):
    GalRingHom σ (GalRingHom σ⁻¹ x) = x := by
  calc _ = (GalRingHom σ).comp (GalRingHom σ⁻¹) x := rfl
    _ = _ := by rw [GalRingHom_mul_inv_cancel, RingHom.id_apply]

/-- The `GalRingHom σ` will send a maximal ideal to a maximal ideal. -/
instance GalRingHom_map.isMaximal (σ : L ≃ₐ[K] L) : IsMaximal (map (GalRingHom σ) P) :=
  Quotient.maximal_of_isField _ <| MulEquiv.isField _ (Field.toIsField ((𝓞 L) ⧸ P))
    (quotientEquiv P (map (GalRingHom σ) P) (GalAlgEquiv σ) rfl).symm.toMulEquiv

-- Propsition 9.1

/-- The Galois group `Gal(K/L)` acts transitively on the set of all maximal ideals `P` of `𝓞 L`
lying above `p`, i.e., these prime ideals are all conjugates of each other. -/
theorem IsMaximal_conjugates {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hpm : P.IsMaximal] [hp : P lies_over p]
    (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [hq : Q lies_over p]
    [IsGalois K L] : ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q := by
  by_contra hs
  push_neg at hs
  let s : Finset (L ≃ₐ[K] L) := Finset.univ
  rcases Submodule.mem_sup.mp <| (eq_top_iff_one (Q ⊔ ∏ σ in s, map (GalRingHom σ) P)).mp <|
    sup_prod_eq_top <| fun σ _ ↦ IsMaximal.coprime_of_ne hqm (GalRingHom_map.isMaximal P σ)
      (hs σ).symm with ⟨x, hx, y, hy, hxy⟩
  let n : 𝓞 L := ∏ σ in s, (GalRingHom σ) x
  have hnx : n = (algebraMap (𝓞 K) (𝓞 L)) (RingOfIntegers.norm K x) :=
    Subtype.val_inj.mp <| Eq.trans
      (Submonoid.coe_finset_prod (integralClosure ℤ L).toSubmonoid (fun i ↦ (GalRingHom i) x) s)
        (Algebra.norm_eq_prod_automorphisms K x.1).symm
  have hnk : RingOfIntegers.norm K x ∈ IdealBelow K P := by
    rw [IdealBelow, ← hp.over, hq.over]
    apply mem_comap.mpr
    rw [← hnx]
    refine (span_singleton_le_iff_mem Q).mp ?_
    rw [← prod_span_singleton]
    exact prod_le_inf.trans <| (@Finset.inf_le _ _ _ _ s (fun σ ↦ span {(GalRingHom σ) x}) _
      (@Finset.mem_univ (L ≃ₐ[K] L) _ 1)).trans (Iff.mpr (span_singleton_le_iff_mem Q) hx)
  have hnp : n ∈ P := Eq.mpr (_root_.id (hnx ▸ Eq.refl (n ∈ P))) hnk
  rcases IsPrime.prod_mem hnp with ⟨⟨σ, _⟩, hs⟩
  have hxp : x ∈ map (GalRingHom σ⁻¹) P := Eq.mpr
    ((GalRingHom_inv_mul_cancel_mem σ x).symm ▸ Eq.refl _) (mem_map_of_mem (GalRingHom σ⁻¹) hs)
  have h := Ideal.add_mem (map (GalRingHom σ⁻¹) P) hxp <|
    (prod_le_inf.trans (Finset.inf_le (Finset.mem_univ σ⁻¹))) hy
  rw [hxy] at h
  exact IsMaximal.ne_top (GalRingHom_map.isMaximal P σ⁻¹) ((eq_top_iff_one _).mpr h)

theorem IsMaximal_conjugates' {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] {P : Ideal (𝓞 L)} [P.IsMaximal] {Q : Ideal (𝓞 L)} [Q.IsMaximal]
    [IsGalois K L] (h : IdealBelow K P = IdealBelow K Q) :
    ∃ σ : L ≃ₐ[K] L, map (GalRingHom σ) P = Q :=
  letI := over_def h
  IsMaximal_conjugates (IdealBelow K P) P Q



open UniqueFactorizationMonoid IsDedekindDomain

/-- The function normalizedFactors commutes with the function `map (GalRingHom σ)`. -/
theorem normalizedFactors_map_GalRingHom_commutes {K L : Type*} [Field K] [Field L]
    [NumberField L] [Algebra K L] {I : Ideal (𝓞 L)} (hI : I ≠ ⊥) (σ : L ≃ₐ[K] L) :
    normalizedFactors (map (GalRingHom σ) I) =
    Multiset.map (map (GalRingHom σ)) (normalizedFactors I) := by
  nth_rw 1 [← prod_normalizedFactors_eq_self hI]
  have h := Multiset.prod_hom (normalizedFactors I) (mapHom (GalRingHom σ))
  simp only [mapHom_apply] at h
  rw [← h, normalizedFactors_prod_of_prime]
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨p, hp, hpq⟩
  have : IsMaximal p := (prime_iff_isMaximal p).mp (prime_of_normalized_factor p hp)
  rw [← hpq]
  exact (prime_iff_isMaximal (map (GalRingHom σ) p)).mpr (GalRingHom_map.isMaximal p σ)

/-- The image of an ideal under the algebraMap between ring of integers remains invariant
under the action of `GalRingHom σ`. -/
theorem Ideal_map_invariant_under_GalRingHom (p : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) :
    (map (GalRingHom σ)) (map (algebraMap (𝓞 K) (𝓞 L)) p) = map (algebraMap (𝓞 K) (𝓞 L)) p := by
  apply le_antisymm <| map_le_of_le_comap <| map_le_of_le_comap <|
    fun _ h ↦ by simp only [← GalAlgEquiv_toAlgHom_toRingHom_eq_GalRingHom,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, mem_comap, RingHom.coe_coe,
        AlgHom.commutes, mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) h]
  apply map_le_of_le_comap
  intro x h
  rw [mem_comap, map_map]
  apply Set.mem_of_eq_of_mem _ (mem_map_of_mem ((GalRingHom σ).comp (algebraMap (𝓞 K) (𝓞 L))) h)
  rw [GalRingHom, ← AlgEquiv.commutes (GalAlgEquiv σ) x]
  rfl

/-- The map induced by `GalRingHom σ` on the ideals of `𝓞 L` is injective. -/
theorem GalRingHom_IdealMap.injective (σ : L ≃ₐ[K] L): Function.Injective (map (GalRingHom σ)) :=
  fun I J h ↦ by rw [← map_id I, ← GalRingHom_inv_mul_cancel σ, ← map_map, h, map_map,
    GalRingHom_inv_mul_cancel σ, map_id]

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P lies_over p]

/-- In the case of Galois extension, all the `ramificationIdx` are the same. -/
theorem ramificationIdx_eq_of_isGalois (Q : Ideal (𝓞 L)) [hqm : Q.IsMaximal] [Q lies_over p]
    [IsGalois K L] : ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P =
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  classical
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L) inferInstance
    (ne_bot_ofIsMaximal P), ramificationIdx_eq_normalizedFactors_count (map_isMaximal_ne_bot p L)
    (IsMaximal.isPrime hqm) (ne_bot_ofIsMaximal Q), ← hs]
  nth_rw 2 [← Ideal_map_invariant_under_GalRingHom p σ]
  rw [normalizedFactors_map_GalRingHom_commutes (map_isMaximal_ne_bot p L) σ]
  rw [Multiset.count_map_eq_count' _ _ (GalRingHom_IdealMap.injective σ) _]

theorem ramificationIdx_eq_of_isGalois' [IsGalois K L] {P : Ideal (𝓞 L)} [P.IsMaximal]
    {Q : Ideal (𝓞 L)} [hqm : Q.IsMaximal] (h : IdealBelow K P = IdealBelow K Q) :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (IdealBelow K P) P =
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) (IdealBelow K Q) Q := by
  letI := over_def h
  rw [← h]
  exact ramificationIdx_eq_of_isGalois (IdealBelow K P) P Q

theorem IdealBelow_invariant_under_GalRingHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [hp : P lies_over p] (σ : L ≃ₐ[K] L) :
    p = IdealBelow K (map (GalRingHom σ) P) := by
  ext x
  rw [mem_comap, hp.over, mem_comap]
  refine ⟨fun h ↦ Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ).commutes x]; rfl)
    (mem_map_of_mem (GalRingHom σ) h), fun h ↦ ?_⟩
  have h := mem_map_of_mem (GalRingHom σ⁻¹) h
  rw [map_map, GalRingHom_inv_mul_cancel, map_id] at h
  exact Set.mem_of_eq_of_mem (by nth_rw 1 [← (GalAlgEquiv σ⁻¹).commutes x]; rfl) h

instance GalRingHom_map_lies_over (σ : L ≃ₐ[K] L) : (map (GalRingHom σ) P) lies_over p :=
  over_def (IdealBelow_invariant_under_GalRingHom p P σ)

/-- The algebra equiv `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ map (GalRingHom σ) P)`
induced by an algebra equiv `σ : L ≃ₐ[K] L`. -/
def residueField_GalAlgEquiv {P : Ideal (𝓞 L)} [P.IsMaximal] [P lies_over p] {Q : Ideal (𝓞 L)}
    [Q.IsMaximal] [Q lies_over p] {σ : L ≃ₐ[K] L} (hs: map (GalRingHom σ) P = Q) :
    ((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ Q) := {
  quotientEquiv P Q (GalAlgEquiv σ) (by rw [← hs]; rfl) with
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgEquiv.commutes (GalAlgEquiv σ) x)
}

/-- In the case of Galois extension, all the `inertiaDeg` are the same. -/
theorem inertiaDeg_eq_of_isGalois (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q lies_over p] [IsGalois K L] :
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p Q := by
  rcases IsMaximal_conjugates p P Q with ⟨σ, hs⟩
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  exact LinearEquiv.finrank_eq (residueField_GalAlgEquiv p hs).toLinearEquiv

/-- In the case of Galois extension, it can be seen from the Theorem `ramificationIdx_eq_of_IsGalois`
that all `ramificationIdx` are the same, which we define as the `ramificationIdx_of_isGalois`. -/
noncomputable def ramificationIdx_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p <|
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/-- In the case of Galois extension, it can be seen from the Theorem `inertiaDeg_eq_of_IsGalois`
that all `inertiaDeg` are the same, which we define as the `inertiaDeg_of_isGalois`. -/
noncomputable def inertiaDeg_of_isGalois (p : Ideal (𝓞 K)) [p.IsMaximal]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] : ℕ :=
  inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p <|
    Classical.choose (exists_ideal_over_maximal_of_ringOfIntegers p L)

/-- In the case of Galois extension, all ramification indices are equal to the
`ramificationIdx_of_isGalois`. This completes the property mentioned in our previous definition. -/
theorem ramificationIdx_eq_ramificationIdx_of_isGalois [IsGalois K L] :
    ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P = ramificationIdx_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [ramificationIdx_of_isGalois]
  exact ramificationIdx_eq_of_isGalois p P _

/-- In the case of Galois extension, all inertia degrees are equal to the `inertiaDeg_of_isGalois`.
This completes the property mentioned in our previous definition. -/
theorem inertiaDeg_eq_inertiaDeg_of_isGalois [IsGalois K L] :
    inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P = inertiaDeg_of_isGalois p L := by
  rcases Classical.choose_spec (exists_ideal_over_maximal_of_ringOfIntegers p L) with ⟨_, _⟩
  rw [inertiaDeg_of_isGalois]
  exact inertiaDeg_eq_of_isGalois p P _

/-- The form of the **fundamental identity** in the case of Galois extension. -/
theorem ramificationIdx_mul_inertiaDeg_of_isGalois (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    Finset.card (primes_over p L) * (ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L) =
    FiniteDimensional.finrank K L := by
  rw [← smul_eq_mul, ← Finset.sum_const]
  rw [← sum_ramification_inertia (R := 𝓞 K) (S := 𝓞 L) p K L (ne_bot_ofIsMaximal p)]
  apply Finset.sum_congr rfl
  intro P hp
  letI := ((primes_over_mem p P).mp hp).1
  letI := ((primes_over_mem p P).mp hp).2
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois, inertiaDeg_eq_inertiaDeg_of_isGalois]



-- Definition 9.2

open MulAction

/-- The `MulAction` of the Galois group `L ≃ₐ[K] L` on the set `primes_over p L`,
given by `σ ↦ (P ↦ σ P)`. -/
instance Gal_MulAction_primes (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (primes_over p L) where
  smul σ Q := primes_over.mk p (map (GalRingHom σ) Q.1)
  one_smul Q :=
    have h : primes_over.mk p (map (GalRingHom (1 : L ≃ₐ[K] L)) Q.1) = Q := by
      simp only [← Subtype.val_inj, GalRingHom_one, map_id]
    h
  mul_smul σ τ Q :=
    have h : primes_over.mk p (map (GalRingHom (σ * τ)) Q.1) =
        primes_over.mk p (map (GalRingHom σ) (primes_over.mk p (map (GalRingHom τ) Q.1)).1) := by
      simp only [← Subtype.val_inj, map_map, GalRingHom_mul]
    h

theorem Gal_MulAction_primes_mk_coe (σ : L ≃ₐ[K] L) :
  (σ • primes_over.mk p P).1 = map (GalRingHom σ) P := rfl

/-- The decomposition group of `P` over `K`, is the stabilizer of `primes_over.mk p P`
under the action `Gal_MulAction_primes`. -/
def DecompositionGroup : Subgroup (L ≃ₐ[K] L) := stabilizer _ (primes_over.mk p P)

/-- The `DecompositionGroup` is consisting of all elements of the Galois group `L ≃ₐ[K] L` such
that keep `P` invariant. -/
theorem DecompositionGroup_mem (σ : L ≃ₐ[K] L) :
    σ ∈ DecompositionGroup p P ↔ map (GalRingHom σ) P = P := by
  rw [DecompositionGroup, mem_stabilizer_iff, ← Subtype.val_inj, Gal_MulAction_primes_mk_coe]

open IntermediateField FiniteDimensional

/-- The decomposition field of `P` over `K` is the fixed field of `DecompositionGroup p P`. -/
def DecompositionField : IntermediateField K L := fixedField (DecompositionGroup p P)

/-- DecompositionField is a Number Field. -/
instance DecompositionField_NumberField : NumberField (DecompositionField p P) :=
  of_IntermediateField (DecompositionField p P)

/-- The ideal equal to the intersection of `P` and `DecompositionField p P`. -/
abbrev DecompositionIdeal : Ideal (𝓞 (DecompositionField p P)) :=
  IdealBelow (DecompositionField p P) P

instance DecompositionIdeal.isMaximal : IsMaximal (DecompositionIdeal p P) :=
  IdealBelow.IsMaximal P




-- Proposition 9.3

open Classical

theorem DecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg [IsGalois K L] :
    Fintype.card (DecompositionGroup p P) =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  apply mul_left_cancel₀ (primes_over_card_ne_zero p L)
  have : Fintype (orbit (L ≃ₐ[K] L) (primes_over.mk p P)) :=
    Set.fintypeRange fun m ↦ m • primes_over.mk p P
  rw [ramificationIdx_mul_inertiaDeg_of_isGalois, ← IsGalois.card_aut_eq_finrank, DecompositionGroup]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (L ≃ₐ[K] L) (primes_over.mk p P)]
  congr 1
  · rw [Fintype.card_of_finset' (@Finset.univ (primes_over p L) _), Finset.card_univ]
    · exact (Fintype.card_coe (primes_over p L)).symm
    · intro Q
      simp only [Finset.univ_eq_attach, Finset.mem_attach, true_iff, MulAction.mem_orbit_iff]
      rcases IsMaximal_conjugates p P Q.1 with ⟨σ, hs⟩
      exact ⟨σ, by rw [← Subtype.val_inj, ← hs]; rfl⟩
  · congr
    exact Subsingleton.elim (fun _ ↦ _) (fun _ ↦ _)

theorem Extension_degree_over_DecompositionField_eq_ramificationIdx_mul_inertiaDeg
    [IsGalois K L] : finrank (DecompositionField p P) L =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  rw [DecompositionField, finrank_fixedField_eq_card (DecompositionGroup p P)]
  rw [DecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg p P]

/-- `P` is the unique ideal lying over `DecompositionIdeal p P`. -/
theorem isMaximal_lies_over_DecompositionIdeal_unique (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Q lies_over (DecompositionIdeal p P)] [IsGalois K L] : Q = P := by
  rcases IsMaximal_conjugates (DecompositionIdeal p P) P Q with ⟨σ, hs⟩
  let τ := (subgroup_equiv_aut (DecompositionGroup p P)).toFun σ
  have h : GalRingHom σ = GalRingHom τ.1 := rfl
  rw [← hs, h, (DecompositionGroup_mem p P τ.1).mp τ.2]

/-- The instance form of `isMaximal_lies_over_DecompositionIdeal_unique`. -/
instance unique_lies_over_DecompositionIdeal [IsGalois K L] :
    P unique_lies_over (DecompositionIdeal p P) :=
  { over_IdealBelow P with unique := fun Q ↦ isMaximal_lies_over_DecompositionIdeal_unique p P Q }

instance DecompositionIdeal.Nonsplit [IsGalois K L] :
    Nonsplit (algebraMap (𝓞 (DecompositionField p P)) (𝓞 L))
  (DecompositionIdeal p P) := unique_lies_over.Nonsplit (DecompositionIdeal p P) P

/-- An alternative statement of `isMaximal_lies_over_DecompositionIdeal_unique`. -/
theorem primes_over_DecompositionIdeal_card_eq_one [IsGalois K L] :
  Finset.card (primes_over (DecompositionIdeal p P) L) = 1 :=
    unique_primes_over_card_eq_one (DecompositionIdeal p P) P

theorem ramificationIdx_and_inertiaDeg_of_DecompositionIdeal [IsGalois K L] :
    ramificationIdx_of_isGalois (DecompositionIdeal p P) L = ramificationIdx_of_isGalois p L ∧
    inertiaDeg_of_isGalois (DecompositionIdeal p P) L = inertiaDeg_of_isGalois p L := by
  let Pz := IdealBelow (DecompositionField p P) P
  let E := { x // x ∈ DecompositionField p P }
  have h := ramificationIdx_mul_inertiaDeg_of_isGalois Pz L
  rw [primes_over_DecompositionIdeal_card_eq_one p P, one_mul,
    Extension_degree_over_DecompositionField_eq_ramificationIdx_mul_inertiaDeg p P] at h
  have h0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot p L) inferInstance (map_le_of_le_comap (le_of_eq hp.over))
  have hr := Nat.le_of_dvd h0 <| Dvd.intro_left _ <| Eq.symm <|
    ramificationIdx_algebra_tower (map_isMaximal_ne_bot p E) (map_isMaximal_ne_bot Pz L)
      (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pz) (ne_bot_ofIsMaximal P) rfl
  have h0 : inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P > 0 := inertiaDeg_pos p P
  have hi := Nat.le_of_dvd h0 <| Dvd.intro_left _  <| Eq.symm <| inertiaDeg_algebra_tower
    (Ideal_comap_IntermediateField p P (DecompositionField p P)) (IdealBelow_def E P)
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P,
    ramificationIdx_eq_ramificationIdx_of_isGalois p P] at hr
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois Pz P, inertiaDeg_eq_inertiaDeg_of_isGalois p P] at hi
  have hr0 := Nat.pos_of_ne_zero <| IsDedekindDomain.ramificationIdx_ne_zero
    (map_isMaximal_ne_bot Pz L) inferInstance (map_le_of_le_comap (le_of_eq rfl))
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h0
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P] at hr0
  exact (mul_eq_mul_iff_eq_and_eq_of_pos hr hi hr0 h0).mp h

theorem ramificationIdx_of_DecompositionIdeal [IsGalois K L]:
  ramificationIdx_of_isGalois (DecompositionIdeal p P) L = ramificationIdx_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_DecompositionIdeal p P).1

theorem inertiaDeg_of_DecompositionIdeal [IsGalois K L]:
  inertiaDeg_of_isGalois (DecompositionIdeal p P) L = inertiaDeg_of_isGalois p L :=
    (ramificationIdx_and_inertiaDeg_of_DecompositionIdeal p P).2

theorem ramificationIdx_of_DecompositionIdeal_over_bot_eq_one [IsGalois K L] : ramificationIdx
    (algebraMap (𝓞 K) (𝓞 (DecompositionField p P))) p (DecompositionIdeal p P) = 1 := by
  let Pz := IdealBelow (DecompositionField p P) P
  let E := { x // x ∈ DecompositionField p P }
  have h := ramificationIdx_algebra_tower (map_isMaximal_ne_bot p E) (map_isMaximal_ne_bot Pz L)
    (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pz) (ne_bot_ofIsMaximal P) rfl
  rw [ramificationIdx_eq_ramificationIdx_of_isGalois Pz P, ramificationIdx_of_DecompositionIdeal p P,
    ← ramificationIdx_eq_ramificationIdx_of_isGalois p P] at h
  nth_rw 1 [← one_mul (ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx_ne_zero (map_isMaximal_ne_bot p L)
    inferInstance (map_le_of_le_comap (le_of_eq hp.over))) h.symm

/-- The residue class field corresponding to `DecompositionField p P` is isomorphic to
residue class field corresponding to `p`. -/
theorem inertiaDeg_of_DecompositionIdeal_over_bot_eq_one [IsGalois K L] : inertiaDeg
    (algebraMap (𝓞 K) (𝓞 (DecompositionField p P))) p (DecompositionIdeal p P) = 1 := by
  have h := inertiaDeg_algebra_tower (Ideal_comap_IntermediateField p P (DecompositionField p P))
    (IdealBelow_def (DecompositionField p P) P)
  rw [inertiaDeg_eq_inertiaDeg_of_isGalois (IdealBelow (DecompositionField p P) P) P,
    inertiaDeg_of_DecompositionIdeal p P, ← inertiaDeg_eq_inertiaDeg_of_isGalois p P] at h
  nth_rw 1 [← one_mul (inertiaDeg (algebraMap (𝓞 K) (𝓞 L)) p P)] at h
  exact mul_right_cancel₀ (ne_of_gt (inertiaDeg_pos p P)) h.symm



-- Proposition 9.4

instance : Module.Finite (ℤ ⧸ comap (algebraMap ℤ (𝓞 K)) p) ((𝓞 K) ⧸ p) :=
  quotient_finite_quotient_comap p

/-- The residue class field of a number field is a finite field. -/
noncomputable instance residue_field_instFintype : Fintype ((𝓞 K) ⧸ p) :=
  fintypeOfFintype (ℤ ⧸ (comap (algebraMap ℤ (𝓞 K)) p)) ((𝓞 K) ⧸ p)

/-- The extension between residue class fields of number fields is a Galois extension. -/
instance extension_of_residue_fields_instIsGalois : IsGalois ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  inferInstance

/-- The inertia group of `P` over `K` is the subgorup of `L ≃ₐ[K] L` that consists of all
the `σ : L ≃ₐ[K] L` that are identity modulo `P`. -/
def InertiaGroup (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] : Subgroup (L ≃ₐ[K] L) where
  carrier := { σ | ∀ x : (𝓞 L), Ideal.Quotient.mk P (GalRingHom σ x) = Ideal.Quotient.mk P x }
  mul_mem' := by
    intro _ τ hs ht x
    rw [← ht x, ← hs (GalRingHom τ x)]
    rfl
  one_mem' _ := rfl
  inv_mem' := by
    intro σ hs x
    rw [← hs (GalRingHom σ⁻¹ x), GalRingHom_mul_inv_cancel_mem σ x]

theorem InertiaGroup_le_DecompositionGroup : InertiaGroup K P ≤ DecompositionGroup p P := by
  refine fun σ hs ↦ (DecompositionGroup_mem p P σ).mpr <|
    le_antisymm (map_le_of_le_comap (fun x hx ↦ ?_)) (fun x hx ↦ ?_)
  · have h := add_mem (Ideal.Quotient.eq.mp (hs x)) hx
    rw [sub_add_cancel] at h
    exact mem_comap.mpr h
  · rw [← GalRingHom_mul_inv_cancel_mem σ x]
    have h := add_mem (Ideal.Quotient.eq.mp (((InertiaGroup K P).inv_mem hs) x)) hx
    rw [sub_add_cancel] at h
    exact mem_map_of_mem (GalRingHom σ) h



section unique

open FiniteDimensional IntermediateField Polynomial

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P unique_lies_over p]

/-- If `P` is the unique ideal lying over `p`, then `P` remains invariant under the action of `σ`. -/
theorem GalRingHom_map_eq_of_unique_lies_over {K L : Type*} [Field K] [Field L]
    [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [P.IsMaximal]
    [hp : P unique_lies_over p] (σ : L ≃ₐ[K] L) : map (GalRingHom σ) P = P :=
  hp.unique (map (GalRingHom σ) P)

/-- If `P` is the unique ideal lying over `p`, then the action of each element `σ` in `L ≃ₐ[K] L`
on the residue class field is an an automorphism of `(𝓞 L) ⧸ P` fixing `(𝓞 K) ⧸ p`, inducing a
homomorphism from `L ≃ₐ[K] L` to the Galois group `((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)`. -/
def ResidueGaloisHom : MonoidHom (L ≃ₐ[K] L) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) where
  toFun σ := residueField_GalAlgEquiv p (GalRingHom_map_eq_of_unique_lies_over p P σ)
  map_one' := by ext ⟨⟩; rfl
  map_mul' _ _ := by ext ⟨⟩; rfl

noncomputable def powerBasis_of_residue : PowerBasis ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P) :=
  letI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := IsGalois.to_isSeparable
  Field.powerBasisOfFiniteOfSeparable ((𝓞 K) ⧸ p) ((𝓞 L) ⧸ P)

theorem ResidueGaloisHom_surjective [hn : Normal K L] :
    Function.Surjective (ResidueGaloisHom p P) := by
  let F := 𝓞 K ⧸ p
  let E := 𝓞 L ⧸ P
  letI : Algebra E E := Algebra.id E
  intro σ
  have e : PowerBasis F E := powerBasis_of_residue p P
  let β := (PowerBasis.liftEquiv e).toFun σ.toAlgHom
  rcases Quotient.exists_rep e.gen with ⟨a, ha⟩
  let f : (𝓞 K)[X] := minpoly (𝓞 K) a
  let fl : (𝓞 L)[X] := f.map (algebraMap (𝓞 K) (𝓞 L))
  let ϕp : (𝓞 K) →+* F := Ideal.Quotient.mk p
  let ϕP : (𝓞 L) →+* E := Ideal.Quotient.mk P
  have h : Quotient.mk (Submodule.quotientRel P) a = ϕP a := rfl
  rw [h] at ha
  have hai : IsIntegral (𝓞 K) a := IsIntegral.isIntegral a
  have hm : f.Monic := minpoly.monic hai
  have h0 : (fl.map ϕP) ≠ 0 := map_monic_ne_zero (Monic.map (algebraMap (𝓞 K) (𝓞 L)) hm)
  have hbr : β.1 ∈ (fl.map ϕP).roots := by
    have h : aeval e.gen (f.map ϕp) = ϕP (aeval a f) := by
      rw [← ha]
      exact (@map_aeval_eq_aeval_map _ _ _ F E _ _ _ _ _ ϕp ϕP rfl f a).symm
    rw [minpoly.aeval, map_zero] at h
    apply (mem_roots_iff_aeval_eq_zero h0).mpr
    have hc : fl.map ϕP = (f.map ϕp).map (algebraMap F E) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      rfl
    have hbz := aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd F e.gen h) β.2
    simp only [Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, PowerBasis.liftEquiv_apply_coe,
      AlgHom.coe_coe, hc, aeval_map_algebraMap, ← hbz]
  have hfe : (Polynomial.map (algebraMap (𝓞 K) K) f) = minpoly K a.1 := by
    refine minpoly.eq_of_irreducible_of_monic
      ((Monic.irreducible_iff_irreducible_map_fraction_map (minpoly.monic hai)).mp
        (minpoly.irreducible hai)) ?_ (Monic.map (algebraMap (𝓞 K) K) (minpoly.monic hai))
    have h : a.1 = algebraMap (𝓞 L) L a := rfl
    rw [h]
    simp only [aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, minpoly.aeval, f]
  have h : fl.roots.map ϕP = (fl.map ϕP).roots := by
    have h := (natDegree_eq_card_roots' (hn.splits a.1)).symm
    have hc : (algebraMap K L).comp (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) L := rfl
    have he := isIntegralClosure_root_card_eq_ofMonic (𝓞 L) L (minpoly.monic hai)
    rw [← hfe, natDegree_map, Monic.natDegree_map (minpoly.monic hai), Polynomial.map_map, hc, ← he,
      ← Monic.natDegree_map (minpoly.monic hai) (algebraMap (𝓞 K) (𝓞 L))] at h
    exact roots_map_of_card_eq_natDegree h0 h
  rw [← h] at hbr
  rcases Multiset.mem_map.mp hbr with ⟨b, ⟨hbr, hb⟩⟩
  have h : aeval b.1 (minpoly K (AdjoinSimple.gen K a.1)) = 0 := by
    have he : minpoly K (AdjoinSimple.gen K a.1) = minpoly K a.1 := by apply minpoly_eq
    have h : b.1 = algebraMap (𝓞 L) L b := rfl
    rw [he, ← hfe, h, aeval_map_algebraMap, aeval_algebraMap_eq_zero_iff, aeval_def, ← eval_map,
      ← coe_aeval_eq_eval, (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero hm)).mp hbr]
  let τ := ((IntermediateField.adjoin.powerBasis (hn.isIntegral a.1)).lift b.1 h).fieldRange_toAlgEquiv.liftNormal L
  use τ
  refine AlgEquiv.coe_algHom_injective ((@PowerBasis.liftEquiv E _ F _ _ E _ _ e).injective ?_)
  apply Subtype.val_inj.mp
  rw [PowerBasis.liftEquiv_apply_coe, AlgHom.coe_coe]
  simp only [← ha, Equiv.toFun_as_coe, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  calc _ = ϕP ((GalAlgEquiv τ) a) := rfl
    _ = β.1 := by
      rw [← hb]
      congr
      apply Subtype.val_inj.mp
      have ha : τ a.1 = τ (AdjoinSimple.gen K a.1).1 := rfl
      rw [← PowerBasis.lift_gen (IntermediateField.adjoin.powerBasis (hn.isIntegral a.1)) b.1 h]
      rw [GalAlgEquiv_apply, ha, AlgEquiv.liftNormal_intermediateField_commutes]
      rfl
    _ = _ := rfl



-- Definition 9.5

open IsGalois

/-- If `P` is the unique ideal lying over `p`, then the `InertiaGroup` is equal to the
kernel of the homomorphism `ResidueGaloisHom`. -/
theorem InertiaGroup_eq_ker {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [hp : P unique_lies_over p] : InertiaGroup K P = MonoidHom.ker (ResidueGaloisHom p P) := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  constructor
  · rintro h ⟨x⟩
    nth_rw 2 [Submodule.Quotient.quot_mk_eq_mk]
    rw [Quotient.mk_eq_mk, ← h x]
    rfl
  · intro h x
    have h := h (Ideal.Quotient.mk P x)
    rw [AlgEquiv.one_apply] at h
    rw [← h]
    rfl

/-- If `P` is the unique ideal lying over `p`, then the `InertiaGroup K P` is a normal subgroup. -/
theorem InertiaGroup_Normal {K L : Type*} [Field K] [Field L] [Algebra K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal]
    [hp : P unique_lies_over p]: Subgroup.Normal (InertiaGroup K P) := by
  rw [InertiaGroup_eq_ker p P]
  exact MonoidHom.normal_ker (ResidueGaloisHom p P)

noncomputable def aut_quoutient_InertiaGroup_equiv_residueField_aut [Normal K L] :
    @MulEquiv ((L ≃ₐ[K] L) ⧸ (InertiaGroup K P)) (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))
    (letI := InertiaGroup_Normal p P; inferInstance) _ :=
  letI := InertiaGroup_Normal p P
  (QuotientGroup.quotientMulEquivOfEq (InertiaGroup_eq_ker p P)).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _ (ResidueGaloisHom_surjective p P)

/-- The intermediate field fixed by `InertiaGroup K P`. -/
def InertiaField' (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] : IntermediateField K L :=
  fixedField (InertiaGroup K P)

/-- `InertiaField' K P` is a Number Field. -/
instance InertiaField_NumberField : NumberField (InertiaField' K P) :=
  of_IntermediateField (InertiaField' K P)

/-- The ideal equal to the intersection of `P` and `InertiaField' p P`. -/
abbrev InertiaIdeal' (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (P : Ideal (𝓞 L)) [P.IsMaximal] : Ideal (𝓞 (InertiaField' K P)) :=
  IdealBelow (InertiaField' K P) P

/-- `InertiaIdeal' p P` is a maximal Ideal. -/
instance InertiaIdeal_IsMaxiaml : IsMaximal (InertiaIdeal' K P) := IdealBelow.IsMaximal P



-- Proposition 9.6

variable [IsGalois K L]

/-- `(InertiaField' p P) / K` is a Galois extension. -/
theorem InertiaField_isGalois_of_unique {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal]
    [P.IsMaximal] [P unique_lies_over p] : IsGalois K (InertiaField' K P) :=
  letI := InertiaGroup_Normal p P
  of_fixedField_normal_subgroup (InertiaGroup K P)

/-- The Galois group `Gal((InertiaField' p P) / K)` is isomorphic to the
Galois group `Gal((𝓞 L) ⧸ P) / (𝓞 K) ⧸ p)`. -/
noncomputable def InertiaField_aut_equiv_ResidueField_aut :
    ((InertiaField' K P) ≃ₐ[K] (InertiaField' K P)) ≃* (((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P)) :=
  letI := InertiaGroup_Normal p P
  (normal_aut_equiv_quotient (InertiaGroup K P)).trans <|
    aut_quoutient_InertiaGroup_equiv_residueField_aut p P

/-- The Galois group `Gal(L / (InertiaField' p P))` is isomorphic to `InertiaGroup K P`. -/
def InertiaField_aut_tower_top_equiv_InertiaGroup_of_unique :
  (L ≃ₐ[InertiaField' K P] L) ≃* InertiaGroup K P := subgroup_equiv_aut (InertiaGroup K P)

/-- The extension degree `[L : K]` is equal to the product of the ramification index
and the inertia degree of `p` in `L`. -/
theorem finrank_eq_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 L))
    [P.IsMaximal] [P unique_lies_over p] : finrank K L =
    ramificationIdx_of_isGalois p L * inertiaDeg_of_isGalois p L := by
  have h := (ramificationIdx_mul_inertiaDeg_of_isGalois p L).symm
  rw [unique_primes_over_card_eq_one p P, one_mul] at h
  exact h

/-- The extension degree `[InertiaField' p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_InertiaField_eq_inertiaDeg_of_unique :
    finrank K (InertiaField' K P) = inertiaDeg_of_isGalois p L := by
  letI := InertiaField_isGalois_of_unique p P
  rw [← inertiaDeg_eq_inertiaDeg_of_isGalois p P, inertiaDeg, ← card_aut_eq_finrank]
  rw [Fintype.card_of_bijective (InertiaField_aut_equiv_ResidueField_aut p P).bijective]
  rw [card_aut_eq_finrank, dif_pos hp.over.symm]

/-- The extension degree `[L : InertiaField' p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_InertiaField_top_eq_ramificationIdx_of_unique :
    finrank (InertiaField' K P) L = ramificationIdx_of_isGalois p L := by
  have h : finrank K (InertiaField' K P) ≠ 0 := ne_of_gt finrank_pos
  apply mul_left_cancel₀ h
  rw [finrank_mul_finrank K (InertiaField' K P) L, finrank_eq_ramificationIdx_mul_inertiaDeg p P,
    finrank_bot_InertiaField_eq_inertiaDeg_of_unique p P, mul_comm]

theorem InertiaGroup_card_eq_ramificationIdx_of_unique :
    Fintype.card (InertiaGroup K P) = ramificationIdx_of_isGalois p L := by
  rw [← finrank_fixedField_eq_card, ← finrank_InertiaField_top_eq_ramificationIdx_of_unique p P]
  rfl

theorem InertiaGroup_InertiaIdeal_top (K : Type*) {L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (P : Ideal (𝓞 L)) [P.IsMaximal] :
    InertiaGroup (InertiaField' K P) P = ⊤ := by
  refine (Subgroup.eq_top_iff' (InertiaGroup (InertiaField' K P) P)).mpr (fun σ x ↦ ?_)
  let τ := (subgroup_equiv_aut (InertiaGroup K P)).toFun σ
  have hst : (GalRingHom σ) x = (GalRingHom τ.1) x := rfl
  rw [hst, τ.2 x]

theorem inertiaDeg_over_InertiaIdeal_eq_one_of_unique (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L))
    [P.IsMaximal] [P unique_lies_over p]  :
    inertiaDeg_of_isGalois (InertiaIdeal' K P) L = 1 := by
  letI := ideal_unique_lies_over_tower_top p (InertiaIdeal' K P) P
  letI := InertiaGroup_Normal (InertiaIdeal' K P) P
  rw [← inertiaDeg_eq_inertiaDeg_of_isGalois (InertiaIdeal' K P) P, inertiaDeg, dif_pos rfl]
  rw [← card_aut_eq_finrank, ← Fintype.card_of_bijective <| MulEquiv.bijective <|
    aut_quoutient_InertiaGroup_equiv_residueField_aut (InertiaIdeal' K P) P]
  have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup (InertiaGroup (InertiaField' K P) P)
  nth_rw 1 [(Subgroup.card_eq_iff_eq_top (InertiaGroup (InertiaField' K P) P)).mpr <|
    InertiaGroup_InertiaIdeal_top K P, ← one_mul (Nat.card (L ≃ₐ[InertiaField' K P] L))] at hm
  simp only [Nat.card_eq_fintype_card] at hm
  exact mul_right_cancel₀ Fintype.card_ne_zero hm.symm

theorem ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique :
    ramificationIdx_of_isGalois (InertiaIdeal' K P) L = ramificationIdx_of_isGalois p L := by
  letI := ideal_unique_lies_over_tower_top p (InertiaIdeal' K P) P
  rw [← finrank_InertiaField_top_eq_ramificationIdx_of_unique p P]
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg (InertiaIdeal' K P) P]
  rw [inertiaDeg_over_InertiaIdeal_eq_one_of_unique p P, mul_one]

theorem ramificationIdx_below_InertiaIdeal_eq_one_of_unique :
    ramificationIdx_of_isGalois p (InertiaField' K P) = 1 := by
  let Pt := IdealBelow (InertiaField' K P) P
  let E := { x // x ∈ InertiaField' K P }
  letI := InertiaField_isGalois_of_unique p P
  have h := ramificationIdx_algebra_tower (map_isMaximal_ne_bot p E) (map_isMaximal_ne_bot Pt L)
    (map_isMaximal_ne_bot p L) (ne_bot_ofIsMaximal Pt) (ne_bot_ofIsMaximal P) rfl
  nth_rw 1 [ramificationIdx_eq_ramificationIdx_of_isGalois Pt P,
    ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique p P,
    ← ramificationIdx_eq_ramificationIdx_of_isGalois p P,
    ← one_mul (ramificationIdx (algebraMap (𝓞 K) (𝓞 L)) p P),
    ramificationIdx_eq_ramificationIdx_of_isGalois p Pt] at h
  exact mul_right_cancel₀ (IsDedekindDomain.ramificationIdx_ne_zero (map_isMaximal_ne_bot p L)
    (IsMaximal.isPrime inferInstance) (map_le_of_le_comap (le_of_eq hp.over))) h.symm

theorem InertiaDeg_below_InertiaIdeal_eq_inertiaDeg_of_unique :
    inertiaDeg_of_isGalois p (InertiaField' K P) = inertiaDeg_of_isGalois p L := by
  letI := InertiaField_isGalois_of_unique p P
  have h := inertiaDeg_algebra_tower (Ideal_comap_IntermediateField p P (InertiaField' K P))
    (IdealBelow_def (InertiaField' K P) P)
  nth_rw 1 [inertiaDeg_eq_inertiaDeg_of_isGalois (InertiaIdeal' K P) P,
    inertiaDeg_over_InertiaIdeal_eq_one_of_unique p P, mul_one] at h
  simp_rw [inertiaDeg_eq_inertiaDeg_of_isGalois] at h
  exact h.symm

end unique



section inertia

/- TODO : The genral version of `InertiaField_aut_equiv_ResidueField_aut`, i.e.,
`((InertiaField p P) ≃ₐ[DecompositionField p P] (InertiaField p P))` is isomorphic to
`(((𝓞 L) ⧸ P) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 L) ⧸ P))`. -/

open IntermediateField FiniteDimensional Classical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
(p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)) [p.IsMaximal] [P.IsMaximal] [P lies_over p]

theorem InertiaGroup_eq :
    Subgroup.map (subgroup_equiv_aut (DecompositionGroup p P)).symm.toMonoidHom
    ((InertiaGroup K P).subgroupOf (DecompositionGroup p P)) =
    InertiaGroup (DecompositionField p P) P := by
  ext σ
  rw [Subgroup.mem_map]
  refine ⟨fun ⟨τ, ht, he⟩ x ↦ by rw [← he, ← Subgroup.mem_subgroupOf.mp ht x]; rfl, fun hs ↦ ?_⟩
  refine ⟨(subgroup_equiv_aut (DecompositionGroup p P)).toFun σ, fun x ↦ by rw [← hs x]; rfl, ?_⟩
  rw [MulEquiv.toEquiv_eq_coe]
  simp only [Equiv.toFun_as_coe, MulEquiv.coe_toEquiv, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

def InertiaGroup_equiv : InertiaGroup (DecompositionField p P) P ≃* InertiaGroup K P :=
  (MulEquiv.subgroupCongr (InertiaGroup_eq p P)).symm.trans <|
    ((subgroup_equiv_aut (DecompositionGroup p P)).symm.subgroupMap
      ((InertiaGroup K P).subgroupOf (DecompositionGroup p P))).symm.trans <|
        (Subgroup.subgroupOfEquivOfLe (InertiaGroup_le_DecompositionGroup p P))

/-- The intertia field of `P` over `K` is the intermediate field of `L / DecompositionField p P`
fixed by the inertia group pf `P` over `K`. -/
def InertiaField : IntermediateField (DecompositionField p P) L :=
  fixedField (InertiaGroup (DecompositionField p P) P)

/-- The ideal equal to the intersection of `P` and `InertiaField p P`. -/
abbrev InertiaIdeal : Ideal (𝓞 (InertiaField p P)) := IdealBelow (InertiaField p P) P

/-- `(InertiaField p P) / (DecompositionField p P)` is a Galois extension. -/
instance InertiaField_isGalois [IsGalois K L] : IsGalois (DecompositionField p P) (InertiaField p P) :=
  InertiaField_isGalois_of_unique (DecompositionIdeal p P) P

/-- The Galois group `Gal(L / (InertiaField p P))` is isomorphic to `InertiaGroup K P`. -/
def InertiaField_aut_tower_top_equiv_InertiaGroup :
    (L ≃ₐ[InertiaField p P] L) ≃* InertiaGroup K P :=
  (subgroup_equiv_aut (InertiaGroup (DecompositionField p P) P)).trans (InertiaGroup_equiv p P)

/-- The extension degree `[InertiaField p P : K]` is equal to the inertia degree of `p` in `L`. -/
theorem finrank_bot_InertiaField_eq_inertiaDeg [IsGalois K L] :
    finrank (DecompositionField p P) (InertiaField p P) = inertiaDeg_of_isGalois p L := by
  rw [← inertiaDeg_of_DecompositionIdeal p P]
  exact finrank_bot_InertiaField_eq_inertiaDeg_of_unique (DecompositionIdeal p P) P

/-- The extension degree `[L : InertiaField p P]` is equal to the
ramification index of `p` in `L`. -/
theorem finrank_InertiaField_top_eq_ramificationIdx [IsGalois K L] :
    finrank (InertiaField p P) L = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P]
  exact finrank_InertiaField_top_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P

theorem InertiaGroup_card_eq_ramificationIdx [IsGalois K L] :
    Fintype.card (InertiaGroup K P) = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P]
  rw [Fintype.card_of_bijective (InertiaGroup_equiv p P).symm.bijective]
  rw [InertiaGroup_card_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P]

theorem inertiaDeg_over_InertiaIdeal_eq_one [IsGalois K L] :
    inertiaDeg_of_isGalois (InertiaIdeal p P) L = 1 :=
  inertiaDeg_over_InertiaIdeal_eq_one_of_unique (DecompositionIdeal p P) P

theorem ramificationIdx_over_InertiaIdeal_eq_ramificationIdx [IsGalois K L] :
    ramificationIdx_of_isGalois (InertiaIdeal p P) L = ramificationIdx_of_isGalois p L := by
  rw [← ramificationIdx_of_DecompositionIdeal p P]
  exact ramificationIdx_over_InertiaIdeal_eq_ramificationIdx_of_unique (DecompositionIdeal p P) P

theorem ramificationIdx_below_InertiaIdeal_eq_one [IsGalois K L] :
    ramificationIdx_of_isGalois (DecompositionIdeal p P) (InertiaField p P) = 1 :=
  ramificationIdx_below_InertiaIdeal_eq_one_of_unique (DecompositionIdeal p P) P

theorem InertiaDeg_below_InertiaIdeal_eq_inertiaDeg [IsGalois K L] :
    inertiaDeg_of_isGalois (DecompositionIdeal p P) (InertiaField p P) =
    inertiaDeg_of_isGalois p L := by
  rw [← inertiaDeg_of_DecompositionIdeal p P]
  exact InertiaDeg_below_InertiaIdeal_eq_inertiaDeg_of_unique (DecompositionIdeal p P) P

end inertia
