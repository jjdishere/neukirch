import Mathlib.Topology.Algebra.ValuedField
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.NNReal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Topology.Algebra.ValuedField
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.Rat.NNRat
import Mathlib.Tactic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Order.Basic

open Classical
set_option maxHeartbeats 300000

#check Valuation.IsEquiv 

open Filter

variable {K : Type _} [Field K]


theorem RatSeqAboveTendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) < a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
  have : ∃ a : ℕ → ℝ, (∀ n, (b : ℝ) < a n) ∧ Tendsto a atTop (nhds b)
  · have h : ∃ a, StrictAnti a ∧ (∀ (n : ℕ), b < a n) ∧ Filter.Tendsto a Filter.atTop (nhds b) := exists_seq_strictAnti_tendsto b
    rcases h with ⟨a, ha₁, ha₂, ha₃⟩
    use a
  choose a hab ha using this
  choose r hr hr' using fun n ↦ exists_rat_btwn (hab n)
  refine ⟨r, hr, tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ b) ?_ ha ?_ ?_⟩
  · simp
  · exact fun n ↦ (hr n).le
  · exact fun n ↦ (hr' n).le

theorem RatSeqBelowTendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) > a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
  have : ∃ a : ℕ → ℝ, (∀ n, (b : ℝ) > a n) ∧ Tendsto a atTop (nhds b)
  · have h : ∃ a, StrictMono a ∧ (∀ (n : ℕ), a n < b) ∧ Filter.Tendsto a Filter.atTop (nhds b) := exists_seq_strictMono_tendsto b
    rcases h with ⟨a, ha₁, ha₂, ha₃⟩
    use a
  choose a hab ha using this
  choose r hr hr' using fun n ↦ exists_rat_btwn (hab n)
  refine ⟨r, hr', tendsto_of_tendsto_of_tendsto_of_le_of_le (h := fun _ ↦ b) ha ?_ ?_ ?_⟩
  · simp
  · exact fun n ↦ (hr n).le
  · exact fun n ↦ (hr' n).le

theorem isEquiv_iff_pow_eq (v₁: Valuation K NNReal) 
(v₂ : Valuation K NNReal) :
Valuation.IsEquiv v₁ v₂ ↔ ∃ (s : ℝ) (hs : s > 0), ∀ {x : K}, v₁ x = (v₂ x) ^ s where
  mp := sorry
  mpr := by 
    intro h
    rcases h with ⟨s, hs, h⟩
    apply (Valuation.isEquiv_iff_val_eq_one v₁ v₂).mpr
    intro x
    constructor
    · intro hv₁
      specialize @h x
      rw [hv₁] at h
      simp at h
      ext
      symm at h
      sorry
    · sorry


theorem ApproximationTheorem {v : Type _} {v' : Type _} {K : Type _} 
[Field K] {Γ : Type _} (v : Valuation K NNReal) (v' : Valuation K NNReal) 
{a₁ a₂ : Type _} (a₁ a₂ : K) : 
 ∀ (ε : ℝ), ∃ (x : K), (v (x - a₁) < ε) ∧ (v (x - a₂) < ε)   
 := sorry

structure NonarchimedeanValuation {K : Type _} [Field K] {Γ : Type _} 
[inst : LinearOrderedCommGroupWithZero Γ]  (v : Valuation K Γ) 
(hv : Valued K Γ) where
strong_tri_ineq : ∀ (x y : K), v (x + y) ≤ max (v x) (v y) 

#check NonarchimedeanValuation
#check Valuation

#check padicNorm

section

variable {p : ℕ} [hp : Fact p.Prime]

def pNorm (p : ℕ) (q : ℚ) : NNRat :=
  if q = 0 then 0 else (p : NNRat) ^ (-padicValRat p q)

theorem padicNorm'.mul (q r : ℚ): pNorm p (q * r) = (pNorm p q) *
(pNorm p r) :=
if hq : q = 0 then by 
  rw [hq, zero_mul] 
  simp [pNorm]
  else
    if hr : r = 0 then by simp [pNorm, hr]
    else by
      have : (p : NNRat) ≠ 0 := by simp [pNorm, hp.1.ne_zero]
      unfold pNorm
      simp [*, padicValRat.mul, zpow_add₀ this, mul_comm]


theorem padicMap_add_le_max (x y : ℚ) :
pNorm p (x + y) ≤ pNorm p x ∨ pNorm p (x + y) ≤ pNorm p y :=  
  if hx : x = 0 then by
  rw [hx, zero_add]
  right
  rfl
  else 
    if hy : y = 0 then by
    rw [hy, add_zero]
    left
    rfl
    else 
      if hxy : x + y = 0 then by
        simp [pNorm, *]
        else 
          if hxx : padicValRat p x ≤ padicValRat p y then by
            simp [pNorm, *]
            left
            rw [←inv_zpow, ←inv_zpow, inv_zpow', inv_zpow']
            have hxx' : padicValRat p x ≤ padicValRat p (x + y) := 
            padicValRat.le_padicValRat_add_of_le hxy hxx
            have hxx'' : - padicValRat p (x + y) ≤ - padicValRat p x := 
            neg_le_neg hxx'
            have hp' : (1 : NNRat) ≤ p := by
              have hp₂ : p ≠ 0 := by simp [hp.1.ne_zero]
              have hp₃ : 1 ≤ p := by exact Iff.mpr Nat.one_le_iff_ne_zero hp₂
              exact Iff.mpr Nat.one_le_cast hp₃
            exact zpow_le_of_le hp' hxx''
            else by
              simp [pNorm, *]
              right
              rw [←inv_zpow, ←inv_zpow, inv_zpow', inv_zpow']
              have hy₁ : padicValRat p x > padicValRat p y := Iff.mp Int.not_le hxx
              have hy₂ : padicValRat p y ≤ padicValRat p x := Int.le_of_lt hy₁
              have hxy' : y + x ≠ 0 := by 
                exact fun h1 => hxy (Eq.mp (add_comm y x ▸ Eq.refl (y + x = 0)) h1) 
              have hyy' : padicValRat p y ≤ padicValRat p (y + x) :=
              @padicValRat.le_padicValRat_add_of_le _ _ y x hxy' hy₂
              have hyy'' : - padicValRat p (y + x) ≤ - padicValRat p y :=
              neg_le_neg hyy' 
              have hyy''' : - padicValRat p (x + y) ≤ - padicValRat p y := by
                rw [add_comm]
                exact hyy''
              have hp' : (1 : NNRat) ≤ p := by
                have hp₂ : p ≠ 0 := by simp [hp.1.ne_zero]
                have hp₃ : 1 ≤ p := by exact Iff.mpr Nat.one_le_iff_ne_zero hp₂
                exact Iff.mpr Nat.one_le_cast hp₃
              exact zpow_le_of_le hp' hyy'''



        

def padicNorm' {p : ℕ}  [hp : Fact (Nat.Prime p)] 
  :
  Valuation ℚ NNRat where
    toFun := fun q ↦ pNorm p q
    map_zero' := by simp only [pNorm, padicValRat.zero, neg_zero, zpow_zero, ite_true]
    map_one' := by simp only [pNorm, padicValRat.one, neg_zero, zpow_zero, ite_false]
    map_mul' := padicNorm'.mul
    map_add_le_max' := by simp [padicMap_add_le_max]

theorem ValuEquiZtoQ 
 (v v' : Valuation ℚ NNRat) (h :∀ {x : ℤ}, v x = 1 ↔ v' x = 1 ): 
 ∀ {x : ℚ}, v x = 1 ↔ v' x = 1
 := sorry

theorem ValuationOfRat (v : Valuation ℚ NNRat)
(existvpltone : ∃ (q : ℕ) (hq : Nat.Prime q), v q < 1):
∃ (q : ℕ) (hq : Nat.Prime q), Valuation.IsEquiv v (@padicNorm' q (fact_iff.mpr hq))
:= by
  have vnleone : ∀ (n : ℕ), v n ≤ 1 := by
    intro n 
    induction' n with n hn
    have hzero : v Nat.zero = (0 : NNRat) := by simp only [Nat.zero_eq, CharP.cast_eq_zero, map_zero]
    simp only [Nat.zero_eq, CharP.cast_eq_zero, map_zero, zero_le]
    rw [Nat.succ_eq_add_one]
    have hone : v 1 ≤ 1 := by
      have hone' : v 1 = 1 := Valuation.map_one v
      exact Eq.ge (id (Eq.symm hone'))
    have hvnaddone : (v (n + 1) ≤ v n) ∨ (v (n + 1) ≤ v 1) := by exact Valuation.map_add' v (↑n) 1
    have trivial : v (↑n + 1) = v ↑(n + 1) := by 
      have ht : ((n : ℚ) + 1) = ((n + 1) : ℚ) := rfl
      rw [ht]
      apply Eq.symm (FunLike.congr_arg v _)
      exact Mathlib.Tactic.Ring.inv_add rfl rfl
    rcases hvnaddone with hn₁ | hn₂
    rw [trivial] at hn₁
    exact le_trans hn₁ hn
    rw [trivial] at hn₂
    exact le_trans hn₂ hone
  have vzleone : ∀ (x : ℤ), v x ≤ 1 := by
    intro x
    cases x with 
    | ofNat a => exact vnleone a 
    | negSucc a => 
      rw [← Valuation.map_neg]
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_neg]
      have trivial (n : ℕ): v (↑n + 1) = v ↑(n + 1) := by 
        have ht : ((n : ℚ) + 1) = ((n + 1) : ℚ) := rfl
        rw [ht]
        apply Eq.symm (FunLike.congr_arg v _)
        exact Mathlib.Tactic.Ring.inv_add rfl rfl
      rw [trivial]
      exact vnleone (a + 1)
  rcases existvpltone with ⟨q, hq, qltone⟩
  let Ideala : Ideal ℤ := {
    carrier := { x | v x < 1}
    add_mem' := by
      simp only [Set.mem_setOf_eq, Int.cast_add]
      intro x y hx hy
      exact lt_of_le_of_lt (v.map_add x y) (max_lt hx hy)
    zero_mem' := by simp only [Set.mem_setOf_eq, Int.cast_zero, map_zero, zero_lt_one]
    smul_mem' := by 
      simp only [Set.mem_setOf_eq, smul_eq_mul, Int.cast_mul, map_mul]
      intro a b hb
      have ha : v a ≤ 1 := vzleone a
      have hbb : 0 ≤ v b := zero_le (v b)
      exact mul_lt_one_of_nonneg_of_lt_one_right ha hbb hb
  }
  let qZ : Ideal ℤ := Ideal.span {(q:ℤ)}
  have IdealaIspz : Ideala = qZ := by
    have pIsmaxi : Ideal.IsMaximal qZ := 
      PrincipalIdealRing.isMaximal_of_irreducible
      (Iff.mpr PrincipalIdealRing.irreducible_iff_prime ((Iff.mp Nat.prime_iff_prime_int hq)))
    have qZlea : qZ ≤ Ideala := by 
      have qina : (q : ℤ) ∈ Ideala := qltone
      exact Iff.mpr (Ideal.span_singleton_le_iff_mem Ideala) qltone
    have anetop : Ideala ≠ ⊤ := by
      intro h
      have vone : v 1 = 1 := Valuation.map_one v
      have onenotin : 1 ∉ Ideala := by 
        intro h
        have h₁ : v 1 < 1 := h
        have h2 : ¬ v 1 ≥ 1 := by exact Iff.mpr not_le h₁
        apply h2
        exact Eq.ge vone
      apply onenotin
      exact Iff.mp (Ideal.eq_top_iff_one Ideala) h
    exact Eq.symm (Ideal.IsMaximal.eq_of_le pIsmaxi anetop qZlea)
  use q 
  use hq
  have valeqone : ∀ {x : ℤ}, v x = 1 ↔ (padicValRat q x = 0) := sorry
  have h₁ : ∀{x : ℤ}, v x = 1 ↔ (@padicNorm' q (fact_iff.mpr hq)) x = 1 := sorry
  have h₂ : ∀{x : ℚ}, v x = 1 ↔ (@padicNorm' q (fact_iff.mpr hq)) x = 1 := by
    exact ValuEquiZtoQ v (@padicNorm' q (fact_iff.mpr hq)) h₁
  exact Iff.mpr (Valuation.isEquiv_iff_val_eq_one v (@padicNorm' q (fact_iff.mpr hq))) h₂





section

variable {K : Type _} [Field K] {n : ℕ}
variable (v : Valuation K NNReal)

-- #check Ideal.span {(q:ℤ)}
-- #check (q : ℤ ⧸ Ideal.span {(q:ℤ)})

-- Definition of exponential valuation

noncomputable def expval (x : K): WithTop ℝ  := 
  if x = (0 : K) then ⊤ else (((- Real.log (v x) : ℝ) : WithTop ℝ) : WithTop ℝ)

-- def expv {p : ℕ}  [hp : Fact (Nat.Prime p)] 
-- : AddValuation K (WithTop ℝ) where
--   toFun := fun x ↦ expval v x
--   map_zero' := by simp  [expval, padicValRat.zero, neg_zero, zpow_zero, ite_true]
--   map_one' := by 
--     simp [expval]
--     rfl
--   map_mul'{x y} := 
--     if hxy : x = 0 ∨ y = 0 then by
--       simp [expval, *]
      
--       else sorry
--   map_add_le_max' := _


-- #check Set.range expvaluation


structure DiscreteValuation where 
valiso : ℕ 

#check AbsoluteValue K ℝ

-- Proposition 3.8
#check Valuation.integer


def GroupOfUnit : Subgroup Kˣ where
  carrier := { x | v x = 1}
  mul_mem' := by 
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul]
    intro a b ha hb
    rw [ha, hb, mul_one]
  one_mem' := by simp only [Set.mem_setOf_eq, Units.val_one, map_one]
  inv_mem' := by simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one, imp_self, forall_const]

def MaximalIdealValuRing : Ideal (Valuation.integer v) where
  carrier := { x | v x < 1}
  add_mem' {x y} hx hy := lt_of_le_of_lt (v.map_add x y) (max_lt hx hy)
  zero_mem' := by simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero, zero_lt_one]
  smul_mem':= by 
    simp
    intro a ha b hb hbb
    have haa : v a ≤ 1 := by exact ha
    have bneg : v b ≥ 0 := by exact zero_le (v b) 
    exact mul_lt_one_of_nonneg_of_lt_one_right haa bneg hbb


-- todo : define discrete valuation 

def IsDiscrete (v : Valuation K NNReal) : Prop 
:= ∃ (q : ℝ) (hq : q > 1), ∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n

def IsDiscrete' (v : Valuation K NNReal) : Prop
:= ∀ (x : Kˣ), ∃ (n : ℤ), v x = 2 ^ n

theorem IsDiscreteEquiv (v₁ : Valuation K NNReal) 
(v₂ : Valuation K NNReal) (hv₁ : IsDiscrete v₁) 
(hv₂ : IsDiscrete v₂) : Valuation.IsEquiv v₁ v₂   
:= sorry

-- noncomputable instance NNRat.toNNReal: Coe NNRat NNReal where
--   coe := fun (x:NNRat) ↦ {
--     val := x.val
--     property := Iff.mpr Rat.cast_nonneg x.property
--   }

def IsDiscreteRat (v : Valuation ℚ NNRat) : Prop 
:= ∃ (q : NNRat) (hq : q > 1), ∀ (x : ℚˣ), ∃ (n : ℤ), (v x :NNRat) = q ^ n

theorem pValIsDiscrete : IsDiscreteRat (@padicNorm' p hp) := by
  unfold IsDiscreteRat 
  simp only [Real.rpow_int_cast, gt_iff_lt, exists_prop]
  use p 
  have hp₃ : 1 < p :=  @Nat.Prime.one_lt p hp.out
  constructor
  exact Iff.mpr Nat.one_lt_cast hp₃
  intro x
  use (-padicValRat p x)
  have h : ↑↑(padicNorm' ↑x) = pNorm p x := rfl
  rw [h]
  simp only [pNorm, Units.ne_zero]
  simp only [zpow_neg, ite_false]



noncomputable def ValueOfPrime {v : Valuation K NNReal} (hv : IsDiscrete v) : ℝ := Classical.choose hv



def HighUnitGroup (n : ℕ) (hn : n ≥ 1)
  (hv : ∃ (q : ℝ) (hq : q > 1), ∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n)
  : Subgroup (@GroupOfUnit K _ v) where
    carrier := { x | v ((1 : K) - ((x : Kˣ): K)) < 1 / (2 ^ (n - 1))}
    mul_mem' := by
      simp only [ge_iff_le, one_div, ne_eq, tsub_pos_iff_lt, Set.mem_setOf_eq, Submonoid.coe_mul,
        Subgroup.coe_toSubmonoid, Units.val_mul, Subtype.forall]
      intro a ha₀ b hb₀ ha₁ hb₁
      have ha : v a = 1 := by exact ha₀
      have hab : (1 : K) - ↑a * ↑b = ((1 : K)- ↑a) + (↑a - ↑a * ↑b):= by simp only [sub_add_sub_cancel]
      rw [hab]
      have hab' : v (((1 : K)- a) + (a - a * b)) ≤ v ((1 : K)- a) ∨ v (((1 : K)- a) + (a - a * b)) ≤ v (a - a * b) :=
        Valuation.map_add' v (1 - ↑a) (↑a - ↑a * ↑b)
      rcases hab' with hab₁ | hab₂
      exact lt_of_le_of_lt hab₁ ha₁
      have h : ↑a - ↑a * ↑b = ↑a * ((1 : K) - ↑b) := Eq.symm (mul_one_sub (a : K) (b : K))
      have hab₃ : v (↑a - ↑a * ↑b) = (v ↑a) * (v ((1 : K) - ↑b)) := by 
        rw [h]
        exact Valuation.map_mul v (↑a) (1 - ↑b)
      have ha' : v a ≥ 0 := zero_le (v ↑a)
      rw [ha, one_mul] at hab₃
      rw [hab₃] at hab₂
      exact lt_of_le_of_lt hab₂ hb₁
    one_mem' := by simp only [ge_iff_le, one_div, ne_eq, tsub_pos_iff_lt, Set.mem_setOf_eq, OneMemClass.coe_one,
      Units.val_one, sub_self, map_zero, inv_pos, gt_iff_lt, zero_lt_two, pow_pos]
    inv_mem' := by 
      simp only [ge_iff_le, one_div, ne_eq, tsub_pos_iff_lt, Set.mem_setOf_eq, SubgroupClass.coe_inv,
        Units.val_inv_eq_inv_val, Subtype.forall]
      intro a ha₀ ha₁
      have h : (1 - (a : K)⁻¹) * a = a - (a : K)⁻¹ * a := by exact one_sub_mul ((a: K)⁻¹) (a:K)
      have h₁ : (1 - (a : K)⁻¹) * a = a - (1 : K) := by 
        simp [h, mul_left_inv a]
      have h₃ :  v (1 - (a : K)⁻¹) * v (a : K)= v (a - 1) := by
        rw [←h₁]
        exact (Valuation.map_mul v (1 - (a : K)⁻¹) (↑a)).symm
      have h₄ : v ((a : K) - 1) = v (1 - a) := Valuation.map_sub_swap v (a : K) (1 : K)
      have ha : v a = 1 := by exact ha₀
      have h₅ : v (1 - (a : K)⁻¹) = v (1 - (a : K)) := by
       rw [←h₄, ←h₃, ha]
       simp only [mul_one]
      exact Eq.trans_lt (id (h₅)) ha₁
      
      
def Idealp (n : ℕ)  (hn : n ≥ 1)
  (hv : ∃ (q : ℝ) (hq : q > 1), ∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n): Ideal (Valuation.integer v) where
    carrier := { x | v (x : K) < 1 / (2 ^ (n - 1))}
    add_mem' {x y} hx hy := lt_of_le_of_lt (v.map_add x y) (max_lt  hx hy)
    zero_mem' := by simp only [ge_iff_le, one_div, ne_eq, tsub_pos_iff_lt, Set.mem_setOf_eq, ZeroMemClass.coe_zero,
      map_zero, inv_pos, gt_iff_lt, zero_lt_two, pow_pos]
    smul_mem' := by 
      simp
      intro a ha b hb hbb
      exact mul_lt_of_le_one_of_lt ha hbb

-- theorem UnitGroupIsomorphism (n : ℕ) (hn : n ≥ 1) (hv : ∃ (q : ℝ) (hq : q > 1), ∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n): 
-- (@GroupOfUnit K _ v) ⧸ (HighUnitGroup v (n : ℕ)) ≃+*  
-- ((Valuation.integer v) ⧸ Idealp v (n : ℕ))ˣ := sorry