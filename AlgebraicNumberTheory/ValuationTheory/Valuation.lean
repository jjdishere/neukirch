/-
Copyright (c) 2023 Zou Wenrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zou Wenrong
-/
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Factorization.Basic

open Classical
set_option maxHeartbeats 300000

#check Valuation.IsEquiv

open Filter

variable {K : Type _} [Field K]

/- coercion from `ℚ≥0` to `ℝ≥0` -/
noncomputable instance NNRat.toNNReal: Coe NNRat NNReal where
  coe := fun (x:NNRat) ↦ {
    val := x.val
    property := Iff.mpr Rat.cast_nonneg x.property
  }

-- remove

theorem Valuation.isEquiv_iff_val_gt_one {K : Type _} [DivisionRing K] {Γ₀ : Type _} {Γ'₀ : Type _}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀]
    (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v x > 1 ↔ v' x > 1 := by
    constructor
    · intro h x
      constructor
      · intro h'
        by_contra h₀
        have h₁ : v' x ≤ 1 := not_lt.mp h₀
        have h₂ : v x ≤ 1 := ((Valuation.isEquiv_iff_val_le_one v v').mp h).mpr h₁
        apply (not_le.mpr h')
        exact h₂
      · intro h'
        by_contra h₀
        have h₁ : v x ≤ 1 := not_lt.mp h₀
        have h₂ : v' x ≤ 1 := ((Valuation.isEquiv_iff_val_le_one v v').mp h).mp h₁
        apply (not_le.mpr h')
        exact h₂
    · intro h
      apply (Valuation.isEquiv_iff_val_le_one v v').mpr
      intro x
      constructor
      · intro h'
        by_contra h₀
        specialize @h x
        have h₁ : 1 < v' x := not_le.mp h₀
        have h₂ : 1 < v x := h.mpr h₁
        apply (not_le.mpr h₂)
        exact h'
      · intro h'
        by_contra h₀
        specialize @h x
        have h₁ : 1 < v x := not_le.mp h₀
        have h₂ : 1 < v' x := h.mp h₁
        apply (not_le.mpr h₂)
        exact h'

-- `generalized to LinearOrderedCommGroupWithZero Γ₀`
theorem Valuation.map_zpow {K : Type u_3} [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀]
(v : Valuation K Γ₀) (x : K)  (m : ℤ) :
v (x ^ m) = (v x) ^ m := by
  cases m with
    | ofNat a =>
      simp only [Int.ofNat_eq_coe, zpow_coe_nat, _root_.map_pow]
    | negSucc m =>
      simp only [zpow_negSucc, map_inv₀, _root_.map_pow]

/- For any given real number, there exist a number sequence of rational number converge to that real number from above.-/
theorem Real.rat_seq_above_tendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) < a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
  have : ∃ a : ℕ → ℝ, (∀ n, (b : ℝ) < a n) ∧ Tendsto a atTop (nhds b)
  · have h : ∃ a, StrictAnti a ∧ (∀ (n : ℕ), b < a n) ∧ Filter.Tendsto a Filter.atTop (nhds b) := exists_seq_strictAnti_tendsto b
    rcases h with ⟨a, _, h₁, h₂⟩
    use a
  choose a hab ha using this
  choose r hr hr' using fun n ↦ exists_rat_btwn (hab n)
  refine ⟨r, hr, tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ b) ?_ ha ?_ ?_⟩
  · simp
  · exact fun n ↦ (hr n).le
  · exact fun n ↦ (hr' n).le

/- For any given real number, there exist a number sequence of rational number converge to that real number from below.-/
theorem Real.rat_seq_below_tendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) > a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
  have : ∃ a : ℕ → ℝ, (∀ n, (b : ℝ) > a n) ∧ Tendsto a atTop (nhds b)
  · have h : ∃ a, StrictMono a ∧ (∀ (n : ℕ), a n < b) ∧ Filter.Tendsto a Filter.atTop (nhds b) := exists_seq_strictMono_tendsto b
    rcases h with ⟨a, _, h₁, h₂⟩
    use a
  choose a hab ha using this
  choose r hr hr' using fun n ↦ exists_rat_btwn (hab n)
  refine ⟨r, hr', tendsto_of_tendsto_of_tendsto_of_le_of_le (h := fun _ ↦ b) ha ?_ ?_ ?_⟩
  · simp
  · exact fun n ↦ (hr n).le
  · exact fun n ↦ (hr' n).le

-- `Does this holds for Division ring?`
/- For any Valuation of a field K, Valuation of a quotient lt one implies element lt relation.-/
theorem Valuation.div_lt_one_iff {K : Type u_3} [Field K]
(v : Valuation K NNReal) {x y : K} (h₀ : y ≠ 0) :
 v (x / y) < 1 ↔ v x < v y := by
  have hxy₁ : v (x / y) * v y = v x := by
    simp only [map_div₀, ne_eq, map_eq_zero]
    have this : v y ≠ 0 := Iff.mpr (ne_zero_iff v) h₀
    exact div_mul_cancel (v x) this
  rw [←hxy₁]
  have this' : 0 < v y := by
    have this : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr h₀
    exact Iff.mpr zero_lt_iff this
  constructor
  · intro h
    exact mul_lt_of_lt_one_left this' h
  · intro h
    exact Iff.mp (mul_lt_iff_lt_one_left this') h

--le version
theorem Valuation.div_ge_one_iff {K : Type u_3} [Field K]
    (v : Valuation K NNReal) {x y : K} (h₀ : y ≠ 0) :
    (v (x / y) > 1) ↔ v x > v y := by
  have hxy₁ : v (x / y) * v y = v x := by
    simp only [map_div₀, ne_eq, map_eq_zero]
    have this : v y ≠ 0 := Iff.mpr (ne_zero_iff v) h₀
    exact div_mul_cancel (v x) this
  rw [←hxy₁]
  have this' : 0 < v y := by
    have this : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr h₀
    exact Iff.mpr zero_lt_iff this
  constructor
  · intro h
    exact lt_mul_left this' h
  · intro h
    exact Iff.mp (lt_mul_iff_one_lt_left this') h

-- version problem
open Real


-- version problem


--Filter.Tendsto.comp
theorem Tendsto_comp_Tendsto {X Y Z : Type _} {F : Filter X} {G : Filter Y}
    {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) : Tendsto (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg

--remove theorem
theorem gtonenezero {a : NNReal} (ha : 1 < a) : a ≠ 0 := by
  intro h
  have neq₁: (0 : NNReal)  ≤ 1 := by exact zero_le_one
  rw [←h] at neq₁
  have neq₂ : ¬ a ≤ 1 := lt_iff_not_le.mp ha
  exact neq₂ neq₁

--remove theorem `example`
theorem nPow {a b : ℝ} {m : ℤ} {n : ℕ} (hn : n > 0) (ha: 0 ≤ a)
(hb : 0 ≤ b) (h : a < b ^ (m / n : ℝ)) :
  a ^ n < b ^ m := by
  calc
    a ^ n < (b ^ (m / n : ℝ)) ^ n := pow_lt_pow_left h ha (by linarith)
    _ = (b ^ (m / n : ℝ)) ^ (n : ℝ) := by norm_num
    _ = b ^ m := by
      rw [← rpow_mul hb]
      field_simp

--remove theorem `example`
theorem nPow' {a b : ℝ} {m : ℤ} {n : ℕ} (hn : n > 0) (ha: 0 ≤ a)
(hb : 0 ≤ b) (h : a > b ^ (m / n : ℝ)) :
  a ^ n > b ^ m := by
  calc
    a ^ n > (b ^ (m / n : ℝ)) ^ n := pow_lt_pow_left h (by positivity) (by linarith)
    _ = (b ^ (m / n : ℝ)) ^ (n : ℝ) := by norm_num
    _ = b ^ m := by
      rw [← rpow_mul hb]
      field_simp


--ContinuousAt.rpow
theorem rPowAt {a : ℝ} (ha : 1 < a) {α : ℝ}:
ContinuousAt (fun (x : ℝ) ↦ a ^ x) α := by
  let f := fun (x : ℝ) ↦ a
  let g := fun (x : ℝ) ↦ x
  have hf : Continuous f := by continuity
  have hf' : ContinuousAt f α := Continuous.continuousAt hf
  have hg : Continuous g := by continuity
  have hg' : ContinuousAt g α := Continuous.continuousAt hg
  have  :  f α ≠ 0 ∨ 0 < g α  := by
    left
    simp only [ne_eq]
    intro h
    have neq₁: (0 : ℝ)  ≤ 1 := by exact zero_le_one
    rw [←h] at neq₁
    have neq₂ : ¬ a ≤ 1 := lt_iff_not_le.mp ha
    exact neq₂ neq₁
  exact ContinuousAt.rpow hf' hg' this

--remove theorem
theorem ExistPow {K : Type _} [Field K] (v₁ : Valuation K NNReal) {y : K} (hy : v₁ y > 1 )
    (x : K) (hx : x ≠ 0) : ∃ (α : ℝ), v₁ x = (v₁ y) ^ α  := by
  have this : v₁ x ≠ 0 := (Valuation.ne_zero_iff v₁).mpr hx
  let α := Real.log (v₁ x) / Real.log (v₁ y)
  use α
  have this₁ : 0 < v₁ x := Iff.mpr zero_lt_iff this
  have this₂ : 0 < (v₁ y)  := lt_trans one_pos hy
  have this₃ : α * Real.log (v₁ y) = Real.log (v₁ x) := by
    have neqzero : Real.log (v₁ y) ≠ 0 := by
      have hyneone₁ : ((v₁ y): ℝ) ≠ 1 :=  ne_of_gt hy
      have hyneone₂ : ((v₁ y): ℝ) ≠ 0 := ne_of_gt this₂
      have hyneone₃ : ((v₁ y): ℝ) ≠ -1 := by
        intro h
        have hyneg : (-1 : ℝ) < 0 := by exact neg_one_lt_zero
        rw [←h] at hyneg
        have hynneg : ¬ ((v₁ y): ℝ) ≤ 0 := not_le.mpr this₂
        apply hynneg
        exact le_of_lt hyneg
      exact Real.log_ne_zero.mpr ⟨hyneone₂, hyneone₁, hyneone₃⟩
    exact (div_mul_cancel (Real.log (v₁ x)) neqzero)
  ext
  exact Eq.symm ((mul_log_eq_log_iff this₂ this₁).mp this₃)

--remove theorem?
theorem InequalityTrans.one {K : Type _} [Field K] (v₁: Valuation K NNReal) {a : ℕ → ℚ}
{x y : K} (hy : v₁ y > 1 )
(hv₁ : ∀ (i : ℕ), v₁ x < ((v₁ y): ℝ) ^ (((a i).num : ℝ) / ((a i).den : ℝ)))
: ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) < 1 := by
  intro i
  specialize @hv₁ i
  have hv₁' : ((v₁ x): ℝ) ^ ((a i).den) < ((v₁ y): ℝ) ^ (((a i).num)) := by
    have hvxpos : 0 ≤ ((v₁ x): ℝ) := NNReal.coe_nonneg (v₁ x)
    have hvypos : 0 ≤ ((v₁ y): ℝ) := NNReal.coe_nonneg (v₁ y)
    have denpos : 0 < (a i).den := Rat.pos (a i)
    exact nPow denpos hvxpos hvypos hv₁
  let s:= @HPow.hPow NNReal ℕ NNReal _ (v₁ x) (a i).den
  let t:= @HPow.hPow NNReal ℤ NNReal _ (v₁ y) (a i).num
  let s' := @HPow.hPow ℝ ℕ ℝ  _ (v₁ x) (a i).den
  let t' := @HPow.hPow ℝ ℤ ℝ  _ (v₁ y) (a i).num
  have seq'' : ((v₁ x)) ^ ((a i).den)= s'  := by norm_num
  have teq'' : ((v₁ y): ℝ) ^ (((a i).num)) = t' := by norm_num
  have seq' : s = s' := rfl
  have teq' : t = t' := rfl
  rw [seq'', teq'', ←seq', ←teq'] at hv₁'
  have hyneqzero : (y ^ (a i).num) ≠ 0 := by
    have hvy : (v₁ y) ≠ 0 := gtonenezero hy
    have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
    exact zpow_ne_zero (a i).num this'
  apply (Valuation.div_lt_one_iff v₁ hyneqzero).mpr
  rw [(Valuation.map_pow v₁ x (a i).den), (Valuation.map_zpow v₁ y (a i).num)]
  exact hv₁'


--remove theorem?
theorem InequalityTrans.one' {K : Type _} [Field K] (v₁: Valuation K NNReal) {a : ℕ → ℚ}
{x y : K} (hy : v₁ y > 1 )
(hv₁ : ∀ (i : ℕ), v₁ x > ((v₁ y): ℝ) ^ (((a i).num : ℝ) / ((a i).den : ℝ)))
: ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) > 1 := by
  intro i
  specialize @hv₁ i
  have hv₁' : ((v₁ x): ℝ) ^ ((a i).den) > ((v₁ y): ℝ) ^ (((a i).num)) := by
    have hvxpos : 0 ≤ ((v₁ x): ℝ) := NNReal.coe_nonneg (v₁ x)
    have hvypos : 0 ≤ ((v₁ y): ℝ) := NNReal.coe_nonneg (v₁ y)
    have denpos : 0 < (a i).den := Rat.pos (a i)
    exact nPow' denpos hvxpos hvypos hv₁
  let s:= @HPow.hPow NNReal ℕ NNReal _ (v₁ x) (a i).den
  let t:= @HPow.hPow NNReal ℤ NNReal _ (v₁ y) (a i).num
  let s' := @HPow.hPow ℝ ℕ ℝ  _ (v₁ x) (a i).den
  let t' := @HPow.hPow ℝ ℤ ℝ  _ (v₁ y) (a i).num
  have seq'' : ((v₁ x)) ^ ((a i).den)= s' := by norm_num
  have teq'' : ((v₁ y): ℝ) ^ (((a i).num)) = t' := by norm_num
  have seq' : s = s' := rfl
  have teq' : t = t' := rfl
  rw [seq'', teq'', ←seq', ←teq'] at hv₁'
  have hyneqzero : (y ^ (a i).num) ≠ 0 := by
    have hvy : (v₁ y) ≠ 0 := gtonenezero hy
    have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
    exact zpow_ne_zero (a i).num this'
  apply (Valuation.div_ge_one_iff v₁ hyneqzero).mpr
  rw [(Valuation.map_pow v₁ x (a i).den), (Valuation.map_zpow v₁ y (a i).num)]
  exact hv₁'

--remove theorem?
theorem InequalityTrans'.one {K : Type _} [Field K] (v₂: Valuation K NNReal) {a : ℕ → ℚ}
{x y : K}
(hx : ∀ (i : ℕ), v₂ x ^ (a i).den < v₂ y ^ (a i).num)
: ∀ (i : ℕ), v₂ x < (v₂ y) ^ ((a i) : ℝ) := by
  intro i
  specialize hx i
  calc
    (v₂ x : ℝ) = ((v₂ x) ^ ((a i).den : ℝ)) ^ (((a i).den : ℝ)⁻¹) := by
      push_cast
      rw [← rpow_mul (by positivity)]
      field_simp [(a i).den_nz]
    _ < (v₂ y ^ (a i).num) ^ (((a i).den : ℝ)⁻¹) := by
      apply Real.rpow_lt_rpow
      · positivity
      · norm_cast
      · simp only [inv_pos, Nat.cast_pos, Rat.den_pos]
    _ = (v₂ y) ^ ((a i) : ℝ) := by
      nth_rw 3 [show a i = (a i).num * ((a i).den : ℚ)⁻¹ by field_simp [Rat.num_div_den (a i)]]
      simp [rpow_mul]

--remove theorem?
theorem InequalityTrans'.one' {K : Type _} [Field K] (v₂: Valuation K NNReal) {a : ℕ → ℚ}
{x y : K}
(hx : ∀ (i : ℕ), v₂ x ^ (a i).den > v₂ y ^ (a i).num)
: ∀ (i : ℕ), v₂ x > (v₂ y) ^ (((a i).num) / ((a i).den) : ℝ) := by
  intro i
  specialize hx i
  calc
    (v₂ x : ℝ) = ((v₂ x) ^ ((a i).den : ℝ)) ^ (((a i).den : ℝ)⁻¹) := by
      push_cast
      rw [← rpow_mul (by positivity)]
      field_simp [(a i).den_nz]
    _ > (v₂ y ^ ((a i).num :ℝ)) ^ (((a i).den : ℝ)⁻¹) := by
      apply Real.rpow_lt_rpow
      · positivity
      · norm_cast
      · simp only [inv_pos, Nat.cast_pos, Rat.den_pos]
    _ = (v₂ y) ^ (((a i).num : ℝ) / ((a i).den) : ℝ) := by
      rw [← rpow_mul]
      field_simp
      exact (v₂ y).2


--name Valuation.isEquiv_iff_exist_rpow_eq_aux₁
theorem Valuation.isEquiv_iff_exist_rpow_eq_aux₁ (v₁: Valuation K NNReal)
(v₂ : Valuation K NNReal) {x y : K} (hy :  v₁ y > 1)
(h : Valuation.IsEquiv v₁ v₂) {α : ℝ} (hx₁ : v₁ x = (v₁ y) ^ α)
: (v₂ x ≤ (v₂ y) ^ α) := by
  have hy₀ : y ≠ 0 := by
    intro h'
    simp [h'] at hy
  rcases Real.rat_seq_above_tendsto α with ⟨a, ha₀, ha₁⟩
  have claim₁ : ∀ i, v₁ x ^ ((a i).den) < (v₁ y) ^ ((a i).num) := by
    intro i
    calc
      (v₁ x : ℝ) ^ ((a i).den)  = ((v₁ y) ^ α) ^ ((a i).den) := by
        congr
        norm_cast
      _ < ((v₁ y) ^ (a i : ℝ)) ^ ((a i).den) := by
        apply pow_lt_pow_left _ _ (a i).den_nz
        exact (Real.rpow_lt_rpow_left_iff hy).mpr (ha₀ i)
        positivity
      _ = ((v₁ y): ℝ) ^ ((a i).num) := by
        rw [← rpow_nat_cast, ← rpow_int_cast, ← rpow_mul]
        congr
        norm_cast
        simp only [Rat.mul_den_eq_num]
        norm_num
  have claim₂ : ∀ (i : ℕ), v₂ x ≤ ((v₂ y): ℝ) ^ (a i: ℝ) := by
    intro i
    let s := x ^ (a i).den / y ^ (a i).num
    have : v₂ s < 1 := by
      rw [← (Valuation.isEquiv_iff_val_lt_one v₁ v₂).mp h]
      dsimp [s]
      rw [Valuation.div_lt_one_iff, Valuation.map_pow, Valuation.map_zpow]
      exact claim₁ i
      exact zpow_ne_zero (a i).num hy₀
    have : (v₂ x : ℝ) ^ (a i).den ≤ (v₂ y) ^ (a i).num := by
      apply (div_le_one _).mp
      simp only [map_div₀, _root_.map_pow, map_zpow₀] at this
      · norm_cast
        exact le_of_lt this
      · norm_cast
        apply zpow_pos_of_pos
        have : ¬ v₂ y ≤ 1 := ((Valuation.isEquiv_iff_val_le_one v₁ v₂).mp h).not.mp (not_le_of_gt hy)
        rw [← NNReal.coe_lt_coe, NNReal.coe_zero]
        rw [← NNReal.coe_le_coe, NNReal.coe_one] at this
        linarith
    calc
      (v₂ x : ℝ) = ((v₂ x) ^ ((a i).den : ℝ)) ^ ((a i).den : ℝ)⁻¹ := by
        rw [← rpow_mul]
        field_simp [(a i).den_nz]
        exact (v₂ x).2
      _ ≤ ((v₂ y) ^ ((a i).num : ℝ)) ^ ((a i).den : ℝ)⁻¹ := by
        apply rpow_le_rpow
        · positivity
        · norm_cast -- this step uses this
        · simp only [inv_nonneg, Nat.cast_nonneg]
      _ = ((v₂ y): ℝ) ^ (a i: ℝ) := by
        rw [← rpow_mul]
        field_simp [(a i).den_nz]
        · nth_rw 3 [← Rat.num_div_den (a i)]
          norm_num
        · exact (v₂ y).2

        -- simp [Rat.num_div_den (a i)]
    /-
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [←this']
    sorry
    -/
  let f' := (fun (x : ℝ) ↦ ((v₂ y) : ℝ) ^ x)
  have f'ContinuousAt : ContinuousAt f' α := by
    have hy' : 1 < ((v₂ y) : ℝ) := by
      have hy₂ : 1 < v₂ y := ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy
      exact hy₂
    exact rPowAt hy'
  let f := f' ∘ (fun i ↦ ((a i) : ℝ))
  have lim₁ : Tendsto f' (nhds α) (nhds (((v₂ y) : ℝ) ^ α)) := ContinuousAt.tendsto f'ContinuousAt
  have lim : Filter.Tendsto f atTop (nhds (((v₂ y) : ℝ) ^ α)) := Tendsto_comp_Tendsto ha₁ lim₁
  rw [← NNReal.coe_le_coe]
  push_cast
  exact @ge_of_tendsto _ _ _ _ _ _ _ _ _ sorry lim sorry --claim₂

example (a : ℝ) (n : ℤ) : a ^ n = a ^ (n : ℝ) := by exact (rpow_int_cast a n).symm
  /-
  have hxa : ∀ (i : ℕ), v₁ x < ((v₁ y): ℝ) ^ (a i : ℝ) := by
    intro i
    rw [hx₁]
    specialize ha₀ i
    exact Real.rpow_lt_rpow_of_exponent_lt hy ha₀
  have hv₁ : ∀ (i : ℕ), v₁ x < ((v₁ y): ℝ) ^ (((a i).num : ℝ) / ((a i).den : ℝ)) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : ((a i).num : ℝ) / ((a i).den: ℝ) = ((a i): ℝ)  := by
      exact (Rat.cast_def (a i)).symm
    rw [this']
    exact (hxa i)
  have hxa₂ : ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) < 1 := InequalityTrans.one v₁ hy hv₁
  have hv₂ : ∀ (i : ℕ), v₂ x < ((v₂ y): ℝ) ^ (((a i).num: ℝ) / ((a i).den : ℝ)) := by
    have hxa₃ : ∀ (i : ℕ), v₂ ((x ^ (a i).den) / (y ^ (a i).num)) < 1 :=
      fun i => ((Valuation.isEquiv_iff_val_lt_one v₁ v₂).mp h).mp (hxa₂ i)
    have hxa₄ : ∀ (i : ℕ), v₂ (x ^ (a i).den) < v₂ (y ^ (a i).num) := by
      intro i
      have this : (y ^ (a i).num) ≠ 0 := by
        have hvy : (v₁ y) ≠ 0 := gtonenezero hy
        have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
        exact zpow_ne_zero (a i).num this'
      exact (Valuation.div_lt_one_iff v₂ this).mp (hxa₃ i)
    have hxa₅ : ∀ (i : ℕ), (v₂ x) ^ ((a i).den) < (v₂ y) ^ ((a i).num) := by
      intro i
      specialize @hxa₄ i
      rw [←(Valuation.map_pow v₂ x (a i).den), ←(Valuation.map_zpow v₂ y (a i).num)]
      exact hxa₄
    sorry
    -- exact InequalityTrans'.one v₂ hxa₅
    -/

  /-
  have hv₂' : ∀ (i : ℕ), v₂ x < ((v₂ y): ℝ) ^ (a i: ℝ) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [←this']
    exact (hv₂ i)
  have hv₂'' : ∀ (i : ℕ), (v₂ x) ≤  ((v₂ y) : ℝ) ^ (a i: ℝ) := fun i ↦ le_of_lt (hv₂' i)
  let f' := fun (x : ℝ) ↦ ((v₂ y) : ℝ) ^ x
  have f'ContinuousAt : ContinuousAt f' α := by
    have hy' : 1 < ((v₂ y) : ℝ) := by
      have hy₂ : 1 < v₂ y := ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy
      exact hy₂
    exact rPowAt hy'
  let f := f' ∘ (fun i ↦ ((a i) : ℝ))
  have lim₁ : Tendsto f' (nhds α) (nhds (((v₂ y) : ℝ) ^ α)) := ContinuousAt.tendsto f'ContinuousAt
  have lim : Filter.Tendsto f atTop (nhds (((v₂ y) : ℝ) ^ α)) := Tendsto_comp_Tendsto ha₁ lim₁
  exact ge_of_tendsto lim hv₂''
-/

theorem Valuation.isEquiv_iff_exist_rpow_eq_aux₂ (v₁: Valuation K NNReal)
(v₂ : Valuation K NNReal) {x y : K} (hy :  v₁ y > 1)
(h : Valuation.IsEquiv v₁ v₂) {α : ℝ} (hx₁ : v₁ x = (v₁ y) ^ α)
: (v₂ x ≥ (v₂ y) ^ α) := by
  have sequbelow : ∃ a : ℕ → ℚ, (∀ i, (α : ℝ) > a i) ∧ Tendsto (fun k ↦ (a k : ℝ)) atTop (nhds α) := Real.rat_seq_below_tendsto α
  rcases sequbelow with ⟨a, ha₀, ha₁⟩
  sorry
  -- have hxa : ∀ (i : ℕ), v₁ x > ((v₁ y): ℝ) ^ (a i: ℝ) := by
  --   intro i
  --   rw [hx₁]
  --   exact Real.rpow_lt_rpow_of_exponent_lt hy (ha₀ i)
  -- have hv₁ : ∀ (i : ℕ), v₁ x > ((v₁ y): ℝ) ^ (((a i).num : ℝ) / ((a i).den : ℝ)) := by
  --   intro i
  --   have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
  --   have this' : ((a i).num : ℝ) / ((a i).den: ℝ) = ((a i): ℝ)  := by
  --     exact (Rat.cast_def (a i)).symm
  --   rw [this']
  --   exact (hxa i)
  -- have hxa₂ : ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) > 1 := InequalityTrans.one' v₁ hy hv₁
  -- have hv₂ : ∀ (i : ℕ), v₂ x > ((v₂ y): ℝ) ^ (((a i).num: ℝ) / ((a i).den : ℝ)) := by
  --   have hxa₃ : ∀ (i : ℕ), v₂ ((x ^ (a i).den) / (y ^ (a i).num)) > 1 :=
  --     fun i => ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp (hxa₂ i)
  --   have hxa₄ : ∀ (i : ℕ), v₂ (x ^ (a i).den) > v₂ (y ^ (a i).num) := by
  --     intro i
  --     have this : (y ^ (a i).num) ≠ 0 := by
  --       have hvy : (v₁ y) ≠ 0 := gtonenezero hy
  --       have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
  --       exact zpow_ne_zero (a i).num this'
  --     exact (Valuation.div_ge_one_iff v₂ this).mp (hxa₃ i)
  --   have hxa₅ : ∀ (i : ℕ), (v₂ x) ^ ((a i).den) > (v₂ y) ^ ((a i).num) := by
  --     intro i
  --     specialize @hxa₄ i
  --     rw [←(Valuation.map_pow v₂ x (a i).den), ←(Valuation.map_zpow v₂ y (a i).num)]
  --     exact hxa₄
  --   exact InequalityTrans'.one' v₂ hxa₅
  -- have hv₂' : ∀ (i : ℕ), v₂ x > ((v₂ y): ℝ) ^ (a i: ℝ) := by
  --   intro i
  --   have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
  --   have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by
  --     rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
  --     exact congrArg Rat.cast this
  --   rw [←this']
  --   exact (hv₂ i)
  -- have hv₂'' : ∀ (i : ℕ), (v₂ x) ≥ ((v₂ y) : ℝ) ^ (a i : ℝ ) := fun i ↦ le_of_lt (hv₂' i)
  -- let f' := fun (x : ℝ) ↦ ((v₂ y) : ℝ) ^ x
  -- have f'ContinuousAt : ContinuousAt f' α := by
  --   have hy' : 1 < ((v₂ y) : ℝ) := by
  --     have hy₂ : 1 < v₂ y := ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy
  --     exact hy₂
  --   exact rPowAt hy'
  -- let f := f' ∘ (fun i ↦ ((a i) : ℝ))
  -- have lim₁ : Tendsto f' (nhds α) (nhds (((v₂ y) : ℝ) ^ α)) := ContinuousAt.tendsto f'ContinuousAt
  -- have lim : Filter.Tendsto f atTop (nhds (((v₂ y) : ℝ) ^ α)) := Tendsto_comp_Tendsto ha₁ lim₁
  -- exact le_of_tendsto' lim hv₂''

--exist change to and
theorem Valuation.isEquiv_iff_exist_rpow_eq (v₁: Valuation K NNReal)
(v₂ : Valuation K NNReal) (h₀ : ∃ (y : K), v₁ y > 1):
Valuation.IsEquiv v₁ v₂ ↔ ∃ (s : ℝ), (0 < s) ∧ (∀ ⦃x : K ⦄, (v₁ x = (v₂ x) ^ s)) where
  mp := by
    intro h
    rcases h₀ with ⟨y, hy⟩
    have hxy : ∀ (x : K), (x ≠ 0) → ∃ (α : ℝ),
    ((v₁ x = (v₁ y) ^ α) ∧ v₂ x = (v₂ y) ^ α) := by
      have hx : ∀ (x : K), (x ≠ 0) → ∃ (α : ℝ), v₁ x = (v₁ y) ^ α := ExistPow v₁ hy
      intro x xneqzero
      specialize @hx x xneqzero
      rcases hx with ⟨α, hx₁⟩
      use α
      constructor
      · exact hx₁
      · apply le_antisymm_iff.mpr ⟨_, _⟩
        · exact Valuation.isEquiv_iff_exist_rpow_eq_aux₁ v₁ v₂ hy h hx₁
        · exact Valuation.isEquiv_iff_exist_rpow_eq_aux₂ v₁ v₂ hy h hx₁
    let s := (Real.log (v₁ y)) / (Real.log (v₂ y))
    use s
    have hs: 0 < s := by
      apply div_pos
      exact log_pos hy
      exact log_pos (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)
    constructor
    · exact hs
    · intro x
      by_cases hx : x = 0
      · rw [((Valuation.zero_iff v₁).mpr hx), ((Valuation.zero_iff v₂).mpr hx)]
        exact (NNReal.zero_rpow (ne_of_gt hs)).symm
      · by_cases hxx : (v₂ x) = 1
        · rw [hxx, (((Valuation.isEquiv_iff_val_eq_one v₁ v₂).mp h).mpr hxx)]
          exact (NNReal.one_rpow s).symm
        · calc
          v₁ x = v₂ x ^ (log (v₁ x) / log (v₂ x )) := by
            ext
            push_cast
            symm
            apply (mul_log_eq_log_iff _ _).mp
            · symm
              apply (div_eq_iff _).mp rfl
              apply Real.log_ne_zero_of_pos_of_ne_one _ _
              norm_num
              apply zero_lt_iff.mpr
              exact (Valuation.ne_zero_iff v₂).mpr hx
              norm_num
              exact hxx
            · norm_num
              apply zero_lt_iff.mpr
              exact (Valuation.ne_zero_iff v₂).mpr hx
            · norm_num
              apply zero_lt_iff.mpr
              exact (Valuation.ne_zero_iff v₁).mpr hx
          _ = v₂ x ^ (log (v₁ y) / log (v₂ y)) := by
            congr 1
            specialize @hxy x hx
            rcases hxy with ⟨α, hxy₁, hxy₂⟩
            rw [hxy₁, hxy₂]
            calc
              (log (v₁ y ^ α)) / (log (v₂ y ^ α)) = (α * log (v₁ y)) / (α * log (v₂ y)) := by
                congr
                · symm
                  apply (mul_log_eq_log_iff _ _).mpr rfl
                  · exact pos_of_gt hy
                  · exact rpow_pos_of_pos (pos_of_gt hy) α
                · symm
                  apply (mul_log_eq_log_iff _ _).mpr rfl
                  · exact pos_of_gt (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)
                  · exact rpow_pos_of_pos (pos_of_gt (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)) α
              _  =  log (v₁ y)/  log (v₂ y) := by
                apply mul_div_mul_left (log (v₁ y)) (log (v₂ y)) _
                intro h'
                rw [h'] at hxy₂
                simp at hxy₂
                exact hxx hxy₂
  mpr := by
    intro h
    rcases h with ⟨s, h⟩
    apply (Valuation.isEquiv_iff_val_lt_one v₁ v₂).mpr
    intro x
    let h₁ := h.1
    let h₂ := h.2
    specialize @h₂ x
    constructor
    · by_cases hx : x = 0
      · intro _
        rw [(Valuation.zero_iff v₂).mpr hx]
        exact one_pos
      · intro hv₁
        rw [h₂] at hv₁
        simpa [h₁, lt_asymm h₁] using ((Real.rpow_lt_one_iff_of_pos (zero_lt_iff.mpr ((Valuation.ne_zero_iff v₂).mpr hx)))).mp hv₁
    · by_cases hx : x = 0
      · intro _
        rw [(Valuation.zero_iff v₁).mpr hx]
        exact one_pos
      · intro hv₂
        apply NNReal.coe_lt_coe.mp
        rw [h₂]
        apply Iff.mpr (Real.rpow_lt_one_iff_of_pos _) (Or.inr { left := hv₂, right := h₁ })
        simp only [NNReal.val_eq_coe, NNReal.coe_pos, (zero_lt_iff.mpr ((Valuation.ne_zero_iff v₂).mpr hx))]



theorem Valuation.approximation_theorem {v : Type _} {v' : Type _} {K : Type _}
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

noncomputable def pNorm (p : ℕ) (q : ℚ) : NNReal :=
  if q = 0 then 0 else (p : NNReal) ^ (-padicValRat p q)

theorem padicNorm'.mul (q r : ℚ): pNorm p (q * r) = (pNorm p q) *
(pNorm p r) :=
if hq : q = 0 then by
  rw [hq, zero_mul]
  simp [pNorm]
  else
    if hr : r = 0 then by simp [pNorm, hr]
    else by
      have : (p : NNReal) ≠ 0 := by simp [pNorm, hp.1.ne_zero]
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
            apply zpow_le_of_le _ (neg_le_neg (padicValRat.le_padicValRat_add_of_le hxy hxx))
            apply Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr _)
            simp [hp.1.ne_zero]
            else by
              simp [pNorm, *]
              right
              rw [←inv_zpow, ←inv_zpow, inv_zpow', inv_zpow']
              apply zpow_le_of_le _ _
              · apply Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr _)
                simp [hp.1.ne_zero]
              · simp only [neg_le_neg_iff]
                rw [add_comm]
                apply (@padicValRat.le_padicValRat_add_of_le p hp y x _ _)
                · exact fun h1 => hxy (Eq.mp (add_comm y x ▸ Eq.refl (y + x = 0)) h1)
                · exact Int.le_of_lt ((Int.not_le).mp hxx)


open Real


noncomputable def padicNorm' {p : ℕ}  [hp : Fact (Nat.Prime p)]
  :
  Valuation ℚ NNReal where
    toFun := fun q ↦ pNorm p q
    map_zero' := by simp only [pNorm, padicValRat.zero, neg_zero, zpow_zero, ite_true]
    map_one' := by
      unfold pNorm
      simp only [one_ne_zero, padicValRat.one, neg_zero, zpow_zero, ite_false]
    map_mul' := padicNorm'.mul
    map_add_le_max' := by simp [padicMap_add_le_max]


--to do: valuation_equiv_on ring to fraction field
theorem ValuEquiZtoQ
 (v v' : Valuation ℚ NNRat) (h :∀ {x : ℤ}, v x = 1 ↔ v' x = 1 ):
 ∀ {x : ℚ}, v x = 1 ↔ v' x = 1
 := sorry

theorem ValuationEqual (v : Valuation ℚ NNReal) {q : ℕ} (hq: Nat.Prime q)
(h : ∀ (n : ℕ), (¬ n = 0) → v n = (v q) ^ (padicValRat q n))
: ∀ (n : ℕ), (¬ n = 0) → v n = ((@padicNorm' q (fact_iff.mpr hq)) n) ^ (- log (v q) / log q)
:= by
  intro n hn
  specialize @h n hn
  rw [h]
  have this' : (@padicNorm' q (fact_iff.mpr hq)).toFun n = (q : NNReal) ^ (- padicValRat q n) := by
    unfold padicNorm'
    simp [pNorm, *]
  have this'' : (@padicNorm' q (fact_iff.mpr hq)) n = (@padicNorm' q (fact_iff.mpr hq)).toFun n := by rfl
  rw [this'', this']; symm
  have hq₀ : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  ext; push_cast
  rw [← Real.rpow_int_cast ↑q (-padicValRat q ↑n), ←Real.rpow_int_cast ↑(v ↑q) (padicValRat q ↑n),
     ←Real.rpow_mul hq₀ ↑(-padicValRat q ↑n) (-log ↑(v ↑q) / log ↑q)]
  -- rw [←Real.rpow_mul hq₀ (-padicValRat q ↑n) (-log ↑(v ↑q) / log ↑q)]
  apply (mul_log_eq_log_iff _ _).mp
  -- goal: ↑(-padicValRat q ↑n) * (-log ↑(v ↑q) / log ↑q) * log ↑q = log (↑(v ↑q) ^ ↑(padicValRat q ↑n))
  · calc
      ↑(-padicValRat q ↑n) * (-log ↑(v ↑q) / log ↑q) * log ↑q = ↑(padicValRat q ↑n) * log ↑(v ↑q) := by

        rw [neg_div (log q) (log (v q))]
        sorry
        -- rw [neg_mul_neg (padicValRat q n : ℝ) (log (v q) / log q)]
      _ = log (↑(v ↑q) ^ ((padicValRat q ↑n) : ℝ)) := by
        apply (mul_log_eq_log_iff _ _).mpr rfl
        · norm_cast
          apply zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (Nat.cast_ne_zero.mpr _))
          simp [((fact_iff.mpr hq)).1.ne_zero]
        · apply Real.rpow_pos_of_pos _ ((padicValRat q ↑n) : ℝ)
          norm_cast
          apply zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (Nat.cast_ne_zero.mpr _))
          simp [((fact_iff.mpr hq)).1.ne_zero]
  · exact Nat.cast_pos.mpr (Nat.Prime.pos hq)
  · apply Real.rpow_pos_of_pos _ ((padicValRat q ↑n) : ℝ)
    norm_cast
    apply zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (Nat.cast_ne_zero.mpr _))
    simp [((fact_iff.mpr hq)).1.ne_zero]



  -- have eq₁ : ((q : NNReal) ^ ((- padicValRat q n) : ℝ)) = @HPow.hPow NNReal ℤ NNReal _ q (- (@Nat.cast ℤ instNatCastInt (padicValNat q n) )) := by
  --   simp only [NNReal.coe_nat_cast, padicValRat.of_nat, Int.cast_ofNat, zpow_neg, zpow_coe_nat, NNReal.coe_inv, NNReal.coe_pow]
  --   rw [←zpow_coe_nat (q : ℝ) (padicValNat q n), ←zpow_neg (q : ℝ) (padicValNat q n)]
  --   simp [Real.rpow_int_cast]
  --   rw [←(Real.rpow_nat_cast q (padicValNat q n))]
  --   exact Real.rpow_neg hq₀ ((padicValNat q n) : ℝ)
  -- simp only [padicValRat.of_nat, zpow_coe_nat, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_nat_cast]
  -- rw [←eq₁]
  -- simp only [NNReal.coe_nat_cast]
  -- rw [←(@rpow_mul q hq₀ (- padicValRat q n) (- log (v q) / log q)), neg_div (log q) (log (v q)), neg_mul_neg (padicValRat q n : ℝ) (log (v q) / log q)]
  -- simp only [padicValRat.of_nat, Int.cast_ofNat]
  -- let t₁ := ((padicValNat q n) : ℝ) * ((log (v q)) / (log q))
  -- have teq₁ : ((padicValNat q n) : ℝ) * ((log (v q)) / (log q)) = t₁ := rfl
  -- rw [teq₁]
  -- let s₁ := @HPow.hPow ℝ ℕ ℝ _ (v q) (padicValNat q n)
  -- have seq₁ : @HPow.hPow ℝ ℕ ℝ _ (v q) (padicValNat q n) = s₁ := rfl
  -- rw [seq₁]
  -- have hq₁ : 0 < (q : ℝ) := by
  --   have qpos : 0 < q := Nat.Prime.pos hq
  --   exact Iff.mpr Nat.cast_pos qpos
  -- have vqnezero : v q ≠ 0 := by
  --     have qnezero : q ≠ 0 := by simp [((fact_iff.mpr hq)).1.ne_zero]
  --     have qnezero' : (q : ℚ) ≠ 0 := Iff.mpr Nat.cast_ne_zero qnezero
  --     exact (Valuation.ne_zero_iff v).mpr qnezero'
  -- have vqpos : 0 < v q := Iff.mpr zero_lt_iff vqnezero
  -- have hq₂ : (0 : ℝ) < s₁ := by
  --   let s₂ := @HPow.hPow NNReal ℕ NNReal _ (v q) (padicValNat q n)
  --   have seq₂ : s₂ =  @HPow.hPow NNReal ℕ NNReal _ (v q) (padicValNat q n) := rfl
  --   have seq₃ : s₁ = s₂ := seq₁
  --   rw [seq₃, seq₂]
  --   exact pow_pos vqpos (padicValNat q n)
  -- apply (mul_log_eq_log_iff hq₁ hq₂).mp
  -- rw [←teq₁, ←seq₁]
  -- have eq₂ : log (@HPow.hPow ℝ ℕ ℝ _ (v q) (padicValNat q n)) = (padicValNat q n) * log (v q) := by
  --   apply Eq.symm
  --   apply (mul_log_eq_log_iff vqpos hq₂).mpr
  --   simp only [NNReal.val_eq_coe, rpow_nat_cast]
  -- rw [eq₂]
  -- have eq₃ : (log (v q) / log q) * log q = log (v q) := by
  --   have nezero : log q ≠ 0 := by
  --     refine Real.log_ne_zero.mpr ⟨?_, ?_, ?_⟩
  --     · simp [((fact_iff.mpr hq)).1.ne_zero]
  --     · simp [((fact_iff.mpr hq)).1.ne_one]
  --     · intro h
  --       have hyneg : (-1 : ℝ) < 0 := by exact neg_one_lt_zero
  --       rw [←h] at hyneg
  --       have hynneg : ¬ (q : ℝ) ≤ 0 := not_le.mpr hq₁
  --       apply hynneg
  --       exact le_of_lt hyneg
  --   exact div_mul_cancel (log (v q)) nezero
  -- rw [mul_assoc, eq₃]


theorem ValuationEqual' (v : Valuation ℚ NNReal) {s : ℝ} {q : ℕ} (hq : Nat.Prime q)
(vformula : ∀ (n : ℕ), (¬ n = 0) → v n = ((@padicNorm' q (fact_iff.mpr hq)) n) ^ s)
: ∀ (x : ℤ), (¬ x = 0) → v x = ((@padicNorm' q (fact_iff.mpr hq)) x) ^ s
:= by
  intro x hx
  cases x with
  | ofNat x =>
    have : x ≠ 0 := by exact Iff.mp Int.ofNat_ne_zero hx
    exact vformula x this
  | negSucc x =>
    rw [← Valuation.map_neg, ←(Valuation.map_neg (@padicNorm' q (fact_iff.mpr hq)) )]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_neg]
    have trivial (n : ℕ): v (↑n + 1) = v ↑(n + 1) := by
      have ht : ((n : ℚ) + 1) = ((n + 1) : ℚ) := rfl
      rw [ht]
      apply Eq.symm (FunLike.congr_arg v _)
      exact Mathlib.Tactic.Ring.inv_add rfl rfl
    have trivial' (n : ℕ): (@padicNorm' q (fact_iff.mpr hq)) (↑n + 1) = (@padicNorm' q (fact_iff.mpr hq)) ↑(n + 1) := by
      have ht : ((n : ℚ) + 1) = ((n + 1) : ℚ) := rfl
      rw [ht]
      apply Eq.symm (FunLike.congr_arg (@padicNorm' q (fact_iff.mpr hq)) _)
      exact Mathlib.Tactic.Ring.inv_add rfl rfl
    rw [trivial, trivial']
    have : x + 1 ≠ 0 := Nat.succ_ne_zero x
    exact vformula (x + 1) this


theorem factorization_eq_padicValNat {n : ℕ} (q : ℕ) (hq : Nat.Prime q)
: (Nat.factorization n) q = padicValNat q n
:= by
  unfold Nat.factorization
  simp
  intro h
  exfalso
  exact h hq



--change
theorem ValuationEquation (v : Valuation ℚ NNReal) (q : ℕ) (hq : Nat.Prime q)
 (h₁ : ∀ {m : ℕ}, ¬q ∣ m  → v m = 1)
: ∀ (n : ℕ), (¬ n = 0) → v n = (v q) ^ (padicValRat q n)
:= by
  intro n hn
  let n₁ := ord_proj[q] n
  let n₂ := ord_compl[q] n
  have : n = n₁ * n₂ := Eq.symm (Nat.ord_proj_mul_ord_compl_eq_self n q)
  have this' : n = (n₁ : ℚ) * (n₂ : ℚ) := by
    rw [this]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.isUnit_iff]
  nth_rw 2 [this']
  sorry
  -- rw [(Valuation.map_mul v n₁ n₂)]
  -- have vn₂ : v n₂ = 1 := by
  --   have nediv : ¬ q ∣ n₂ := Nat.not_dvd_ord_compl hq hn
  --   exact h₁ nediv
  -- rw [vn₂]
  -- have vn₁ : v n₁ = (v q) ^ (padicValNat q n) := by
  --   have neq : n₁ = q ^ (padicValNat q n) := by
  --     have eq₀ : (Nat.factorization n) q = padicValNat q n := factorization_eq_padicValNat q hq
  --     exact congrArg (Nat.pow q) eq₀
  --   rw [neq]
  --   have eq₁ : ((q ^ (padicValNat q n)): ℚ) = (q : ℚ) ^ (padicValNat q n) := Nat.cast_pow q (padicValNat q n)
  --   rw [eq₁]
  --   exact Valuation.map_pow v (q : ℚ) (padicValNat q n)
  -- rw [vn₁, mul_one]
  -- simp only [padicValRat.of_nat, zpow_coe_nat]

--change condition
theorem Valuation.isEquiv_padicNorm_of_nonarchValuation (v : Valuation ℚ NNReal)
    (existvpltone : ∃ (q : ℕ) (hq : Nat.Prime q), v q < 1):
    ∃ (q : ℕ) (hq : Nat.Prime q), Valuation.IsEquiv v (@padicNorm' q (fact_iff.mpr hq)):= by
  have vnleone : ∀ (n : ℕ), v n ≤ 1 := by
    intro n
    induction' n with n hn
    simp only [Nat.zero_eq, CharP.cast_eq_zero, map_zero, zero_le]
    rw [Nat.succ_eq_add_one]
    have trivial : v (↑n + 1) = v ↑(n + 1) := by congr; norm_cast
    rcases (Valuation.map_add' v (↑n) 1) with hn₁ | hn₂
    rw [trivial] at hn₁
    exact le_trans hn₁ hn
    rw [trivial] at hn₂
    exact le_trans hn₂ (id (Valuation.map_one v).symm).ge
  have vzleone : ∀ (x : ℤ), v x ≤ 1 := by
    intro x
    cases x with
    | ofNat a => exact vnleone a
    | negSucc a =>
      rw [← Valuation.map_neg]
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_neg]
      have trivial (n : ℕ): v (↑n + 1) = v ↑(n + 1) := by congr; norm_cast
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
      exact mul_lt_one_of_nonneg_of_lt_one_right (vzleone a) (zero_le (v b)) hb
  }
  let qZ : Ideal ℤ := Ideal.span {(q:ℤ)}
  have IdealaIspz : Ideala = qZ := by
    symm
    apply Ideal.IsMaximal.eq_of_le
    · exact PrincipalIdealRing.isMaximal_of_irreducible
        (Iff.mpr PrincipalIdealRing.irreducible_iff_prime ((Iff.mp Nat.prime_iff_prime_int hq)))
    · intro h
      have onenotin : 1 ∉ Ideala := by
        intro h
        apply (not_le.mpr (show v 1 < 1 by exact h))
        exact (Valuation.map_one v).ge
      apply onenotin
      exact (Ideal.eq_top_iff_one Ideala).mp h
    · exact (Ideal.span_singleton_le_iff_mem Ideala).mpr qltone
  use q
  use hq
  have h₂ : ∃ (y : ℚ), 1 < v y := by
    let y := (1 : ℚ) / q
    use y
    calc
      1 = (v y) * (v q) := by
        rw [←(Valuation.map_one v), ←(Valuation.map_mul v y (q : ℚ))]
        congr
        apply (div_mul_cancel 1 _).symm
        simp [((fact_iff.mpr hq)).1.ne_zero]
      _ < v y := by
        apply mul_lt_of_lt_one_right (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (one_div_ne_zero (Nat.cast_ne_zero.mpr _)))) qltone
        simp [((fact_iff.mpr hq)).1.ne_zero]
  apply (Valuation.isEquiv_iff_exist_rpow_eq v (@padicNorm' q (fact_iff.mpr hq)) h₂).mpr
  let s := - log (v q) / log q
  have hs : 0 < s := by
    apply div_pos
    · apply neg_pos.mpr (Real.log_neg _ qltone)
      simp only [NNReal.val_eq_coe, NNReal.coe_pos, gt_iff_lt]
      apply zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr (Nat.cast_ne_zero.mpr _))
      simp only [ne_eq, ((fact_iff.mpr hq)).1.ne_zero, not_false_eq_true]
    · exact Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hq))
  use s
  use hs
  intro x
  have heq : ∀ {m : ℕ}, ¬q ∣ m  → v m = 1 := by
    intro m h
    -- apply le_antisymm (vzleone m) (not_lt.mp _)
    -- only need to translate the goal to m not in Ideala
    have : (m : ℤ) ∉ qZ := by
      by_contra h'
      apply h
      have existdiv : ∃ (m' : ℤ), m' * q = m := Ideal.mem_span_singleton'.mp h'
      rcases existdiv with ⟨m', hm⟩
      have dvdm : (q : ℤ) ∣ (m : ℤ) := Dvd.intro_left m' hm
      exact Iff.mp Int.ofNat_dvd dvdm
    have this' : (m : ℤ) ∉ Ideala := by
      rw [IdealaIspz]
      exact this
    have vmgeone : 1 ≤ v m := Iff.mp not_lt this'
    exact le_antisymm (vzleone m) vmgeone
  have claim₃ : ∀ (x : ℤ), (¬ x = 0) → v x = ((@padicNorm' q (fact_iff.mpr hq)) x) ^ s := ValuationEqual' v hq (ValuationEqual v hq (ValuationEquation v q hq heq))
  by_cases hx : x = 0
  · rw [hx, (Valuation.map_zero v), (Valuation.map_zero (@padicNorm' q (fact_iff.mpr hq)))]
    symm; ext; push_cast
    exact (Real.zero_rpow (ne_of_gt hs))
  · calc
      v x = v (x.num / x.den) := by rw [(Rat.num_div_den x)]
      _ = v (x.num) / v (x.den) := by
        exact map_div₀ v (x.num : ℚ) (x.den : ℚ)
      _ = ((@padicNorm' q (fact_iff.mpr hq)) x.num) ^ s / ((@padicNorm' q (fact_iff.mpr hq)) x.den) ^ s := by
        congr
        · exact claim₃ x.num (Rat.num_ne_zero_of_ne_zero hx)
        · exact claim₃ x.den (Int.ofNat_ne_zero.mpr (Rat.den_nz x))
      _ = ((@padicNorm' q (fact_iff.mpr hq)) x) ^ s := by
        symm; nth_rw 1 [←(Rat.num_div_den x)]
        simp only [map_div₀]
        ext; push_cast
        exact (Real.div_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s)


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

--Mathlib.RingTheory.Valuation.Integers
def MaximalIdealValuRing : Ideal (Valuation.integer v) where
  carrier := { x | v x < 1}
  add_mem' {x y} hx hy := lt_of_le_of_lt (v.map_add x y) (max_lt hx hy)
  zero_mem' := by simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero, zero_lt_one]
  smul_mem':= by
    simp
    intro a ha b _ hbb
    have haa : v a ≤ 1 := by exact ha
    have bneg : v b ≥ 0 := by exact zero_le (v b)
    exact mul_lt_one_of_nonneg_of_lt_one_right haa bneg hbb


-- todo : define discrete valuation

def IsDiscrete (v : Valuation K NNReal) : Prop
:= ∃ (q : ℝ), (1 < q) ∧ (∃ (x : K), v x = q) ∧ (∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n)



theorem pValIsDiscrete : IsDiscrete (@padicNorm' p hp) := by
  unfold IsDiscrete
  use p
  have hp₃ : 1 < p :=  @Nat.Prime.one_lt p hp.out
  have this' : p ≠ 0 := by sorry
  constructor
  exact Iff.mpr Nat.one_lt_cast hp₃
  constructor
  · let p' := (p : ℚ)
    use p'
    simp
    have : (@padicNorm' p hp).toFun p = (p : NNReal)⁻¹ := by
      unfold padicNorm'
      simp [pNorm, *]
    sorry
   -- use p
  · intro x
    use (-padicValRat p x)
    have h : ↑↑(padicNorm' ↑x) = pNorm p x := rfl
    rw [h]
    simp only [pNorm, Units.ne_zero, zpow_neg, ite_false, NNReal.coe_inv, NNReal.coe_zpow, NNReal.coe_nat_cast]



noncomputable def ValueOfPrime {v : Valuation K NNReal} (hv : IsDiscrete v) : ℝ := Classical.choose hv



def HighUnitGroup (n : ℕ) (hn : n ≥ 1)
  (hv : IsDiscrete v)
  : Subgroup (@GroupOfUnit K _ v) where
    carrier := { x | v ((1 : K) - ((x : Kˣ): K)) < 1 / ((ValueOfPrime hv) ^ (n - 1))}
    mul_mem' := by
      simp only [ge_iff_le, one_div, ne_eq, tsub_pos_iff_lt, Set.mem_setOf_eq, Submonoid.coe_mul,
        Subgroup.coe_toSubmonoid, Units.val_mul, Subtype.forall]
      intro a ha₀ b _ ha₁ hb₁
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
    one_mem' := by
      simp only [one_div, Set.mem_setOf_eq, OneMemClass.coe_one, Units.val_one, sub_self, map_zero, NNReal.coe_zero,
        inv_pos]
      have : 1 < (ValueOfPrime hv) := (Classical.choose_spec hv).1
      norm_cast
      refine' Real.rpow_pos_of_pos _ ((n : ℝ) - 1)
      linarith
    inv_mem' := by
      simp only [one_div, Set.mem_setOf_eq, SubgroupClass.coe_inv, Units.val_inv_eq_inv_val, Subtype.forall]
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
      have h₆ :(v (1 - (a : K)⁻¹) : ℝ) = (v (1 - (a : K)) : ℝ) := congrArg NNReal.toReal h₅
      exact Eq.trans_lt (id (h₆)) ha₁


def Idealp (n : ℕ)  (hn : n ≥ 1)
  (hv : IsDiscrete v): Ideal (Valuation.integer v) where
    carrier := { x | v (x : K) < 1 / ((ValueOfPrime hv) ^ (n - 1))}
    add_mem' {x y} hx hy := by
      have h : (v (x + y): ℝ) ≤ max ((v x): ℝ) ((v y): ℝ) := v.map_add x y
      have h₁ : max ((v x) : ℝ) ((v y): ℝ) < 1 / ((ValueOfPrime hv) ^ (n - 1)) := by
        refine max_lt ?_ ?_
        · exact hx
        · exact hy
      exact lt_of_le_of_lt h h₁
    zero_mem' := by
      simp only [one_div, Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero, NNReal.coe_zero, inv_pos]
      have : 1 < (ValueOfPrime hv) := (Classical.choose_spec hv).1
      refine' Real.rpow_pos_of_pos _ ((n : ℝ) - 1)
      linarith
    smul_mem' := by
      simp only [one_div, Set.mem_setOf_eq, smul_eq_mul, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid,
        Subring.coe_toSubsemiring, map_mul, NNReal.coe_mul, Subtype.forall]
      intro a ha b hb hbb
      exact mul_lt_of_le_one_of_lt_of_nonneg ha hbb (NNReal.coe_nonneg (v b))


-- theorem UnitGroupIsomorphism (n : ℕ) (hn : n ≥ 1) (hv : ∃ (q : ℝ) (hq : q > 1), ∀ (x : Kˣ), ∃ (n : ℤ), v x = q ^ n):
-- (@GroupOfUnit K _ v) ⧸ (HighUnitGroup v (n : ℕ)) ≃+*
-- ((Valuation.integer v) ⧸ Idealp v (n : ℕ))ˣ := sorry
