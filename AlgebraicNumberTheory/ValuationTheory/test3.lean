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

open Classical
set_option maxHeartbeats 300000

#check Valuation.IsEquiv 

open Filter

variable {K : Type _} [Field K]


noncomputable instance NNRat.toNNReal: Coe NNRat NNReal where
  coe := fun (x:NNRat) ↦ {
    val := x.val
    property := Iff.mpr Rat.cast_nonneg x.property
  }

theorem Valuation.isEquiv_iff_val_gt_one [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ'₀] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) :
    v.IsEquiv v' ↔ ∀ {x : K}, v x > 1 ↔ v' x > 1 := sorry


theorem RatSeqAboveTendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) < a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
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

theorem RatSeqBelowTendsto (b : ℝ) : ∃ a : ℕ → ℚ, (∀ n, (b : ℝ) > a n) ∧ Tendsto (fun n ↦ (a n : ℝ)) atTop (nhds b) := by
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


theorem Valuation.div_le_one {K : Type u_3} [inst : Field K] 
(v : Valuation K NNReal) {x y : K} (h₀ : y ≠ 0) 
(h : v (x / y) < 1): v x < v y := by
  have hxy₁ : v (x / y) * v y = v x := by
    simp only [map_div₀, ne_eq, map_eq_zero]
    have this : v y ≠ 0 := Iff.mpr (ne_zero_iff v) h₀
    exact div_mul_cancel (v x) this
  rw [←hxy₁]
  have this' : 0 < v y := by
    have this : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr h₀
    exact Iff.mpr zero_lt_iff this
  exact mul_lt_of_lt_one_left this' h

theorem Valuation.div_le_one_iff {K : Type u_3} [inst : Field K] 
(v : Valuation K NNReal) {x y : K} (h₀ : y ≠ 0) :
 (v (x / y) < 1) ↔ v x < v y := by
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

theorem Valuation.div_ge_one_iff {K : Type u_3} [inst : Field K] 
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

theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩
-- version problem


theorem exp_eq {a b : ℝ} (h1 : 0 < a) (h2 : 0 < b) (h3 : b ≠ 1):
   a = b ^ ((Real.log a) / (Real.log b)) 
  := by
    have this : Real.log a = ((Real.log a) / (Real.log b)) * (Real.log b) := by 
      have this' : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h2 h3 
      exact Iff.mp (div_eq_iff this') rfl
    exact Eq.symm ((mul_log_eq_log_iff h2 h1).mp (Eq.symm this))


theorem Tendsto_comp_Tendsto {X Y Z : Type _} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) : Tendsto (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg


theorem gtonenezero {a : NNReal} (ha : 1 < a) : a ≠ 0 := by
  intro h
  have neq₁: (0 : NNReal)  ≤ 1 := by exact zero_le_one 
  rw [←h] at neq₁
  have neq₂ : ¬ a ≤ 1 := lt_iff_not_le.mp ha 
  exact neq₂ neq₁


theorem nPow {a b : ℝ} {m : ℤ} {n : ℕ} (hn : n > 0) (ha: 0 ≤ a) 
(hb : 0 ≤ b) (h : a < b ^ (m / n)) : 
  a ^ n < b ^ m := by 
  let s := @HPow.hPow ℝ ℕ ℝ _ a n 
  let t := @HPow.hPow ℝ ℕ ℝ _ (b ^ (m / n)) n   
  have this : s < t := pow_lt_pow_of_lt_left h ha hn
  have hs : s = a ^ n := Eq.symm (rpow_nat_cast a n)
  have ht : t = (b ^ (m / n)) ^ n := Eq.symm (rpow_nat_cast (b ^ (m / n)) n)
  rw [hs, ht, ←(Real.rpow_mul hb (m / n) (n))] at this
  have hn₁ : (n : ℝ) ≠ 0 := by 
    have hn₂ : n ≠ 0 := Iff.mp Nat.pos_iff_ne_zero hn 
    exact Iff.mpr Nat.cast_ne_zero hn₂
  rw [(div_mul_cancel (m : ℝ) hn₁)] at this
  exact this


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


theorem ExistSeqAbove (v₁: Valuation K NNReal) 
(v₂ : Valuation K NNReal) {x y : K} (hy :  v₁ y > 1)
(h : Valuation.IsEquiv v₁ v₂) {α : ℝ} (hx₁ : v₁ x = (v₁ y) ^ α)
: (v₂ x ≤ (v₂ y) ^ α) := by
  have sequabove : ∃ a : ℕ → ℚ, (∀ i, (α : ℝ) < a i) ∧ Tendsto (fun k ↦ (a k : ℝ)) atTop (nhds α) := RatSeqAboveTendsto α 
  rcases sequabove with ⟨a, ha₀, ha₁⟩
  have hxa : ∀ (i : ℕ), v₁ x < ((v₁ y): ℝ) ^ (a i) := by
    intro i 
    rw [hx₁]
    specialize @ha₀ i
    exact Real.rpow_lt_rpow_of_exponent_lt hy ha₀
  have hv₁ : ∀ (i : ℕ), v₁ x < ((v₁ y): ℝ) ^ (((a i).num : ℚ) / ((a i).den :ℚ)) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by 
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [this']
    exact (hxa i)
  have hxa₂ : ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) < 1 := sorry
  have hv₂ : ∀ (i : ℕ), v₂ x < ((v₂ y): ℝ) ^ (((a i).num: ℚ) / ((a i).den : ℚ)) := by
    have hxa₃ : ∀ (i : ℕ), v₂ ((x ^ (a i).den) / (y ^ (a i).num)) < 1 := 
      fun i => ((Valuation.isEquiv_iff_val_lt_one v₁ v₂).mp h).mp (hxa₂ i)
    have hxa₄ : ∀ (i : ℕ), v₂ (x ^ (a i).den) < v₂ (y ^ (a i).num) := by
      intro i
      have this : (y ^ (a i).num) ≠ 0 := by
        have hvy : (v₁ y) ≠ 0 := gtonenezero hy
        have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
        exact zpow_ne_zero (a i).num this'
      exact (Valuation.div_le_one_iff v₂ this).mp (hxa₃ i)
    have hxa₅ : ∀ (i : ℕ), (v₂ x) ^ ((a i).den) < (v₂ y) ^ ((a i).den) := sorry
    intro i
    specialize @hxa₅ i
    sorry -- 1/n pow on both side
  have hv₂' : ∀ (i : ℕ), v₂ x < ((v₂ y): ℝ) ^ (a i) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by 
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [←this']
    exact (hv₂ i)
  -- exp_continuous
  have hv₂'' : ∀ (i : ℕ), (v₂ x) ≤  ((v₂ y) : ℝ) ^ (a i) := fun i ↦ le_of_lt (hv₂' i)
  let f' := fun (x : ℝ) ↦ ((v₂ y) : ℝ) ^ x
  have f'ContinuousAt : ContinuousAt f' α := by
    have hy' : 1 < ((v₂ y) : ℝ) := by
      have hy₂ : 1 < v₂ y := ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy
      exact hy₂
    exact rPowAt hy'
  let f := f' ∘ (fun i ↦ ((a i) : ℝ))
  have lim₁ : Tendsto f' (nhds α) (nhds (((v₂ y) : ℝ) ^ α)) := ContinuousAt.tendsto f'ContinuousAt
  have lim : Filter.Tendsto f atTop (nhds (((v₂ y) : ℝ) ^ α)) := Tendsto_comp_Tendsto ha₁ lim₁
  exact ge_of_tendsto' lim hv₂''


theorem ExistSeqBelow (v₁: Valuation K NNReal) 
(v₂ : Valuation K NNReal) {x y : K} (hy :  v₁ y > 1)
(h : Valuation.IsEquiv v₁ v₂) {α : ℝ} (hx₁ : v₁ x = (v₁ y) ^ α)
: (v₂ x ≥ (v₂ y) ^ α) := by
  have sequbelow : ∃ a : ℕ → ℚ, (∀ i, (α : ℝ) > a i) ∧ Tendsto (fun k ↦ (a k : ℝ)) atTop (nhds α) := RatSeqBelowTendsto α 
  rcases sequbelow with ⟨a, ha₀, ha₁⟩
  have hxa : ∀ (i : ℕ), v₁ x > ((v₁ y): ℝ) ^ (a i) := by
    intro i 
    rw [hx₁]
    exact Real.rpow_lt_rpow_of_exponent_lt hy (ha₀ i)
  have hv₁ : ∀ (i : ℕ), v₁ x > ((v₁ y): ℝ) ^ (((a i).num : ℚ) / ((a i).den :ℚ)) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by 
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [this']
    exact (hxa i)
  have hxa₂ : ∀ (i : ℕ), v₁ ((x ^ (a i).den) / (y ^ (a i).num)) > 1 := sorry
  have hv₂ : ∀ (i : ℕ), v₂ x > ((v₂ y): ℝ) ^ (((a i).num: ℚ) / ((a i).den : ℚ)) := by
    have hxa₃ : ∀ (i : ℕ), v₂ ((x ^ (a i).den) / (y ^ (a i).num)) > 1 := 
      fun i => ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp (hxa₂ i)
    have hxa₄ : ∀ (i : ℕ), v₂ (x ^ (a i).den) > v₂ (y ^ (a i).num) := by
      intro i
      have this : (y ^ (a i).num) ≠ 0 := by
        have hvy : (v₁ y) ≠ 0 := gtonenezero hy
        have this' : y ≠ 0 := (Valuation.ne_zero_iff v₁).mp hvy
        exact zpow_ne_zero (a i).num this'
      exact (Valuation.div_ge_one_iff v₂ this).mp (hxa₃ i)
    have hxa₅ : ∀ (i : ℕ), (v₂ x) ^ ((a i).den) > (v₂ y) ^ ((a i).den) := sorry
    intro i
    specialize @hxa₅ i
    sorry
  have hv₂' : ∀ (i : ℕ), v₂ x > ((v₂ y): ℝ) ^ (a i) := by
    intro i
    have this : (a i).num / (a i).den  = a i := Rat.num_div_den (a i)
    have this' : (((a i).num : ℚ): ℝ) / (((a i).den : ℚ): ℝ) = ((a i): ℝ)  := by 
      rw [← (Rat.cast_div ((a i).num :ℚ) ((a i).den: ℚ))]
      exact congrArg Rat.cast this
    rw [←this']
    exact (hv₂ i)
  -- exp_continuous
  have hv₂'' : ∀ (i : ℕ), (v₂ x) ≥ ((v₂ y) : ℝ) ^ (a i) := fun i ↦ le_of_lt (hv₂' i)
  let f' := fun (x : ℝ) ↦ ((v₂ y) : ℝ) ^ x
  have f'ContinuousAt : ContinuousAt f' α := by
    have hy' : 1 < ((v₂ y) : ℝ) := by
      have hy₂ : 1 < v₂ y := ((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy
      exact hy₂
    exact rPowAt hy'
  let f := f' ∘ (fun i ↦ ((a i) : ℝ))
  have lim₁ : Tendsto f' (nhds α) (nhds (((v₂ y) : ℝ) ^ α)) := ContinuousAt.tendsto f'ContinuousAt
  have lim : Filter.Tendsto f atTop (nhds (((v₂ y) : ℝ) ^ α)) := Tendsto_comp_Tendsto ha₁ lim₁
  exact le_of_tendsto' lim hv₂''


theorem isEquiv_iff_pow_eq (v₁: Valuation K NNReal) 
(v₂ : Valuation K NNReal) (h₀ : ∃ (y : K), v₁ y > 1):
Valuation.IsEquiv v₁ v₂ ↔ ∃ (s : ℝ) (hs : s > 0), ∀ {x : K}, v₁ x = (v₂ x) ^ s where
  mp := by
    intro h
    have h₁ : ∀ {x : K}, v₁ x < 1 ↔ v₂ x < 1 := (Valuation.isEquiv_iff_val_lt_one v₁ v₂).mp h
    rcases h₀ with ⟨y, hy⟩
    have h₀ : ∃ (y : K), v₁ y > 1 := by
      use y
    have hxy : ∀ (x : K) (hx₀ : x ≠ 0), ∃ (α : ℝ), 
    ((v₁ x = (v₁ y) ^ α) ∧ v₂ x = (v₂ y) ^ α) := by 
      have hx : ∀ (x : K) (hx₀ : x ≠ 0), ∃ (α : ℝ), v₁ x = (v₁ y) ^ α := sorry
      intro x xneqzero
      specialize @hx x xneqzero
      rcases hx with ⟨α, hx₁⟩
      use α
      constructor
      · exact hx₁
      · have le₁ : v₂ x ≤ (v₂ y) ^ α := ExistSeqAbove v₁ v₂ hy h hx₁
        have ge₁ : (v₂ y) ^ α ≤ v₂ x := ExistSeqBelow v₁ v₂ hy h hx₁       
        exact le_antisymm_iff.mpr ⟨le₁, ge₁⟩ 
    let s := (Real.log (v₁ y)) / (Real.log (v₂ y))
    use s
    have hs : 0 < s := by
      have hs₁ : 0 < Real.log (v₁ y) := log_pos hy
      have hs₂ : 0 < Real.log (v₂ y) := log_pos (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)
      exact div_pos hs₁ hs₂
    use hs 
    intro x
    by_cases hx : x = 0
    · have this : v₁ x = 0 := (Valuation.zero_iff v₁).mpr hx
      have this' : v₂ x = 0 := (Valuation.zero_iff v₂).mpr hx
      have this₁ : ((v₁ x) : ℝ) = 0 := Iff.mpr (NNReal.coe_eq_zero ((v₁ x): NNReal)) this
      have this₂ : ((v₂ x) : ℝ) = 0 := Iff.mpr (NNReal.coe_eq_zero ((v₂ x): NNReal)) this'
      rw [this₁, this₂]
      have this'' : s ≠ 0 := ne_of_gt hs
      rw [(zero_rpow this'')]  
    · by_cases hxx : (v₂ x) = 1
      · have vxeqone : (v₁ x)  = 1 := by 
          exact ((Valuation.isEquiv_iff_val_eq_one v₁ v₂).mp h).mpr hxx
        have vxeqone' : ((v₁ x) : ℝ) = 1 := Iff.mpr (NNReal.coe_eq_one ((v₁ x): NNReal)) vxeqone
        have hxx' : ((v₂ x) : ℝ) = 1 := Iff.mpr (NNReal.coe_eq_one ((v₂ x): NNReal)) hxx
        rw [hxx', vxeqone']
        rw [Real.one_rpow s]
      · have hxy' :  (Real.log (v₁ x)) / (Real.log (v₂ x)) = (Real.log (v₁ y)) / (Real.log (v₂ y))  := by
          specialize @hxy x hx
          rcases hxy with ⟨α, hxy₁, hxy₂⟩
          rw [hxy₁, hxy₂] 
          have ha : α ≠ 0 := by
            intro h' 
            rw [h'] at hxy₂
            simp at hxy₂
            exact hxx hxy₂
          have this : log (((v₁ y) : ℝ) ^ α ) = α * log ((v₁ y) : ℝ) := by
            have hvy₁ : 0 < ((v₁ y) : ℝ) := pos_of_gt hy
            have hvy₂ : 0 < ((v₁ y) : ℝ) ^ α := rpow_pos_of_pos (pos_of_gt hy) α
            have hvy₃ : ((v₁ y) : ℝ) ^ α = ((v₁ y) : ℝ) ^ α := rfl 
            exact Eq.symm ((mul_log_eq_log_iff hvy₁ hvy₂).mpr hvy₃)
          have this' : log (((v₂ y) : ℝ) ^ α ) = α * log ((v₂ y) : ℝ) := by
            have hvy₁ : 0 < ((v₂ y) : ℝ) := pos_of_gt (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)
            have hvy₂ : 0 < ((v₂ y) : ℝ) ^ α := rpow_pos_of_pos (pos_of_gt (((Valuation.isEquiv_iff_val_gt_one v₁ v₂).mp h).mp hy)) α
            have hvy₃ : ((v₂ y) : ℝ) ^ α = ((v₂ y) : ℝ) ^ α := rfl 
            exact Eq.symm ((mul_log_eq_log_iff hvy₁ hvy₂).mpr hvy₃)
          rw [this, this']
          exact mul_div_mul_left (log (v₁ y)) (log (v₂ y)) ha 
        simp
        rw [←(hxy')]
        have this : 0 < v₁ x := by 
          have hneqzero : v₁ x ≠ 0 := Iff.mpr (Valuation.ne_zero_iff v₁) hx 
          exact Iff.mpr zero_lt_iff hneqzero
        have this' : 0 < v₂ x := by
          have hneqzero : v₂ x ≠ 0 := Iff.mpr (Valuation.ne_zero_iff v₂) hx 
          exact Iff.mpr zero_lt_iff hneqzero
        have this'' : ((v₂ x) : ℝ) ≠ 1 := by
          intro hxx'
          have this : v₂ x = 1 := Iff.mp (NNReal.coe_eq_one (v₂ x)) hxx'
          exact hxx this
        exact exp_eq this this' this''
    
  mpr := by 
    intro h
    rcases h with ⟨s, hs, h⟩
    apply (Valuation.isEquiv_iff_val_lt_one v₁ v₂).mpr
    intro x
    constructor
    · by_cases hx : x = 0 
      · intro hv₁
        have this : v₂ x = 0 := (Valuation.zero_iff v₂).mpr hx
        rw [this]
        exact one_pos
      · intro hv₁
        specialize @h x
        have hv₁ : ((v₁ x): ℝ) < 1 := hv₁ 
        rw [h] at hv₁
        have hvpos : v₂ x > 0 := by
          have this : v₂ x ≠ 0 := (Valuation.ne_zero_iff v₂).mpr hx
          exact Iff.mpr zero_lt_iff this
        simpa [hs, lt_asymm hs] using ((Real.rpow_lt_one_iff_of_pos hvpos)).mp hv₁
    · by_cases hx : x = 0
      · intro hv₁
        have this : v₁ x = 0 := (Valuation.zero_iff v₁).mpr hx
        rw [this]
        exact one_pos
      · intro hv₂
        specialize @h x
        have hv₂ : ((v₂ x): ℝ) < 1 := hv₂
        apply NNReal.coe_lt_coe.mp
        rw [h]
        have hvpos : v₂ x > 0 := by
          have this : v₂ x ≠ 0 := (Valuation.ne_zero_iff v₂).mpr hx
          exact Iff.mpr zero_lt_iff this
        exact Iff.mpr (Real.rpow_lt_one_iff_of_pos hvpos) (Or.inr { left := hv₂, right := hs })

theorem Valuation.map_negpow {K : Type u_3} [Field K]
(v : Valuation K NNReal) (x : K)  (m : ℤ) :
v (x ^ m) = (v x) ^ m := by
  cases m with 
    | ofNat a => sorry
    | negSucc m => sorry
      

theorem ratpow {x y : K} {m : ℤ} {n : ℕ} (v : Valuation K NNReal) 
(hv : v x < ((v y) : ℝ) ^ (m / n)) (hn : 0 < n) (hy : y ≠ 0):
  v ((x ^ n) / (y ^ m)) < 1 := by
  have this : (v x) ^ n < (v y) ^ m := sorry
  have this' : v (x ^ n) < v (y ^ m) := by 
    rw [←(Valuation.map_pow v x n)] at this
    rw [←(Valuation.map_negpow v y m)] at this
    exact this
  have hv : y ^ m ≠ 0 := zpow_ne_zero m hy
  exact (Valuation.div_le_one_iff v hv).mpr this'
  