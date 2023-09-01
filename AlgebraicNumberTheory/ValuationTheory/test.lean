import Mathlib.Topology.Algebra.ValuedField
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Rat.NNRat
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


variable {K : Type _} [Monoid K]

theorem commK (x y : K) : x * y = y * x := sorry 

theorem e {a b c: ℝ} (h : a = b ) (h1 : b < c) : a < c:= by exact Eq.trans_lt (id ( h)) h1

theorem z {a b c : NNRat} (h : a < 1) (h1 : a =1 ): False := by
  have h2 : ¬ a ≥ 1 := by exact Iff.mpr not_le h 
  apply h2
  exact Eq.ge h1

theorem a {a b : ℚ} (h : b = a) (h1 : 0 < a) : 0 < b := by exact Eq.trans_gt (id (Eq.symm h)) h1

theorem de {a b c : ℝ} (h : a ≤ 1 ) (h₁ : b ≤  1) (h2 : c ≤ a ∨ c ≤ b)
: c ≤ 1 := by
  rcases h2 with h₃ | h₄
  exact ge_trans h h₃
  exact ge_trans h₁ h₄

theorem spow {a : ℝ } (ha : a > 0)  {s : ℝ} (h : s > 0) 
(h1 : a ^ s < 1) : a < 1 := by 
  have ha₁ : s * Real.log a < 0 := sorry
  have ha₂ : Real.log a < 0 := Iff.mp (pos_iff_neg_of_mul_neg ha₁) h
  exact Iff.mp (Real.log_neg_iff ha) ha₂

#check le_trans

theorem dd {a b c : ℝ} (ha : a ≤ b) (hb : b < c) : a < c := by exact lt_of_le_of_lt ha hb

theorem d {x y : ℤ } (h : ¬x + y = 0): y + x ≠ 0 := by 
  exact fun h1 => h (Eq.mp (add_comm y x ▸ Eq.refl (y + x = 0)) h1)

theorem cc {a b : ℤ} (h : ¬a ≤ b) : a> b := by exact Iff.mp Int.not_le h
instance CommMonoidK : CommMonoid K where
  mul_comm := commK

theorem log_eq_log {a b : ℝ} (h1 : 0 < a) (h2 : 0 < b) (h : a = b): 
Real.log a = Real.log b := by exact congrArg Real.log h

theorem cd {a b : ℝ} (h : b ≠ 0 ) : a / b * b = a := by exact div_mul_cancel a h

open Real

theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩

theorem exp_eq {a b : ℝ} (h1 : 0 < a) (h2 : 0 < b) (h3 : b ≠ 1):
   a = b ^ ((Real.log a) / (Real.log b)) 
  := by
    have this : Real.log a = ((Real.log a) / (Real.log b)) * (Real.log b) := by 
      have this' : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h2 h3 
      exact Iff.mp (div_eq_iff this') rfl
    exact Eq.symm ((mul_log_eq_log_iff h2 h1).mp (Eq.symm this))


theorem ded {a b : ℝ } (h : a * b > b)(hb : 0 < b) : a > 1 := by exact Iff.mp (lt_mul_iff_one_lt_left hb) h



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

-- theorem th2 {a : ℝ} {m n : ℕ} : 
--   (a ^ m) ^ n = a ^ (m * n) := by exact Eq.symm (pow_mul a m n) 


theorem exp_con {a : ℝ} (ha : 1 < a) {α : ℝ} :
let f:= fun (x : ℝ) ↦ exp (a * x) ; Continuous f:= by continuity

theorem exp_conAt {a : ℝ} (ha : 1 < a) {α : ℝ} :
 ContinuousAt (fun (x : ℝ) ↦ exp (a * x)) α:= by 
  have h : Continuous (fun (x : ℝ) ↦ exp (a * x)) := by continuity  
  exact Continuous.continuousAt (h)

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


theorem gtonenezero {a : NNReal} (ha : 1 < a) : a ≠ 0 := by
  intro h
  have neq₁: (0 : NNReal)  ≤ 1 := by exact zero_le_one 
  rw [←h] at neq₁
  have neq₂ : ¬ a ≤ 1 := lt_iff_not_le.mp ha 
  exact neq₂ neq₁

theorem gtzero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 
  0 < a / b := by exact div_pos ha hb



theorem aa {a : NNReal} {α : ℝ } (h : 1 < a) : 0 < (a : ℝ) ^ α  := rpow_pos_of_pos (pos_of_gt h) α

-- theorem aaa {K : Type _} [Field K] (v₁ v₂ : Valuation K NNReal) {y : K} (hy : v₁ y > 1 ) 
-- : log (((v₁ y) : ℝ) ^ α ) = α * log ((v₁ y) : ℝ) := by
--   -- have hvy₁ : 0 < ((v₁ y) : ℝ) := pos_of_gt hy
--   -- have hvy₂ : 0 < ((v₁ y) : ℝ) ^ α := rpow_pos_of_pos (pos_of_gt hy) α
--   -- have hvy₃ : ((v₁ y) : ℝ) ^ α = ((v₁ y) : ℝ) ^ α := rfl 
--   -- exact Eq.symm ((mul_log_eq_log_iff hvy₁ hvy₂).mpr hvy₃)
--   refine ⟨Eq.symm ((@mul_log_eq_log_iff _ _ _ ?_ ?_).mpr ?_)⟩
--   · exact pos_of_gt hy
--   · exact rpow_pos_of_pos (pos_of_gt hy) α
--   · rfl

theorem aaa {a b α : ℝ } (h : α ≠ 0 ) (hb : b ≠ 0):
 α * a / (α * b) = a / b := by exact mul_div_mul_left a b h

theorem th3 {a b α : ℝ} (ha : a ≠ 1)  (hb : 1 < b) (h : a= b ^ α ):
α ≠ 0 := by 
  intro hv' 
  rw [hv'] at h
  simp at h
  exact ha h

