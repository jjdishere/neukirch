import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem spow {a : ℝ } (ha : a > 0)  {s : ℝ} (h : s > 0) 
(h1 : a ^ s < 1) : a < 1 := by
  simpa [h, lt_asymm h] using ((Real.rpow_lt_one_iff_of_pos ha)).mp h1
  

theorem spow2 {a : ℝ } (ha : 0 < a)  {s : ℝ} (h : 0 < s) 
(h1 : a ^ s < 1) : a < 1 := by
  have ineq := ((Real.rpow_lt_one_iff_of_pos ha)).mp h1
  have : ¬ s < 0 := lt_asymm h
  simp [h, this] at ineq
  exact ineq

theorem spow3 {a : ℝ } (ha : 0 < a)  {s : ℝ} (h : 0 < s) 
(h1 : a < 1) : a ^ s < 1 := by
  exact Iff.mpr (Real.rpow_lt_one_iff_of_pos ha) (Or.inr { left := h1, right := h })


theorem rat1 (a : ℕ → ℚ) : ∀ (i : ℕ), a i = (a i).num / (a i).den := fun i => Eq.symm (Rat.num_div_den (a i)) 



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

