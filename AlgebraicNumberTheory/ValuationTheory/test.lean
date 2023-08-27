import Mathlib.Topology.Algebra.ValuedField
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Rat.NNRat
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


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

theorem des {a b : ℝ } (ha : a > 0) (hb : b > 0) {s : ℝ} (h : s > 0) 
(h1 : a ^ s = 1) : a = 1 := by 
  have h₁ :  Real.log (a ^ s) = Real.log 1 := by exact congrArg Real.log h1
  have h₂ : s * Real.log a = Real.log 1 := by sorry
  sorry

#check le_trans

theorem dd {a b c : ℝ} (ha : a ≤ b) (hb : b < c) : a < c := by exact lt_of_le_of_lt ha hb

theorem d {x y : ℤ } (h : ¬x + y = 0): y + x ≠ 0 := by 
  exact fun h1 => h (Eq.mp (add_comm y x ▸ Eq.refl (y + x = 0)) h1)

theorem cc {a b : ℤ} (h : ¬a ≤ b) : a> b := by exact Iff.mp Int.not_le h
instance CommMonoidK : CommMonoid K where
  mul_comm := commK
