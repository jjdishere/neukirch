import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.EMetricSpace
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Bezout
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Algebra.Basic

open Filter TopologicalSpace Set Classical UniformSpace Function

open Classical Uniformity Topology Filter

class CompleteNormedField (α : Type _) 
  extends Norm α, Field α, MetricSpace α, CompleteSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is multiplicative. -/
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete_field : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

class ArchimedeanField (α : Type _)
  extends NormedField α where 
  anti_tri_ineq : ∃ x y, norm (x + y) > max (norm x) (norm y)

#check Archimedean

/- Proposition 4.2 : Let K be a field which is complete with respect to
  an archimedean valuation | |. Then there is an isomorphism σ from K 
  onto ℝ or ℂ satisfying |a| = |σ a| ^ s for all a ∈ K,
  for some fixed s ∈ (0,1]. -/
theorem Ostrowski {K :Type _} [NormedField K] [CompleteSpace K] [ArchimedeanField K]
    :∃ (f : K ≃+* ℂ), ∀ (x : K), ∃ (s : ℝ), 0 < s → s < 1 → |norm x| = |norm (f x)| ^ s
      ∨  ∃ (f : K ≃+* ℝ), ∀ (x : K), ∃ (s : ℝ), 0 < s → s < 1 → |norm x| = |norm (f x)| ^ s 
    := sorry 

open ValuationRing
open Completion
open LocalRing

#check Completion
#check ValueGroup
#check Valuation
#check ValuationRing.localRing

variable (𝓞 : Type u) [CommRing 𝓞]

variable (K : Type v) [Field K] [Algebra 𝓞 K]

-- theorem ResidualOfCompletion  {p : Type _} [IsDomain 𝓞] 
--   [ValuationRing 𝓞] (ValueGroup 𝓞 K) [CommSemiring 𝓞] [LocalRing 𝓞] 
--   [p : maximalIdeal 𝓞] [𝓞' : Completion 𝓞] [K' : ValueGroup 𝓞'] 
--   [p' : LocalRing.maximalIdeal 𝓞']
--   : 𝓞' ⧸ p' ≃+* 𝓞 ⧸ p  := sorry
