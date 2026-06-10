module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

section RCLike

variable [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} {μ : Measure ℝ}

open scoped ComplexConjugate in
theorem intervalIntegral_conj : ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ) := by
  sorry

end RCLike

end

end
