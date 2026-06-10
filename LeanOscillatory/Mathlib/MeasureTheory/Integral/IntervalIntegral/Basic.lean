module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 ε ε' E F A : Type*} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']

namespace intervalIntegral

section RCLike

variable [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} {μ : Measure ℝ}

section LinearIsometry

variable {a b : ℝ} {μ : Measure ℝ} {f : ℝ → E}
variable [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable [NormedSpace ℝ F] [NormedSpace ℝ E] [CompleteSpace E] [CompleteSpace F]

-- Missing analogue of `LinearIsometry.integral_comp_comm`
theorem _root_.LinearIsometry.intervalIntegral_comp_comm (L : E →ₗᵢ[𝕜] F) (f : ℝ → E) :
    ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm, L.map_sub]

end LinearIsometry

-- Missing analogue of `integral_conj`
open scoped ComplexConjugate in
theorem intervalIntegral_conj : ∫ x in a..b, conj (f x) ∂μ = conj (∫ x in a..b, f x ∂μ) :=
  RCLike.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

end RCLike

end intervalIntegral

end

end
