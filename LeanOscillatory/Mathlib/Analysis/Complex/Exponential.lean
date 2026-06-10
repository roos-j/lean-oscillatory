module

public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

variable (x y : ℂ)

theorem conj_exp_mul_I (x : ℝ) : conj (exp (x * I)) = exp (-(x * I)) := by
  sorry

end Complex

end
