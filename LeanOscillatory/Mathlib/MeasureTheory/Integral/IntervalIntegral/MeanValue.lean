module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Monotone.Extension

/-!
# Second mean value theorem for interval integrals

This file contains the second mean value theorem and a Banach-space valued variant.

## Main results

* `exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn`
* `exists_norm_intervalIntegral_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn`
-/

public section

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- **Second mean value theorem for interval integrals** with a nonnegative nonincreasing weight. -/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : 0 ≤ f b)
    (hf_mon : AntitoneOn f (Icc a b)) (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x := by
  sorry

/-- A Banach-space-valued version of the second mean value theorem.
Note this is necessarily an inequality. -/
theorem exists_norm_intervalIntegral_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → ℝ} {g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : 0 ≤ f b)
    (hf_mon : AntitoneOn f (Icc a b)) (hg : IntervalIntegrable g volume a b) : ∃ ξ ∈ Icc a b,
    ‖∫ x in a..b, f x • g x‖ ≤ f a * ‖∫ x in a..ξ, g x‖ := by
  sorry
