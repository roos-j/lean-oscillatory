import Mathlib

open Set Function intervalIntegral Interval MeasureTheory


/-- Second mean value theorem for integrals -/
theorem smvt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hf_mon : AntitoneOn f (Icc a b)) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc a b)) : ∃ ξ ∈ Icc a b,
    ∫ x in a..b, f x * g x = f a * ∫ x in a..ξ, g x := by
  sorry
