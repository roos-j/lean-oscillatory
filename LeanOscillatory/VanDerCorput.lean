import LeanOscillatory.Basic

/-!
# Van der Corput's lemma

In this file we prove van der Corput's lemma for oscillatory integrals
of the first kind in one real variable, following Stein.

## Main results

`abs_integral_exp_mul_I_le_of_order_one`: van der Corput's lemma, first order case
`abs_integral_exp_mul_I_le_of_order_ge_two`: van der Corput's lemma, higher order case

## References

*E. M. Stein:
Harmonic Analysis: Real-Variable Methods, Orthogonality and Oscillatory Integrals
Ch. VIII.1, Prop. 2, p. 332-334*
-/

namespace Oscillatory

--namespace VanDerCorput

noncomputable section

open Set Complex NNReal Function
open intervalIntegral Interval

open Preliminaries

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}

section SpecialCase

#check c

-- Auxiliary lemma: adapt appropriately
example {f : ℝ → ℝ} (hf : Continuous f) (hf2 : ∀ x, 1 ≤ |f x|) : (∀ x, 1 ≤ f x) ∨ (∀ x, f x ≤ -1) := by
  by_contra! h
  obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩ := h
  replace hx₀ : f x₀ ≤ -1 := by sorry
  replace hx₁ : f x₁ ≥ 1 := by sorry
  have h1 : f x₀ ≤ f x₁ := by linarith
  have : 0 ∈ [[f x₀, f x₁]] := by sorry
  obtain ⟨x, _, hx⟩ := intermediate_value_uIcc (Continuous.continuousOn hf) this
  specialize hf2 x
  rw [hx] at hf2
  norm_num at hf2

#check deriv_smul
#check integral_mul_deriv_eq_deriv_mul
#check integral_congr
/-- **Van der Corput's lemma**. Special case of `abs_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar.  -/
theorem abs_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 1 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], 1 ≤ |deriv φ x|)
    (h' : Monotone φ) (hL : L ≠ 0) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c 1 * |L|⁻¹ := by
  wlog h : ∀ x ∈ [[a, b]], 1 ≤ deriv φ x; focus {
    sorry
  }
  sorry


/-- **Van der Corput's lemma**. Special case of `abs_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar.  -/
theorem abs_integral_exp_mul_I_le_of_order_ge_two' (k : ℕ) (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ k φ ([[a, b]])) (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDeriv k φ x|)
    (hL : L ≠ 0) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c k * |L| ^ (- (1 : ℝ) / k) := by
  -- have h1 : ∫ x in a..b, exp (L * φ x * I) = ∫ x in a..b,
  sorry

end SpecialCase

section GeneralCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable  {ψ : ℝ → E}

/-- **Van der Corput's lemma** for vector-valued amplitude functions, first order case.
For second and higher order see `abs_integral_exp_mul_I_le_of_order_ge_two`. -/
theorem abs_integral_exp_mul_I_le_of_order_one
    (hφ : ContDiffOn ℝ 1 φ ([[a, b]])) (hψ : ContDiffOn ℝ 1 ψ ([[a, b]]))
    (h : ∀ x ∈ [[a, b]], 1 ≤ |deriv φ x|) (h' : Monotone φ) (hL : L ≠ 0) :
  ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤ c 1 * |L|⁻¹ * (‖ψ b‖ + ∫ x in a..b, ‖deriv ψ x‖) := by
  sorry

/-- **Van der Corput's lemma** for vector-valued amplitude functions, case `k ≥ 2`.
For `k = 1` see `abs_integral_exp_mul_I_le_of_order_one`. -/
theorem abs_integral_exp_mul_I_le_of_order_ge_two (k : ℕ) (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ 1 φ ([[a, b]])) (hψ : ContDiffOn ℝ k ψ ([[a, b]]))
    (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDeriv k φ x|) (hL : L ≠ 0) :
  ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤ c k * |L| ^ ((-1 : ℝ) / k) * (‖ψ b‖ + ∫ x in a..b, ‖deriv ψ x‖) := by
  sorry

end GeneralCase

end

--end VanDerCorput

end Oscillatory

#min_imports
