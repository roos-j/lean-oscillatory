import LeanOscillatory.Basic
import LeanOscillatory.ToMathlib

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

abbrev c (k : ℕ) : ℝ := 5 * 2 ^ (k - 1) - 2

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

#check mul_div_cancel₀

/-- **Van der Corput's lemma**. Special case of `abs_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar.  -/
theorem abs_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], 1 ≤ |deriv φ x|)
    (h' : Monotone φ) (hL : 0 < L) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c 1 * L⁻¹ := by
  wlog h : ∀ x ∈ [[a, b]], 1 ≤ deriv φ x; focus {
    sorry
  }
  let φ' := fun x ↦ deriv φ x
  -- have φ'_eq {x : ℝ} : φ' x = deriv φ x := by rfl
  let u := fun x ↦ 1 / (L * φ' x * I)
  let v := fun x ↦ exp (L * φ x * I)
  let u' := fun x ↦ (deriv φ' x) * I / (L * (φ' x) ^ 2)
  let v' := fun x ↦ L * φ' x * I * exp (L * φ x * I)
  have hnz : ∀ x ∈ [[a, b]], L * φ' x * I ≠ 0 := by
      intro x hx
      have := h x hx
      apply Complex.ne_zero_of_im_pos
      simp
      positivity
  have hasDeriv_u : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x := by
    intro x hx
    have := h x hx
    have hasDerivAt_φ' : HasDerivAt φ' (deriv φ' x) x := by sorry
    convert HasDerivAt.div (hasDerivAt_const _ _) (.mul (.mul (hasDerivAt_const _ _) (.ofReal_comp hasDerivAt_φ')) (hasDerivAt_const _ _)) (hnz x hx) using 1
    simp [mul_pow, u']
    have : ofReal L * (φ' x) ^ 2 ≠ 0 := by norm_cast; positivity
    have : ofReal L ^ 2 * (φ' x) ^ 2 ≠ 0 := by norm_cast; positivity
    field_simp
    ring
  have hasDeriv_v : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x := by
    intro x hx
    have hasDerivAt_φ : HasDerivAt φ (φ' x) x := by sorry
    convert HasDerivAt.cexp (.mul (.mul (hasDerivAt_const _ _) (.ofReal_comp hasDerivAt_φ)) (hasDerivAt_const _ _)) using 1
    simp [v']
    ring
  have h1 : ∫ x in a..b, exp (L * φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h : ∀ x ∈ [[a, b]], exp (L * φ x * I) = u x * v' x by
      rw [integral_congr h]
      refine integral_mul_deriv_eq_deriv_mul hasDeriv_u hasDeriv_v ?_ ?_
      · apply ContinuousOn.intervalIntegrable
        intro x hx
        apply ContinuousWithinAt.div
        · apply ContinuousWithinAt.mul
          · sorry
          · sorry
        · sorry
        · sorry
      · sorry
    intro x hx
    simp only [u, v, v']
    field_simp [hnz _ hx]
  have h2 : ‖u b * v b - u a * v a‖ ≤ 2 * L⁻¹ := by
    sorry
  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ L⁻¹ := by
    have hφ' : ∀ x ∈ [[a, b]], ‖deriv (fun x ↦ 1 / φ' x) x‖ = deriv (fun x ↦ -1 / φ' x) x := by
      sorry
    sorry
  calc
    _ ≤ ‖∫ x in a..b, u' x * v x‖ + ‖u b * v b - u a * v a‖ := by
      rw [h1, sub_eq_neg_add]
      nth_rewrite 2 [← norm_neg]
      exact norm_add_le _ _
    _ ≤ L⁻¹ + 2 * L⁻¹ := by gcongr
    _ = _ := by ring



/-- **Van der Corput's lemma**. Special case of `abs_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar.  -/
theorem abs_integral_exp_mul_I_le_of_order_ge_two' (k : ℕ) (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ k φ ([[a, b]])) (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDeriv k φ x|)
    (hL : 0 < L) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c k * L ^ (- (1 : ℝ) / k) := by
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
