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

/-- If `f` is continuous on `[a, b]` and `|f x| ≥ 1` for all `x ∈ [a, b]`,
  then either `f x ≥ 1` for all `x ∈ [a, b]` or `f x ≤ -1` for all `x ∈ [a, b]`. -/
lemma _root_.ContinuousOn.forall_le_or_forall_le_of_forall_le_abs {a b : ℝ} {f : ℝ → ℝ}
    (hfcont : ContinuousOn f [[a, b]]) (hf : ∀ x ∈ [[a, b]], 1 ≤ |f x|) :
    (∀ x ∈ [[a, b]], 1 ≤ f x) ∨ (∀ x ∈ [[a, b]], f x ≤ -1) := by
  by_contra! h
  obtain ⟨⟨x₀, hx₀, hx₀'⟩, ⟨x₁, hx₁, hx₁'⟩⟩ := h
  replace hx₀' : f x₀ ≤ -1 := by sorry -- use `hx₀` and `hf x₀`
  replace hx₁' : f x₁ ≥ 1 := by sorry
  have h1 : f x₀ ≤ f x₁ := by linarith
  have h2 : [[x₀, x₁]] ⊆ [[a, b]] := uIcc_subset_uIcc hx₀ hx₁
  have : 0 ∈ [[f x₀, f x₁]] := by sorry -- start with `constructor`
  obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc (hfcont.mono h2) this
  specialize hf x (h2 hx)
  rw [hfx] at hf
  norm_num at hf

abbrev VanDerCorput.c (k : ℕ) : ℝ := 5 * 2 ^ (k - 1) - 2

open VanDerCorput

#check deriv_smul

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}

section SpecialCase

/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_one`
  where the amplitude function is constant and scalar.  -/
theorem norm_integral_exp_mul_I_le_of_order_one'
    (hφ : ContDiffOn ℝ 2 φ [[a, b]]) (h : ∀ x ∈ [[a, b]], 1 ≤ |derivWithin φ [[a, b]] x|)
    (hφ'_mono : MonotoneOn (derivWithin φ [[a, b]]) [[a, b]]) (hL : 0 < L) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c 1 * L⁻¹ := by
  have := hφ.continuousOn
  letI φ' := fun x ↦ derivWithin φ [[a, b]] x
  have hasDerivAt_φ : ∀ x ∈ [[a, b]], HasDerivWithinAt φ (φ' x) [[a, b]] x := fun x hx ↦
    DifferentiableWithinAt.hasDerivWithinAt <| (hφ.contDiffWithinAt hx).differentiableWithinAt (by norm_num)
  have hφ'cont : ContinuousOn φ' [[a, b]] := hφ.continuousOn_derivWithin_uIcc (by norm_num)

  obtain h' := hφ'cont.forall_le_or_forall_le_of_forall_le_abs h

  letI φ'' := fun x ↦ derivWithin φ' [[a, b]] x
  have hasDerivAt_φ' : ∀ x ∈ [[a, b]], HasDerivWithinAt φ' (φ'' x) [[a, b]] x := fun x hx ↦
    DifferentiableWithinAt.hasDerivWithinAt <|
      (hφ.contDiffWithinAt hx).differentiableWithinAt_derivWithin_uIcc hx (by norm_num)
  have hφ''_cont : ContinuousOn φ'' [[a, b]] := by
    convert hφ.continuousOn_iteratedDerivWithin_uIcc (m := 2) (by norm_num)
    ext
    rw [iteratedDerivWithin_two]

  obtain ⟨x₀, _, hx₀'⟩ := isCompact_uIcc.exists_isMaxOn nonempty_uIcc <| ContinuousOn.abs hφ''_cont
  have hC₀ := isMaxOn_iff.mp hx₀'
  set C₀ := |φ'' x₀|

  letI u := fun x ↦ 1 / (L * φ' x * I)
  letI v := fun x ↦ exp (L * φ x * I)
  letI u' := fun x ↦ (φ'' x) * I / (L * (φ' x) ^ 2)
  letI v' := fun x ↦ L * φ' x * I * exp (L * φ x * I)

  have hφ'_nz {x : ℝ} (hx : x ∈ [[a, b]]) : φ' x ≠ 0 := by
    rcases h' with h' | h'
      <;> linarith only [h' x hx]

  have hnz1 {x : ℝ} (hx : x ∈ [[a, b]]) : L * φ' x * I ≠ 0 := by
    apply Complex.ne_zero_of_im_ne_zero
    simp [(ne_of_lt hL).symm, hφ'_nz hx]

  have hnz2 {x : ℝ} (hx : x ∈ [[a, b]]) : (L : ℂ) * (φ' x) ^ 2 ≠ 0 := by
    norm_cast
    have := hφ'_nz hx
    positivity

  have hasDerivAt_u : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const _ _ _) (.mul (.mul (hasDerivWithinAt_const _ _ _) (.ofReal_comp <| hasDerivAt_φ' _ hx)) (hasDerivWithinAt_const _ _ _)) (hnz1 hx) using 1
    simp [mul_pow, u']
    have := hφ'_nz hx
    have := hnz2 hx
    have : ofReal L ^ 2 * (φ' x) ^ 2 ≠ 0 := by norm_cast; positivity
    field_simp
    ring

  have hasDerivAt_v : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x := by
    intro x hx
    convert HasDerivWithinAt.cexp (.mul (.mul (hasDerivWithinAt_const _ _ _)
      (.ofReal_comp <| hasDerivAt_φ _ hx)) (hasDerivWithinAt_const _ _ _)) using 1
    simp [v']
    ring

  have h1 : ∫ x in a..b, exp (L * φ x * I) = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
    suffices h'' : ∀ x ∈ [[a, b]], exp (L * φ x * I) = u x * v' x by
      rw [integral_congr h'']
      refine integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt hasDerivAt_u hasDerivAt_v ?_ ?_
      · exact ContinuousOn.intervalIntegrable (by fun_prop (discharger := assumption))
      · exact ContinuousOn.intervalIntegrable (by fun_prop (discharger := assumption))
    intro x hx
    simp only [u, v']
    field_simp [hnz1 hx]

  have h2 {x : ℝ} (hx : x ∈ [[a, b]]) : ‖u x * v x‖ ≤ L⁻¹ := by
    simp only [u, v, norm_mul, norm_div, norm_one]
    norm_cast
    rw [norm_exp_ofReal_mul_I]
    have : 0 < L * |φ' x| := by have := h x hx; positivity
    refine le_of_mul_le_mul_left ?_ this
    field_simp [abs_of_pos, φ', h x hx]

  have hasDerivAt_φ'_int : ∀ x ∈ uIoo a b, HasDerivWithinAt (fun x ↦ -1 / φ' x) (φ'' x / (φ' x) ^ 2) (Ioi x) x := by
    intro x hx
    have hx' := uIoo_subset_uIcc _ _ hx
    have := ((hasDerivAt_φ' x hx').mono (uIoo_subset_uIcc _ _)).hasDerivAt <| uIoo_mem_nhds hx
    convert HasDerivWithinAt.div (hasDerivWithinAt_const _ _ _) this.hasDerivWithinAt ?_ using 1
    · simp
    · exact hφ'_nz hx'

  have hnorm_u'_eq : ∀ x ∈ [[a, b]], ‖u' x‖ = φ'' x / (φ' x) ^ 2 * L⁻¹ := by
    intro x hx
    simp only [Complex.norm_div, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_eq_self.mpr (le_of_lt hL), norm_pow, sq_abs, u']
    rw [abs_of_nonneg <| hφ'_mono.derivWithin_nonneg (x := x), mul_comm L]
    have : φ' x ^ 2 * L ≠ 0 := by haveI := hφ'_nz hx; positivity
    field_simp
    rfl

  have hv {x : ℝ} : ‖v x‖ = 1 := by
    simp only [v]
    exact_mod_cast norm_exp_ofReal_mul_I _

  have h3 : ‖∫ x in a..b, u' x * v x‖ ≤ L⁻¹ := by
    apply le_trans norm_integral_le_abs_integral_norm
    simp_rw [norm_mul, hv, mul_one]
    rw [integral_congr hnorm_u'_eq, integral_mul_const]
    rw [integral_eq_sub_of_hasDeriv_right ?_ hasDerivAt_φ'_int]
    · rw [abs_mul, abs_of_pos (show 0 < L⁻¹ by positivity)]
      refine le_of_mul_le_mul_right ?_ hL
      rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one, neg_div, neg_div, sub_neg_eq_add]
      rcases h' with h' | h'
      · have ha1 := div_nonneg zero_le_one <| le_trans zero_le_one <| h' _ left_mem_uIcc
        have hb1 := div_nonneg zero_le_one <| le_trans zero_le_one <| h' _ right_mem_uIcc
        have := one_div_le (lt_of_lt_of_le zero_lt_one <| h' _ left_mem_uIcc) zero_lt_one |>.mpr
        have ha2 := div_self (G₀ := ℝ) one_ne_zero ▸ this <| h' _ left_mem_uIcc
        have := one_div_le (lt_of_lt_of_le zero_lt_one <| h' _ right_mem_uIcc) zero_lt_one |>.mpr
        have hb2 := div_self (G₀ := ℝ) one_ne_zero ▸ this <| h' _ right_mem_uIcc
        rcases le_or_gt 0 (-(1 / φ' b) + 1 / φ' a) with hab | hab
        · rw [abs_of_nonneg hab]; linarith only [ha2, hb1]
        · rw [abs_of_neg hab]; linarith only [ha1, hb2]
      · have ha1 := div_nonpos_iff.mpr (Or.inl ⟨zero_le_one, le_trans (h' _ left_mem_uIcc) (le_of_lt neg_one_lt_zero)⟩)
        have hb1 := div_nonpos_iff.mpr (Or.inl ⟨zero_le_one, le_trans (h' _ right_mem_uIcc) (le_of_lt neg_one_lt_zero)⟩)
        have ha2 : -(1 / φ' a) ≤ 1 := by
          simpa only [← neg_div] using div_le_one_of_ge (h' _ left_mem_uIcc)
            <| le_trans (h' _ left_mem_uIcc) <| le_of_lt neg_one_lt_zero
        have hb2 : -(1 / φ' b) ≤ 1 := by
          simpa only [← neg_div] using div_le_one_of_ge (h' _ right_mem_uIcc)
            <| le_trans (h' _ right_mem_uIcc) <| le_of_lt neg_one_lt_zero
        rcases le_or_gt 0 (-(1 / φ' b) + 1 / φ' a) with hab | hab
        · rw [abs_of_nonneg hab]; linarith only [ha1, hb2]
        · rw [abs_of_neg hab]; linarith only [ha2, hb1]
    · apply ContinuousOn.intervalIntegrable
      fun_prop (discharger := exact fun x hx ↦ by haveI := hφ'_nz hx; positivity)
    · fun_prop (discharger := exact fun x hx ↦ by haveI := hφ'_nz hx; positivity)

  calc
    _ ≤ ‖∫ x in a..b, u' x * v x‖ + ‖u b * v b - u a * v a‖ := by
      rw [h1, sub_eq_neg_add]
      nth_rewrite 2 [← norm_neg]
      exact norm_add_le _ _
    _ ≤ L⁻¹ + 2 * L⁻¹ := by
      gcongr
      apply le_trans (norm_sub_le _ _) (by linarith only [h2 left_mem_uIcc, h2 right_mem_uIcc])
    _ = _ := by ring


/-- **Van der Corput's lemma**. Special case of `norm_integral_exp_mul_I_le_of_order_ge_two`
  where the amplitude function is constant and scalar.  -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two' (k : ℕ) (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ k φ ([[a, b]])) (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDeriv k φ x|)
    (hL : 0 < L) : ‖∫ x in a..b, exp (L * φ x * I)‖ ≤ c k * L ^ (- (1 : ℝ) / k) := by
  -- have h1 : ∫ x in a..b, exp (L * φ x * I) = ∫ x in a..b,
  sorry

end SpecialCase

section GeneralCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable  {ψ : ℝ → E}

/-- **Van der Corput's lemma** for vector-valued amplitude functions, first order case.
For second and higher order see `norm_integral_exp_mul_I_le_of_order_ge_two`. -/
theorem norm_integral_exp_mul_I_le_of_order_one
    (hφ : ContDiffOn ℝ 1 φ ([[a, b]])) (hψ : ContDiffOn ℝ 1 ψ ([[a, b]]))
    (h : ∀ x ∈ [[a, b]], 1 ≤ |deriv φ x|) (h' : Monotone φ) (hL : L ≠ 0) :
  ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤ c 1 * |L|⁻¹ * (‖ψ b‖ + ∫ x in a..b, ‖deriv ψ x‖) := by
  sorry

/-- **Van der Corput's lemma** for vector-valued amplitude functions, case `k ≥ 2`.
For `k = 1` see `norm_integral_exp_mul_I_le_of_order_one`. -/
theorem norm_integral_exp_mul_I_le_of_order_ge_two (k : ℕ) (hk : 2 ≤ k)
    (hφ : ContDiffOn ℝ 1 φ ([[a, b]])) (hψ : ContDiffOn ℝ k ψ ([[a, b]]))
    (h : ∀ x ∈ [[a, b]], 1 ≤ |iteratedDeriv k φ x|) (hL : L ≠ 0) :
  ‖∫ x in a..b, exp (L * φ x * I) • ψ x‖ ≤ c k * |L| ^ ((-1 : ℝ) / k) * (‖ψ b‖ + ∫ x in a..b, ‖deriv ψ x‖) := by
  sorry

end GeneralCase

end

--end VanDerCorput

end Oscillatory

#min_imports
