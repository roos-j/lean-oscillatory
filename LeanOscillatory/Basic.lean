import Mathlib

/-!

Some basic definitions.

-/

namespace Oscillatory

namespace Preliminaries

noncomputable section

open Set Complex NNReal Function
open intervalIntegral Interval

variable {a b : ℝ} {L : ℝ}
variable {φ : ℝ → ℝ}

/-- Complex exponential `exp (x * I)` -/
abbrev e (x : ℝ) := exp (x * I)

/-- Auxiliary differential operator `D` -/
abbrev D (φ : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) := (deriv φ x * I)⁻¹ * deriv f x

theorem _root_.HasDerivAt.e {φ' : ℝ} {x : ℝ} (hφ : HasDerivAt φ φ' x) :
    HasDerivAt (fun x ↦ e (φ x)) (φ' * I * e (φ x)) x := by
  convert HasDerivAt.cexp <| HasDerivAt.smul_const hφ I using 1
  rw [Oscillatory.Preliminaries.e, real_smul, real_smul, mul_comm]

theorem deriv_e {φ' : ℝ} {x : ℝ} (hφ : HasDerivAt φ φ' x) :
    deriv (fun x ↦ e (φ x)) x = φ' * I * e (φ x) := HasDerivAt.deriv <| HasDerivAt.e hφ

theorem D_exp_mul_I {φ' : ℝ} {x : ℝ} (hφ : HasDerivAt φ φ' x) (hφ' : φ' ≠ 0) : e (φ x) = (D φ) (fun x ↦ e (φ x)) x := by
  rw [D, deriv_e hφ (φ' := φ'), HasDerivAt.deriv hφ]
  have : φ' * I ≠ 0 := by sorry -- There should be a tactic `nonvanishing`
  field_simp

theorem iterate_D_exp_mul_I (n : ℕ) {φ' : ℝ} {x : ℝ} (hφ : HasDerivAt φ φ' x) (hφ' : φ' ≠ 0) :
    e (φ x) = (D φ)^[n] (fun x ↦ e (φ x)) x := by
  induction' n with n ih
  · simp
  · rw [iterate_succ, comp_apply]
    sorry


end

end Preliminaries

end Oscillatory
