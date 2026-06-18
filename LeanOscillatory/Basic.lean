module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Circle

-- Temporary imports
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!

-/

@[expose] public section

namespace Complex

open scoped ComplexConjugate

/--
Complex exponential as a function `ℝ → ℂ`, `x ↦ exp (x * I)`.
TODO: Decide what name is best: `expI` seems very clear, but e.g. `cis` is also widely used
-/
noncomputable def expI : ℝ → ℂ := fun x ↦ exp (x * I)


-- TODO: Basic properties, mirror `cexp`
#check cexp

theorem expI_eq_exp_ofReal_mul_I (x : ℝ) : expI x = exp (x * I) := by rfl

@[simp]
theorem expI_zero : expI 0 = 1 := by simp [expI]

@[simp]
theorem norm_expI (x : ℝ) : ‖expI x‖ = 1 := by simp [expI]

theorem conj_expI (x : ℝ) : conj (expI x) = expI (-x) := by simp [expI, ← exp_conj]


section Continuous
#check ContinuousOn.cexp

variable {α : Type*} [TopologicalSpace α] {f : α → ℝ} {s : Set α}

@[fun_prop]
theorem ContinuousOn.expI (h : ContinuousOn f s) : ContinuousOn (fun y => expI (f y)) s :=
  .cexp (.mul_const (Continuous.comp_continuousOn' continuous_ofReal h) I)

end Continuous

section Deriv

#check hasDerivAt_exp

theorem hasDerivAt_expI (x : ℝ) : HasDerivAt expI (I * expI x) x := by
  convert! HasDerivAt.cexp (.mul_const (.ofReal_comp <| hasDerivAt_id _) I) using 1
  simp [expI, mul_comm]

-- variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
-- TODO: Mirror the `cexp` API

variable {f : ℝ → ℝ} {f' : ℝ} {x : ℝ}

-- TODO: Insert HasStrictDerivAt.expI, HasDerivAt.expI, deriv_expI

variable {s : Set ℝ}
#check HasDerivWithinAt.cexp

theorem HasDerivAt.expI (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x ↦ expI (f x)) (I * expI (f x) * f') x := by
  convert! HasDerivAt.cexp (.mul_const (.ofReal_comp <| hf) I) using 1
  rw [expI_eq_exp_ofReal_mul_I]
  ring

theorem HasDerivWithinAt.expI (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => expI (f x)) (I * expI (f x) * f') s x := by
  convert! HasDerivWithinAt.cexp (.mul_const (.ofReal_comp <| hf) I) using 1
  rw [expI_eq_exp_ofReal_mul_I]
  ring

end Deriv

section FDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → ℝ} {f' : E →L[𝕜] ℝ} {x : E} {s : Set E}

-- theorem HasFDerivWithinAt.expI (hf : HasFDerivWithinAt f f' s x) :
--     HasFDerivWithinAt (fun x => expI (f x)) (expI (f x) • f') s x :=
--   sorry
  -- (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

#check HasFDerivWithinAt.cexp

end FDeriv

end Complex

namespace Oscillatory

open Complex

@[inherit_doc] scoped notation "𝐞" => expI

end Oscillatory

open Oscillatory Complex

-- example (x : ℝ) : ∫ x in a..b, (probChar x)

#check Real.probChar
#check Real.fourierChar
#check Real.deriv_fourierChar
#check Circle.exp

#check HasDerivWithinAt.cexp
-- example (x : ℝ) : (fourierChar : ℝ → ℂ)

--#synth FunLike (AddChar ℝ Circle)

end
