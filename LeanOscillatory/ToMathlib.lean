import Mathlib

section Analysis.Complex.RealDeriv

variable {s : Set ℝ} {z : ℝ}

open Complex in
set_option backward.isDefEq.respectTransparency false in -- Lean has a new bug/feature(?) which makes this necessary
theorem HasDerivWithinAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivWithinAt f u s z) :
    HasDerivWithinAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u s z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using
    ofRealCLM.hasDerivWithinAt.scomp z hf <| fun _ _ ↦ Set.mem_univ _

end Analysis.Complex.RealDeriv
