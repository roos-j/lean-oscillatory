import LeanOscillatory.Basic

namespace Complex

lemma ne_zero_of_im_pos {s : ℂ} (hs : 0 < s.im) : s ≠ 0 :=
  fun h ↦ (zero_im ▸ h ▸ hs).false

end Complex

section ContDiffOn

/- Todo: generalize to ordered field -/

variable {a b : ℝ}
variable {n : WithTop ℕ∞}
variable {f : ℝ → ℝ}

open Real Interval

theorem ContDiffOn.continuousOn_derivWithin_uIcc (h : ContDiffOn ℝ n f [[a, b]])
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f [[a, b]]) [[a, b]] := by
  by_cases hab : b = a
  · simp [hab]
  · exact h.continuousOn_derivWithin (uniqueDiffOn_Icc (by simp [hab])) hn

section Analysis.Calculus.IteratedDeriv

theorem ContDiffOn.continuousOn_iteratedDerivWithin_uIcc
    {m : ℕ} (h : ContDiffOn ℝ n f [[a, b]])
    (hmn : m ≤ n) : ContinuousOn (iteratedDerivWithin m f [[a, b]]) [[a, b]] := by
  by_cases hab : b = a
  · simp [hab]
  · exact h.continuousOn_iteratedDerivWithin hmn (uniqueDiffOn_Icc (by simp [hab]))

variable {x : ℝ}

theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin_uIcc {m : ℕ}
    (h : ContDiffWithinAt ℝ n f [[a, b]] x) (hx : x ∈ [[a, b]]) (hmn : m < n) :
    DifferentiableWithinAt ℝ (iteratedDerivWithin m f [[a, b]]) [[a, b]] x := by
  by_cases hab : b = a
  · simp [hab]
  · refine h.differentiableWithinAt_iteratedDerivWithin hmn ?_
    rw [Set.insert_eq_of_mem hx]
    exact uniqueDiffOn_Icc (by simp [hab])

theorem ContDiffWithinAt.differentiableWithinAt_derivWithin_uIcc
    (h : ContDiffWithinAt ℝ n f [[a, b]] x) (hx : x ∈ [[a, b]]) (hmn : 1 < n) :
    DifferentiableWithinAt ℝ (derivWithin f [[a, b]]) [[a, b]] x := by
  convert h.differentiableWithinAt_iteratedDerivWithin_uIcc hx hmn
  ext
  exact iteratedDerivWithin_one.symm

end Analysis.Calculus.IteratedDeriv

end ContDiffOn

section Analysis.Calculus.IteratedDeriv.Defs

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

open scoped Topology
open Filter Asymptotics Set

theorem iteratedDerivWithin_two {x : 𝕜} :
    iteratedDerivWithin 2 f s x = derivWithin (derivWithin f s) s x := by
  rw [iteratedDerivWithin_succ]
  congr
  ext
  exact iteratedDerivWithin_one

end Analysis.Calculus.IteratedDeriv.Defs

section Analysis.Complex.RealDeriv

variable {s : Set ℝ} {z : ℝ}

open Complex in
theorem HasDerivWithinAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivWithinAt f u s z) :
    HasDerivWithinAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u s z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using
    ofRealCLM.hasDerivWithinAt.scomp z hf <| fun _ _ ↦ Set.mem_univ _

end Analysis.Complex.RealDeriv
