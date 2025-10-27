import LeanOscillatory.Basic

-- namespace Complex

-- -- lemma ne_zero_of_im_pos {s : ℂ} (hs : 0 < s.im) : s ≠ 0 :=
-- --   fun h ↦ (zero_im ▸ h ▸ hs).false

-- lemma ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 :=
--   fun h ↦ zero_im ▸ h ▸ hs <| by rfl

-- end Complex

section ContDiffOn

variable {a b : ℝ}
variable {n : WithTop ℕ∞}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : ℝ → F}

open Real Interval

-- section Mathlib.Analysis.Calculus.Deriv.Basic

-- theorem HasDerivWithinAt.derivWithin_uIcc {f' : F} {x : ℝ} (hx : x ∈ [[a, b]])
--     (h : HasDerivWithinAt f f' [[a, b]] x) (hab : b ≠ a) : _root_.derivWithin f [[a, b]] x = f' := by
--   apply h.derivWithin
--   apply uniqueDiffOn_Icc (by simpa)
--   exact hx

-- end Mathlib.Analysis.Calculus.Deriv.Basic

section Mathlib.Analysis.Calculus.ContDiff.Basic

theorem ContDiffOn.continuousOn_derivWithin_uIcc (h : ContDiffOn ℝ n f [[a, b]])
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f [[a, b]]) [[a, b]] := by
  by_cases hab : b = a
  · simp [hab]
  · exact h.continuousOn_derivWithin (uniqueDiffOn_Icc (by simp [hab])) hn

end Mathlib.Analysis.Calculus.ContDiff.Basic

section Mathlib.Analysis.Calculus.IteratedDeriv

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
  ext : 2
  exact iteratedDerivWithin_one.symm

end Mathlib.Analysis.Calculus.IteratedDeriv

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

-- section Mathlib.Data.Real.Sign

-- namespace Real

-- theorem abs_sign_le {r : ℝ} : |r.sign| ≤ 1 := by
--   rcases sign_apply_eq r with h|h|h
--     <;> { rw [h]; simp }

-- theorem abs_sign_eq {r : ℝ} (hr : r ≠ 0) : |r.sign| = 1 := by
--   rcases sign_apply_eq_of_ne_zero r hr with h|h
--     <;> { rw [h]; simp }

-- end Real

-- end Mathlib.Data.Real.Sign

section Mathlib.Topology.Order.OrderClosed

variable {α : Type*}
variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]

open Set

theorem uIoo_mem_nhds {a b x : α} (hx : x ∈ uIoo a b) : uIoo a b ∈ nhds x := by
  rcases lt_trichotomy a b with h | h | h
  · exact uIoo_of_lt h ▸ Ioo_mem_nhds (uIoo_of_lt h ▸ hx).1 (uIoo_of_lt h ▸ hx).2
  · exact False.elim <| notMem_empty x (uIoo_self (a := b) ▸ h ▸ hx)
  · exact uIoo_of_gt h ▸ Ioo_mem_nhds (uIoo_of_gt h ▸ hx).1 (uIoo_of_gt h ▸ hx).2

end Mathlib.Topology.Order.OrderClosed
