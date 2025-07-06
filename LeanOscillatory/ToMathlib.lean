import LeanOscillatory.Basic

namespace Complex

-- lemma ne_zero_of_im_pos {s : ℂ} (hs : 0 < s.im) : s ≠ 0 :=
--   fun h ↦ (zero_im ▸ h ▸ hs).false

lemma ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 :=
  fun h ↦ zero_im ▸ h ▸ hs <| by rfl

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


section Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace IntervalIntegrable

open MeasureTheory Set Filter Function

open scoped Topology Filter Interval

variable {𝕜 E : Type*} [NormedAddCommGroup E]

variable [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]

variable {f : ℝ → 𝕜} {a b : ℝ} {μ : Measure ℝ} [NoAtoms μ]
variable {g : ℝ → E}

theorem smul_continuousOn (hf : IntervalIntegrable f μ a b)
    (hg : ContinuousOn g [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff'] at hf ⊢
  apply hf.smul_continuousOn hg isCompact_uIcc

theorem continuousOn_smul (hg : IntervalIntegrable g μ a b)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => f x • g x) μ a b := by
  rw [intervalIntegrable_iff'] at hg ⊢
  apply hg.continuousOn_smul hf isCompact_uIcc

end IntervalIntegrable

end Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

section Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace intervalIntegral

section SMul

open MeasureTheory Set

open scoped Topology Interval

variable {a b : ℝ}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]

variable {u u' : ℝ → 𝕜}
variable {v v' : ℝ → E}

theorem integral_deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x • v x + u x • v' x = u b • v b - u a • v a := by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx ↦ (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

/-- **Integration by parts** (vector-valued). -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x := by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv


/-- **Integration by parts** (vector-valued).
Special case of `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a two-sided derivative in the interior of the interval. -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a one-sided derivative at the endpoints. -/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/-- **Integration by parts** (vector-valued). Special case of
`intervalIntegrable.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`
where the functions have a derivative also at the endpoints. -/
theorem integral_smul_deriv_eq_deriv_smul
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x) (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end SMul

end intervalIntegral

end Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
