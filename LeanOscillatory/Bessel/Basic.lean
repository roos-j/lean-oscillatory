module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic


public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric -- remove

/-!
# Bessel functions

In this file we define standard Bessel functions.

The basic definition is `uniformBessel`. We prefer this over defining `besselJ` directly
because it is an entire function avoiding branch cuts.

-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Complex Nat

namespace Complex

/-- Coefficient of `z ^ (2 * k)` in the power series defining `uniformBessel`.
Note that also at poles of `Gamma` (when `k + α + 1` is a negative integer) this has
the correct value of `0` by a convenient coincidence of junk values.
-/
def uniformBesselCoeff (α : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k / (4 ^ k * (k)! * Gamma (k + α + 1))

@[simp]
theorem uniformBesselCoeff_zero (α : ℂ) : uniformBesselCoeff α 0 = 1 / Gamma (α + 1) := by
  simp [uniformBesselCoeff]

-- /-- The uniform Bessel J function as an infinite series. The series converges unconditionally
-- for every value of `α` and `z`. -/
-- def uniformBessel (α : ℂ) (z : ℂ) : ℂ :=
--   ∑' k, uniformBesselJCoeff α (2 * k) * z ^ (2 * k)

-- /-- The standard Bessel function of the first kind $J_\alpha(z)$ using the principal branch
-- as in `Complex.cpow`.  -/
-- def besselJ (α : ℂ) (z : ℂ) : ℂ := (z / 2) ^ α * uniformBesselJ α z


-- /-- Uniform Bessel J function as a formal power series in the variable `w = z ^ 2` -/
-- def uniformBesselJSqFPowerSeries (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
--   .ofScalars ℂ <| uniformBesselJCoeff α

section Abstract

variable (A : Type*) [Ring A] [Algebra ℂ A] [TopologicalSpace A] [IsTopologicalRing A]

def uniformBesselSeries (α : ℂ) : FormalMultilinearSeries ℂ A A :=
  .ofScalars A fun n ↦ if Even n then uniformBesselCoeff α (n / 2) else 0


def uniformBesselSeries' (α : ℂ) : FormalMultilinearSeries ℂ A A :=
  .comp (.ofScalars A <| uniformBesselCoeff α) (.ofScalars A <| Pi.single 2 1)


def monomial (n : ℕ) : FormalMultilinearSeries ℂ A A :=
  .ofScalars A <| Pi.single n 1

#check FormalMultilinearSeries.ofScalarsSum

theorem monomial_sum_eq (n : ℕ) (z : A) : (monomial A n).sum z = z ^ n := by
  change FormalMultilinearSeries.ofScalarsSum (Pi.single n 1) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq, tsum_eq_single n]
  · simp
  · intro m hm
    simp [Pi.single_eq_of_ne hm]

#check FormalMultilinearSeries.ofScalars_comp_neg

variable {A : Type*} [Ring A] [Algebra ℂ A] [TopologicalSpace A] [IsTopologicalRing A]

theorem uniformBesselSeries_apply_even_eq (α : ℂ) (z : A) (k : ℕ) :
    (uniformBesselSeries A α (2 * k) <| fun _ ↦ z) = (uniformBesselCoeff α k) • z ^ (2 * k) := by
  simp [uniformBesselSeries, FormalMultilinearSeries.ofScalars_apply_eq]

theorem uniformBesselSeries_apply_odd_eq (α : ℂ) (z : A) (k : ℕ) :
    (uniformBesselSeries A α (2 * k + 1) <| fun _ ↦ z) = 0 := by
  simp [uniformBesselSeries]

theorem uniformBesselSeries_apply_eq (α : ℂ) (z : A) (n : ℕ) :
    (uniformBesselSeries A α n <| fun _ ↦ z) =
      (if Even n then uniformBesselCoeff α (n / 2)  • z ^ n else 0) := by
  simp [uniformBesselSeries, FormalMultilinearSeries.ofScalars_apply_eq]

#check NormedSpace.expSeries_sum_eq

theorem uniformBesselSeries_sum_eq (α : ℂ) (z : A) :
    (uniformBesselSeries A α).sum z = ∑' k, (uniformBesselCoeff α k) • z ^ (2 * k) := by
  sorry
  -- simp [FormalMultilinearSeries.sum]
  -- --support (fun n ↦ uniformBesselSeries A α n (fun _ ↦ z))
  -- simp_rw [uniformBesselSeries_apply_eq]
  -- rw [← tsum_subtype_eq_of_support_subset (s := Even)]
  -- ·
  -- · intro n hn
  --   simp at hn
  --   exact hn.1

  -- change FormalMultilinearSeries.ofScalarsSum
  --     (fun n ↦ if Even n then uniformBesselCoeff α (n / 2) else 0) z =
  --   ∑' k, (uniformBesselCoeff α k) • z ^ (2 * k)
  -- rw [FormalMultilinearSeries.ofScalars_sum_eq]
  -- let e : ℕ ≃ ↑{n : ℕ | Even n} := {
  --   toFun k := ⟨2 * k, even_iff_exists_two_mul.mpr ⟨k, rfl⟩⟩
  --   invFun n := n / 2
  --   left_inv k := Nat.mul_div_right k (by norm_num)
  --   right_inv n := by
  --     ext
  --     obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp n.2
  --     simp [hk]
  -- }
  -- rw [show (∑' n, (if Even n then uniformBesselCoeff α (n / 2) else 0) • z ^ n) =
  --     ∑' n, ({n : ℕ | Even n}.indicator
  --       (fun n ↦ uniformBesselCoeff α (n / 2) • z ^ n) n) by
  --   apply tsum_congr
  --   intro n
  --   by_cases h : Even n <;> simp [h, Set.indicator]]
  -- rw [← tsum_subtype {n : ℕ | Even n},
  --   ← e.tsum_eq
  --     (fun n : ↑{n : ℕ | Even n} ↦ uniformBesselCoeff α ((n : ℕ) / 2) • z ^ (n : ℕ))]
  -- apply tsum_congr
  -- intro k
  -- change uniformBesselCoeff α ((2 * k) / 2) • z ^ (2 * k) =
  --   uniformBesselCoeff α k • z ^ (2 * k)
  -- simp

-- theorem tsum_comp_le_tsum_of_inj {α : Type*} {β : Type*}
--   {f : α → ℝ}
--   (hn : ∀ (a : α), 0 ≤ f a) {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f


variable (f : ℕ → ℂ)

#check tsum_range f <| show Function.Injective (fun n ↦ 2 * n) from fun _ _ ↦ by grind

#check tsum_subtype

-- tsum_subtype.{u_1, u_2} {α : Type u_1} {β : Type u_2} [AddCommMonoid α] [TopologicalSpace α] (s : Set β) (f : β → α) :
--   ∑' (x : ↑s), f ↑x = ∑' (x : β), s.indicator f x



section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
-- variable [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem uniformBesselSeries_radius_eq_top (α : ℂ) :
    (uniformBesselSeries A α).radius = ⊤ := by
  sorry



end

end Abstract

variable {α : ℂ}

#check HasFPowerSeriesAt.comp

section Analytic

/- In this section we prove analyticity via the formal power series API -/


end Analytic

end Complex

end

end
