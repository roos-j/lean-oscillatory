module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Bessel functions

In this file we define standard Bessel functions.

The basic definition is `uniformBesselJ`. We prefer this over defining `besselJ` directly
because it is an entire function avoiding branch cuts.

-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Complex Nat

namespace Complex

/-- Coefficient of `z ^ (2 * k)` in the power series defining `uniformBesselJ`.
Note that also at poles of `Gamma` (when `k + α + 1` is a negative integer) this has
the correct value of `0` by a convenient coincidence of junk values.
-/
def uniformBesselJCoeff (α : ℂ) (k : ℕ) : ℂ :=
  (-1) ^ k / (4 ^ k * (k)! * Gamma (k + α + 1))

/-- The uniform Bessel J function as an infinite series. The series converges unconditionally
for every value of `α` and `z`. -/
def uniformBesselJ (α : ℂ) (z : ℂ) : ℂ :=
  ∑' k, uniformBesselJCoeff α (2 * k) * z ^ (2 * k)

/-- The standard Bessel function of the first kind $J_\alpha(z)$ using the principal branch
as in `Complex.cpow`.  -/
def besselJ (α : ℂ) (z : ℂ) : ℂ := (z / 2) ^ α * uniformBesselJ α z

section Analytic
/- In this section we prove analyticity via the formal power series API -/

-- /-- Uniform Bessel J function as a formal power series in the variable `w = z ^ 2` -/
-- def uniformBesselJSqFPowerSeries (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
--   .ofScalars ℂ <| uniformBesselJCoeff α

/-- Uniform Bessel J function as a formal power series -/
def uniformBesselJFPowerSeries (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .comp (.ofScalars ℂ <| uniformBesselJCoeff α) (.ofScalars ℂ <| Pi.single 2 1)

theorem uniformBesselJFPowerSeries_radius_eq_top (α : ℂ) :
    (uniformBesselJFPowerSeries α).radius = ⊤ := by
  sorry



variable {α : ℂ}

#check HasFPowerSeriesAt.comp
#check (uniformBesselJSqFPowerSeries α).radius

end Analytic

end Complex

end

end
