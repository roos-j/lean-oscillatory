module

-- public import Mathlib.Topology.Connected.Basic
-- public import Mathlib.Algebra.Order.Group.Abs

public import Mathlib

@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α] {s : Set α}

variable [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {f : α → β} {b : β}

variable [Group β] [MulLeftMono β]


/-- On a preconnected set, if a continuous map has multiplicative absolute value bounded
below by `L > 1`, then it is either `≥ L` everywhere or its inverse is `≥ L` everywhere. -/
@[to_additive
/-- On a preconnected set, if a continuous map has absolute value bounded below by `L > 0`,
then it is either `≥ L` everywhere or its negative is `≥ L` everywhere. -/]
theorem IsPreconnected.forall_le_or_forall_le_of_forall_le_mabs {s : Set α}
    (hs : IsPreconnected s) {L : β} (hL : 1 < L) {f: α → β}
    (hfcont: ContinuousOn f s) (hf : ∀ x ∈ s, L ≤ |f x|ₘ) :
    (∀ x ∈ s, L ≤ f x) ∨ (∀ x ∈ s, L ≤ (f x)⁻¹) := by
  obtain (h | h) := hs.mapsTo_Ioi_or_Iio (b := 1) hfcont (fun x hx h ↦
    not_le_of_gt hL <| by simpa [mabs_one, h] using hf x hx)
  · grind [MapsTo, mabs_of_one_lt]
  · grind [MapsTo, mabs_of_lt_one]

-- #find_home! IsPreconnected.forall_le_or_forall_le_of_forall_le_mabs

end
