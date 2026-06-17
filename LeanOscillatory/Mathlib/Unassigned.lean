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


@[to_additive]
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
