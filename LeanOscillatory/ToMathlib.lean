import LeanOscillatory.Basic

namespace Complex

lemma ne_zero_of_im_pos {s : ℂ} (hs : 0 < s.im) : s ≠ 0 :=
  fun h ↦ (zero_im ▸ h ▸ hs).false

end Complex
