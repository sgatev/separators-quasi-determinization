import Mathlib

/-!
# Alphabets, words, and languages (thesis §2.3)

Words over `Σ` are `List α`; languages are Mathlib's `Language α`.
-/

namespace Sqdfsa

variable {α : Type*}

/-- The left quotient `u⁻¹w`. The thesis defines it only when `u` is a prefix of `w`; we
make it total by dropping `|u|` letters, which agrees with the thesis on that domain. -/
def lquot (u w : List α) : List α := w.drop u.length

theorem lquot_append (u w : List α) : lquot u (u ++ w) = w := by
  simp [lquot]

/-- Proposition `left_word_factor`: `v⁻¹(u⁻¹w) = (uv)⁻¹w`. -/
theorem left_word_factor (u v w : List α) : lquot v (lquot u w) = lquot (u ++ v) w := by
  simp [lquot, List.drop_drop]

end Sqdfsa
