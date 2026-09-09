open Classical

-- These theorems are the laws as introduced in the book so you
-- don't need to worry about how they are proven
theorem not_or_imp (p q : Prop) : (¬p ∨ q) = (p → q) :=
  calc
  (¬p ∨ q) = (¬¬p → q) := by rw [or_iff_not_imp_left]
  _ = (p → q) := by rw [not_not]
