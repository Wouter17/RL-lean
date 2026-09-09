import «RLLean».additional_laws

open Classical

-- 2a
example : ∃p q, ¬(p ∧ q) ≠ ((¬p) ∧ ¬(q)) :=
  have h : ¬(True ∧ False) ≠ ((¬True) ∧ (¬False)) := by simp
  ⟨True, False, h⟩

-- 2b
example : ∃p q, ¬(p ∨ q) ≠ ((¬p) ∨ (¬q)) :=
  have h : ¬(True ∨ False) ≠ ((¬True) ∨ (¬False)) := by simp
  ⟨True, False, h⟩


-- 3a
example : ∃p q, (¬p → ¬q) ≠ ¬(p → q) :=
  have h : (¬True → ¬True) ≠ ¬(True → True) := by simp
  ⟨True, True, h⟩

-- 3b
example : ∃p q, (¬p → q) ≠ ¬(p → q) :=
  have h : (¬False → True) ≠ ¬(False → True) := by simp
  ⟨False, True, h⟩

-- 3c
example : ∃p q, (p → ¬q) ≠ ¬(p → q) :=
  have h : (False → ¬False) ≠ ¬(False → False) := by simp
  ⟨False, False, h⟩

-- 4
example : ∃p q, ¬(p ↔ q) ≠ (¬p ↔ ¬q) :=
  have h: ¬(True ↔ True) ≠ (¬True ↔ ¬True) := by simp
  ⟨True, True, h⟩

-- 6
example (p q r : Prop) : ((p ∨ q) ∧ r) = ((p ∧ r) ∨ (q ∧ r)) :=
  calc
  ((p ∨ q) ∧ r) = (r ∧ (p ∨ q)) := by rw [And.comm]
  _ = ((r ∧ p) ∨ (r ∧ q)) := by rw [and_or_left]
  _ = ((p ∧ r) ∨ (r ∧ q)) := by rw [And.comm]
  _ = ((p ∧ r) ∨ (q ∧ r)) := by rw [@And.comm r q]

example (p q r : Prop) : ((p ∧ q) ∨ r) = ((p ∨ r) ∧ (q ∨ r)) :=
  calc
  ((p ∧ q) ∨ r) = (r ∨ (p ∧ q)):= by rw [Or.comm]
  _ = ((r ∨ p) ∧ (r ∨ q)) := by rw [or_and_left]
  _ = ((p ∨ r) ∧ (r ∨ q)) := by rw [Or.comm]
  _ = ((p ∨ r) ∧ (q ∨ r)) := by rw [@Or.comm q r] -- We need to explicitly provide the arguments
                                                  -- as otherwise p and r will be switched back

-- 7
example (p q r s : Prop) : (p ∧ (q ∨ r ∨ s)) = ((p ∧ q) ∨ (p ∧ r) ∨ (p ∧ s)) :=
  calc
  (p ∧ (q ∨ r ∨ s)) = (p ∧ (q ∨ (r ∨ s))) := rfl
  _ = ((p ∧ q) ∨ (p ∧ (r ∨ s))) := by rw [and_or_left]
  _ = ((p ∧ q) ∨ ((p ∧ r) ∨ (p ∧ s))) := by rw [and_or_left]
  -- note that we could put a step here to remove the brackets, but Lean already sees these are
  -- not needed anyway

-- 9a
example (p q : Prop) : (p ∧ (q ∧ p)) = (p ∧ q) :=
  calc
  (p ∧ (q ∧ p)) = (p ∧ q ∧ p) := rfl
  _ = (q ∧ p ∧ p) := by rw [and_rotate]
  -- note that ∧ binds from r to l so this is the same as
  -- (q ∧ (p ∧ p))
  _ = (q ∧ p) := by rw [and_self] -- Idempotent law
  _ = (p ∧ q) := by rw [And.comm]

-- 9b
example (p q : Prop) : (¬p → q) = (p ∨ q) :=
  calc
  (¬p → q) = (¬¬p ∨ q) := by rw [not_or_imp]
  _ = (p ∨ q) := by rw [not_not]

-- 9c
example (p q : Prop) : ((p ∨ q) ∧ ¬q) = (p ∧ ¬q) :=
  calc
  ((p ∨ q) ∧ ¬q) = ((p ∧ ¬q) ∨ (q ∧ ¬q)) := by rw [or_and_right]
  _ = ((p ∧ ¬q) ∨ False) := by rw [and_not_self_iff]
  _ = (p ∧ ¬q) := by rw [or_false] -- Identity law

-- 9d
example (p q : Prop) : (p → (q → r)) = ((p ∧ q) → r) :=
  calc
  (p → (q → r)) = (¬p ∨ (q → r)) := by rw [not_or_imp]
  _ = (¬p ∨ ¬q ∨ r) := by rw [@not_or_imp q r]
  _ = (r ∨ ¬p ∨ ¬q) := by rw [or_rotate, or_rotate] -- since rotate is a proof for rotating left, we need to rotate twice
  _ = ((¬p ∨ ¬q) ∨ r) := by rw [Or.comm]
  _ = (¬(p ∧ q) ∨ r) := by rw [not_and_iff_or_not_not]
  _ = ((p ∧ q) → r) := by rw [not_or_imp]

-- 9e
example (p q r : Prop) : ((p → r) ∧ (q → r)) = ((p ∨ q) → r) :=
  calc
  ((p → r) ∧ (q → r)) = ((¬p ∨ r) ∧ (¬q ∨ r)) := by repeat rw [not_or_imp]
  _ = ((¬p ∧ ¬q) ∨ r) := by rw [and_or_right]
  _ = (¬(p ∨ q) ∨ r) := by rw [not_or]
  _ = ((p ∨ q) → r) := by rw [not_or_imp]

-- 9f
example (p q : Prop) : (p → (p ∧ q)) = (p → q) :=
  calc
  (p → (p ∧ q)) = (¬p ∨ (p ∧ q)) := by rw [not_or_imp]
  _ = ((¬p ∨ p) ∧ (¬p ∨ q)) := by rw [or_and_left]
  -- Though it is already obvious here that (¬p ∨ p) is True
  -- We need to do some shenanigains to also convince lean
  _ = ((¬p ∨ ¬¬p) ∧ (¬p ∨ q)) := by rw [not_not]
  _ = (¬(p ∧ ¬p) ∧ (¬p ∨ q)) := by rw [not_and_iff_or_not_not]
  _ = (¬False ∧ (¬p ∨ q)) := by rw [and_not_self_iff]
    -- Normal proof continues
  _ = (True ∧ (¬p ∨ q)) := by rw [not_false_iff]
  _ = (¬p ∨ q) := by rw [true_and]
  _ = (p → q) := by rw [not_or_imp]
