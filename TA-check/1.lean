import «RLLean».additional_laws

open Classical

-- 2b valid
example (p q : Prop) : (p → q) → ¬q → ¬p := by
intro h1 h2 h3
have h4 := h1 h3
contradiction

-- 2c counter example
example: ∃pc pw pe, ((pc → pw) ∧ (pc → pe) ∧ (pw ∧ pe)) → ¬pc :=
  have h : ((False → True) ∧ (False → True) ∧ (True ∧ True)) → ¬False := by simp
  ⟨False, True, True, h⟩

example (h f p : Prop) : ¬(h ∧ ¬f) → (h ∨ ¬p) → ¬f → ¬p := by
  intro h1 h2 h3
  rw [not_and_iff_or_not_not, not_not] at h1
  apply Or.elim h1
  intro h4
  apply Or.resolve_left h2
  exact h4
  intro h4
  contradiction

-- 2g valid
example (p q : Prop) : (p → q) → ¬(p ∧ ¬q) := by
  intro h1
  rw [not_and]
  rw [not_not]
  exact h1

--3a
example (p q : Prop) : (q ∨ (p → q)) = ¬(¬q ∧ (p ∧ ¬q)) :=
  calc
  (q ∨ (p → q)) = (q ∨ (p → ¬¬q)) := by rw [not_not]
  _ = (q ∨ ¬(p ∧ ¬q)) := by rw [not_and]
  _ = (¬¬q ∨ ¬(p ∧ ¬q)) := by rw [not_not]
  _ = ¬(¬q ∧ (p ∧ ¬q)) := by rw[←not_and_iff_or_not_not]

--3b
example: ∃p q r s, ((¬s ↔ p) ∧ (r → q)) ≠ ((¬p ∧ ¬r ∧ ¬s) ∨ (s ∧ ¬q)) :=
  have h : ((¬False ↔ False) ∧ (False → False)) ≠ ((¬False ∧ ¬False ∧ ¬False) ∨ (False ∧ ¬False)) := by simp
  ⟨False, False, False, False, h⟩

--3c
example: ∃p q r, ((p ∨ q) → (r ∨ q)) ≠ ((¬r ∨ ¬q) → (¬p ∨ ¬q)) :=
  have h : ((True ∨ False) → (False ∨ False)) ≠ ((¬False ∨ ¬False) → (¬True ∨ ¬False)) := by simp
  ⟨True, False, False, h⟩

--3d
example (p q r : Prop) : (p ∨ (q ∧ r)) = (¬p → (q ∧ r)) :=
  by rw [←not_or_imp, not_not]


-- 6c
example (p q : Prop) : (¬p → q) = (p ∨ q) :=
  by rw [←not_or_imp, not_not]

example (p q : Prop) : (¬(p → ¬q)) = (p ∧ q) :=
  calc
  _ = (¬(¬p ∨ ¬q)) := by rw [←not_or_imp]
  _ = (¬¬p ∧ ¬¬q) := by rw [not_or]
  _ = (p ∧ q) := by repeat rw [not_not]

example (p q : Prop) : (¬((p → q) → ¬(q → p))) = (p ↔ q) :=
  calc
  _ = (¬(¬(p → q) ∨ ¬(q → p))) := by rw [not_or_imp]
  _ = (((p → q) ∧ (q → p))) := by rw [not_or, not_not, not_not]
  _ = (p ↔ q) := by rw [iff_iff_implies_and_implies]
