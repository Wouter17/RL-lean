import «RLLean».additional_laws

open Classical

-- Exercises

-- 2a tautology
example (p q : Prop) : (p ∧ (p → q)) → q := by
  intro h
  have h2 := h.left
  exact h.right h2

-- 2b tautology
example (p q : Prop) : ((p → q) ∧ (q → r)) → (p → r) := by
  intro h h1
  have ⟨h2, h3⟩ := h
  exact h3 (h2 h1)

-- 2c contradiction
example (p : Prop) : (p ∧ ¬p) ↔ False :=
  ⟨λ h => absurd h.left h.right, λ h => by contradiction⟩

-- 2d contingency
-- Show there exists some values of p,q for which this is true
example : ∃p q, (p ∨ q) → p ∧ q :=
  -- Here we show lean how to construct the type
  have h : (True ∨ True) → (True ∧ True) := fun _ => ⟨trivial, trivial⟩
  ⟨True, True, h⟩

-- Show there exists some values of p,q for which this is false
example : ∃p q, ¬((p ∨ q) → p ∧ q) :=
-- Here we just let lean simplify the expressions to find if it is true
  have h : ¬((True ∨ False) → (True ∧ False)) := by simp
  ⟨True, False, h⟩

-- 2e tautology
-- proving this is actually quite hard, so we use the built-in proof
example (p : Prop) : p ∨ ¬p := by apply em

-- 2f tautology
example (p q : Prop) : (p ∧ q) → (p ∨ q) := by
  intro h
  -- We only need to state that if p is true, the or is also true,
  -- since p ∨ q only needs p to be true, to be true
  apply Or.inl h.left


-- 3a
example (p q : Prop) : ((p → q) ∧ (q → p)) = (p ↔ q) := by
  rw [←iff_iff_implies_and_implies p q]

-- 3b
example (p q : Prop) : (¬p ↔ ¬q) = (p ↔ q) :=
  calc
  (¬p ↔ ¬q) = ((¬p → ¬q) ∧ (¬q → ¬p)) := by rw [iff_iff_implies_and_implies]
  _ = ((q → p) ∧ (p → q)) := by rw [Decidable.not_imp_not, Decidable.not_imp_not]
  _ = (q ↔ p) := by rw [iff_iff_implies_and_implies]
  _ = (p ↔ q) := by rw [Iff.comm]

-- 3c
example (p q : Prop) : ((p → q) ∧ (¬p → ¬q)) = (p ↔ q) :=
  calc
  ((p → q) ∧ (¬p → ¬q)) = ((p → q) ∧ (q → p)) := by rw [Decidable.not_imp_not]
  _ = (p ↔ q) := by rw [iff_iff_implies_and_implies]

-- 3d
example (p q : Prop) : (¬(xor p q)) = (p ↔ q) :=
  calc
  (¬(xor p q)) = (¬(¬(p ↔ q))) := by simp
  _ = (p ↔ q) := by rw [not_not]

-- 4
-- Counterexaple: p = true, q,r = false
example : ∃ p q r, (p → q) → r ≠ p → (q → r) :=
  have h : (True → False) → False ≠ True → (False → False) := by simp
  ⟨True, False, False, h⟩

-- 9

-- First we will define nor
def nor (a b : Prop) : Prop :=
  ¬(a ∨ b)

-- We make the the first proof a theorem, because we will use it later
theorem nor_neg (p : Prop) : nor p p = ¬p :=
  calc
  nor p p = ¬(p ∨ p) := rfl -- rfl stands for reflection
                            -- It is a way to show both are exactly the same
  _ = ¬p := by rw [or_self] -- Idempotent rule

-- We will also use this later to prove the bi-implication
theorem nor_and (p q : Prop) : nor (nor p p) (nor q q) = (p ∧ q) :=
  calc
  nor (nor p p) (nor q q) = nor (¬p) (¬q) := by repeat rw [nor_neg]
  _ = ¬(¬p ∨ ¬q) := rfl
  _ = (¬¬p ∧ ¬¬q) := by rw [not_or]
  _ = (p ∧ q) := by repeat rw [not_not]

-- We also use this to prove the implication
theorem nor_or (p q : Prop) : nor (nor p q) (nor p q) = (p ∨ q) :=
  calc
  nor (nor p q) (nor p q) = ¬(nor p q) := by rw [nor_neg]
  _ = ¬(¬(p ∨ q)) := rfl
  _ = (p ∨ q) := by rw [not_not]

-- We will also use this later to prove the bi-implication
theorem nor_imp (p q : Prop) : nor (nor (nor p p) q) (nor (nor p p) q) = (p → q) :=
  calc
  nor (nor (nor p p) q) (nor (nor p p) q) = nor (nor (¬p) q) (nor (¬p) q) := by repeat rw [nor_neg]
  _ = (¬p ∨ q) := by rw [nor_or]
  _ = (p → q) := by rw [not_or_imp]

theorem nor_iff (p q : Prop) :
nor ( --This is the and
  nor
  (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
  (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
  )
  (
  nor
  (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
  (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
) = (p ↔ q) :=
  calc
  _ = (nor (
  nor
  (p → q) --We've now repleced the implication with the actual implication
  (p → q)
  )
  (
  nor
  (q → p)
  (q → p)
  )) := by repeat rw [nor_imp p q, nor_imp q p]
  _ = ((p → q) ∧ (q → p)) := by rw [nor_and] -- We also replace the and
  _ = (p ↔ q) := by rw [iff_iff_implies_and_implies]

--Finally we can define xor to be the negation of the previous theorem
example (p q : Prop) :
nor --This is the negation
  (nor ( --This is the and
    nor
    (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
    (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
    )
    (
    nor
    (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
    (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
  ))
  (nor ( --This is the and
    nor
    (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
    (nor (nor (nor p p) q) (nor (nor p p) q)) --This is p → q
    )
    (
    nor
    (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
    (nor (nor (nor q q) p) (nor (nor q q) p)) --This is q → p
    )
  )
= (xor p q) :=
  calc
  _ = nor (p ↔ q) (p ↔ q) := by rw [nor_iff]
  _ = ¬(p ↔ q) := by rw [nor_neg]
  _ = (xor p q) := by simp

-- 10
example (p q : Prop) : (¬(¬p ∨ ¬q)) = (p ∧ q) :=
  calc
  (¬(¬p ∨ ¬q)) = ¬¬(p ∧ q) := by rw [not_and_iff_or_not_not]
  _ = (p ∧ q) := by rw [not_not]

-- note that this is the definition we usually use to rewrite into p → q
-- though we will now show a proof that uses p ∨ q = ¬p → q instead
example (p q : Prop) : (¬p ∨ q) = (p → q) :=
  calc
  (¬p ∨ q) = (¬¬p → q) := by rw [or_iff_not_imp_left]
  _ = (p → q) := by rw [not_not]

-- We combine both the and and implication definitions
example (p q : Prop) : (¬(¬(¬p ∨ q) ∨ ¬(¬q ∨ p))) = (p ↔ q) :=
  calc
  _ = ¬¬((¬p ∨ q) ∧ (¬q ∨ p)) := by rw [not_and_iff_or_not_not]
  _ = ((¬p ∨ q) ∧ (¬q ∨ p)) := by rw [not_not]
  _ = ((p → q) ∧ (q → p)) := by repeat rw [not_or_imp]
  _ = (p ↔ q) := by rw [iff_iff_implies_and_implies]
  -- note that we could also have done this by rewriting with the previous definitions
  -- as shown with theorems in exercise 9

-- 13
-- Let y stand for "all lemons are yellow"
-- And u for "unicorns exist"

-- The following code then:
-- States y is a propsitional variable: (y : Prop)
-- States u is something in a universe (u : Sort v), note that we could have also chosen it to be a property, since that is also somethign in a universe
-- States we have a proof called a for y: (a : y)
-- States we have a proof called b for ¬y: (b : ¬y)
-- States that we want to prove u

-- Now we use absurd with the two assumptions/proofs (a and b). This shows lean that this function/example can never be reached,
-- As the assumptions already form a contradiction, thus we can conclude anything.
-- This statisfies the proof.
example (y : Prop) (u : Sort v) (a : y) (b : ¬y) : u :=
  absurd a b
