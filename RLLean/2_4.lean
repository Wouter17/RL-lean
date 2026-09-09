-- -- variable (α : Type)

-- -- variable (Circle : α → Prop)
-- -- variable (Blue : α → Prop)
-- -- variable (Above : α → Prop)
-- -- variable (Below : α → Prop)

-- -- def isBlue (a : α) : Prop := Blue a
-- def Blue {α : Type} {b : α → Prop} (a : α) : Prop := b a
-- def Circle {α : Type} {b : α → Prop} (a : α) : Prop := b a
-- def Square {α : Type} {b : α → Prop} (a : α) : Prop := b a
-- def RightOf {α : Type} {x : α → α → Prop} (a b : α) : Prop := x a b
-- def LeftOf {α : Type} {x : α → α → Prop} (a b : α) : Prop := x a b

-- -- def Circle {U : Type} (a: U → Prop) : U → Prop := a
-- -- def Blue {U : Type} (a: U → Prop) : U → Prop := a
-- -- def Above {U : Type} (a: U → Prop) : U → Prop := a
-- -- def Below {U : Type} (a: U → Prop) : U → Prop := a

-- -- 12
-- example: ∃a b c,
-- ((∀x, Circle x → ¬(Blue x))
-- ∧ (∃x, Circle x) ∧ (∃x, Blue x)
-- ∧ (RightOf a b) ∧ ((LeftOf a b) ∨ (Square c)))
import Mathlib
open Set

variable (α : Type)
variable (blue circle square: α -> Prop)
variable (right_of left_of : α -> α -> Prop)
variable (a b c : α)


variable (h_blue_a : blue a)
variable (h_ro_a_b : right_of a b)
variable (h_circle_b : circle b)
variable (h_not_blue_b : ¬blue b)
variable (h_square_c : square c)

variable (h_not_circle_a : ¬circle a)
variable (h_not_circle_c : ¬circle c)

theorem exercise12: ∃D : Set α,
  (∀x ∈ D, circle x → ¬blue x) ∧
  (∃x ∈ D, circle x) ∧ (∃x ∈ D, blue x) ∧
  (right_of a b) ∧
  (left_of a b ∨ square c) ∧
  a ∈ D ∧ b ∈ D ∧ c ∈ D
  :=
  -- have h : blue a := h_blue_a
  -- have h2: right_of a b := h_ro_a_b
  -- have h3: circle b := h_circle_b
  -- have h4: square c := h_square_c
  ⟨{a,b,c}, ⟨fun h1 h2 =>
  by
  cases h2 with
  | inl ha => rw [ha]; intro _; contradiction
  | inr hbc => cases hbc with
    | inl hb => rw [hb]; intro _; exact h_not_blue_b
    | inr hc => rw [hc]; intro _; contradiction
  , ⟨b, ⟨by simp, h_circle_b⟩⟩ ,⟨a, ⟨by simp, h_blue_a⟩⟩, h_ro_a_b, Or.inr h_square_c, by simp⟩⟩
