import Mathlib
open Set

-- def 2

inductive Color where
  | red | green | blue
  deriving Repr

inductive Shape where
  | square | circle | triangle
  deriving Repr

class Object where
  color : Color
  shape : Shape
  deriving Repr

variable (right_of left_of : Object -> Object -> Prop)

axiom position (a b : Object) : ¬((right_of a b) ∧ (left_of a b))

def Red (obj : Object) : Prop :=
obj.color = Color.red

def Green (obj : Object) : Prop :=
obj.color = Color.green

def Blue (obj : Object) : Prop :=
obj.color = Color.blue

def Square (obj : Object) : Prop :=
obj.shape = Shape.square

def Circle (obj : Object) : Prop :=
obj.shape = Shape.circle

def Triangle (obj : Object) : Prop :=
obj.shape = Shape.triangle

-- problem

theorem exercise12: ∃D : Set Object,
  (∀x ∈ D, Circle x → ¬Blue x) ∧
  (∃x ∈ D, Circle x) ∧ (∃x ∈ D, Blue x) ∧
  ∃a b c,((right_of a b) ∧
  (left_of a b ∨ Square c) ∧
  a ∈ D ∧ b ∈ D ∧ c ∈ D)
  :=
  have x : Object := { color := Color.red, shape := Shape.circle };  -- a red circle
  have y : Object := { color := Color.blue, shape := Shape.triangle };  -- a blue triangle
  have z := Object.mk Color.green Shape.square;  -- a green square
  have s : Set Object := {x,y,z};
  have a1 :x ∈ s := by 



  by
  -- use s


  exact ⟨ sorry
   , ⟨⟨x, ⟨sorry, sorry⟩ ⟩ , sorry⟩ ⟩

  -- split,
  -- {

  -- }




-- theorem exercise12: ∃D : Set Object,
--   (∀x ∈ D, Circle x → ¬Blue x) ∧
--   (∃x ∈ D, Circle x) ∧ (∃x ∈ D, Blue x) ∧
--   ∃a b c, ((right_of a b) ∧
--   (left_of a b ∨ Square c) ∧
--   a ∈ D ∧ b ∈ D ∧ c ∈ D)
--   :=
--   have a : Object := { color := Color.blue, shape := Shape.square }
--   have b : Object := { color := Color.red, shape := Shape.circle }
--   have c : Object := { color := Color.blue, shape := Shape.square }
--   have D := {a, b, c}
--   have h10 := right_of a b = true
--   by
--   apply Exists.intro D
--   apply And.intro
--   intro x h1 h2
