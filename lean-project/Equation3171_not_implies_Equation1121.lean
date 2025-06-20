import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation3171 (G: Type _) [Magma G] := ∀ w x y z : G, x = (((y ◇ y) ◇ z) ◇ w) ◇ x

abbrev Equation1121 (G: Type _) [Magma G] := ∀ x y z : G, x = y ◇ ((y ◇ (y ◇ x)) ◇ z)

theorem Equation3171_not_implies_Equation1121 : ∃ (G: Type) (_: Magma G), Equation3171 G ∧ ¬ Equation1121 G := by
  use Bool
  use { op := fun a b => false }
  constructor
  · intro w x y z
    simp [Magma.op]
  intro h
  have h1 := h true false false
  have h2 := h true true false
  have h3 := h false true true
  have h4 := h true true true
  have h5 := h false false true
  have h6 := h true false true
  have h7 := h false true false
  have h8 := h true true false
  have h9 := h false false false
  have h10 := h true false false
  simp [Magma.op] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  <;> simp_all