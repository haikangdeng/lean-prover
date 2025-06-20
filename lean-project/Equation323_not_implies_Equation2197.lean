import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation323 (G: Type _) [Magma G] := ∀ x y : G, x ◇ y = x ◇ (x ◇ y)

abbrev Equation2197 (G: Type _) [Magma G] := ∀ x y z : G, x = ((y ◇ z) ◇ z) ◇ (x ◇ z)

theorem Equation323_not_implies_Equation2197 : ∃ (G: Type) (_: Magma G), Equation323 G ∧ ¬ Equation2197 G := by
  use Bool
  use { op := fun a b => a }
  constructor
  · intro x y
    simp [Equation323]
  · intro h
    have h1 := h true true false
    have h2 := h true false true
    have h3 := h false true true
    have h4 := h true true true
    have h5 := h true false false
    have h6 := h false true false
    have h7 := h false false true
    have h8 := h false false false
    simp at h1 h2 h3 h4 h5 h6 h7 h8
    <;> simp_all