import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation2476 (G: Type _) [Magma G] := ∀ x y z : G, x = (x ◇ ((y ◇ z) ◇ x)) ◇ x

abbrev Equation2780 (G: Type _) [Magma G] := ∀ x y z : G, x = ((y ◇ z) ◇ (x ◇ z)) ◇ z

theorem Equation2476_not_implies_Equation2780 : ∃ (G: Type) (_: Magma G), Equation2476 G ∧ ¬ Equation2780 G := by
  have h_main : ∃ (G: Type) (_: Magma G), Equation2476 G ∧ ¬ Equation2780 G := by
    use Bool
    use {
      op := fun a b => a
    }
    constructor
    · -- Prove Equation2476
      intro x y z
      simp [Magma.op]
      <;>
      (try cases x <;> cases y <;> cases z <;> simp) <;>
      (try aesop) <;>
      (try simp_all) <;>
      (try aesop)
    · -- Prove ¬ Equation2780
      intro h
      have h₁ := h true true false
      simp [Magma.op] at h₁
      <;>
      (try cases h₁ <;> simp_all) <;>
      (try aesop)
      <;>
      (try contradiction)
      <;>
      (try simp_all)
      <;>
      (try aesop)
  exact h_main