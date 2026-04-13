-- filepath: /Users/javiermaassmartinez/Documents/PhDStuff/Code/lean4ml/lean4ml/Example.lean
/-- A tiny identity definition used in lint examples. -/
def test_def {α : Type} (a : α) : α := a

/-- Equality is symmetric. -/
theorem test_a {α : Type} {a b : α} (h : a = b) : b = a := by
  simpa using h.symm

/-- Equality is transitive. -/
theorem test_b {α : Type} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c := by
  exact h₁.trans h₂
