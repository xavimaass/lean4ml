def test_def {α : Type} : α → α := (fun a => a)

theorem test_a {α : Type} (a : α) : a = a := by
  rfl

theorem test_b {α : Type} (a : α) : a = a := by
  rfl
