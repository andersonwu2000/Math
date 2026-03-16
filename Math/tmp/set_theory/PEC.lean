


class PC where
  Univ : Type u
  Mem : Univ → Univ → Prop
  power : ∀ A, ∃ P, ∀ B, Mem B P ↔ (∀ x, Mem x B → Mem x A)
  compl : ∀ A, ∃ B, ∀ x, Mem x A ↔ ¬ Mem x B
