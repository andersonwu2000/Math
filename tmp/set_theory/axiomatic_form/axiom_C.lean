import MATH.set_theory.Basic
open Classical

axiom complement : ∀ A, ∃ B, ∀ x, (x ∈ B) ↔ (¬ x ∈ A)
notation A "ᶜ" => choose (complement A)
