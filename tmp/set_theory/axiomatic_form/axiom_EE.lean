import MATH.set_theory.Basic
open Classical

axiom empty : ∃ O, ∀ x, ¬ x ∈ O
notation "∅" => choose empty

def non_empty (A : univ) : Prop :=
  ∃ a, a ∈ A

theorem vacuous_truth (φ : univ → Prop) :
    ∀ x, (x ∈ ∅) → φ x := by
  intros x h
  have h := choose_spec empty x
  simp_all

theorem empty_fun_mono (emp : f : ∅ ⟶ A) : (f : ∅ ↣ A) := by
  apply And.intro
  . exact emp
  . intros a b c
    intro ⟨h₀, h₁, h₂, h₃, h₄⟩
    simp_all [vacuous_truth]

axiom extensionality : ∀ A B, A = B ↔ ∀ x, (x ∈ A) ↔ (x ∈ B)

theorem empty_unique : non_empty A ↔ A ≠ ∅ := by
  simp_all [non_empty]
  apply Iff.intro
  . intro ⟨a, h⟩
    exact fun h₀ => by
      have h₁ : ¬ a ∈ ∅ := choose_spec empty a
      simp_all
  . intro h
    simp_all [extensionality]
    let ⟨a, h₀⟩ := h
    have h₁ : ¬ a ∈ ∅ := choose_spec empty a
    exact ⟨a, by simp_all⟩
