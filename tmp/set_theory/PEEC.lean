import MATH.set_theory.axiom_P
import MATH.set_theory.EEC
open Classical

theorem double_complement (A : univ) : Aᶜᶜ = A := by
  simp [extensionality]
  intro x
  apply Iff.intro
  . intro h
    have h₀ := choose_spec (complement (Aᶜ))
    have h₁ : ¬ x ∈ Aᶜ := by simp_all
    have h₂ := choose_spec (complement A)
    simp_all
  . intro h
    have h₀ := choose_spec (complement A)
    have h₁ : ¬ x ∈ Aᶜ := by simp_all
    have h₂ := choose_spec (complement (Aᶜ))
    simp_all

theorem fixed_power : ∅ᶜ = P ∅ᶜ := by
  have h : ∀ x, (x ∈ ∅ᶜ) ↔ (x ∈ P ∅ᶜ) := by
    intro x
    have h₁ : x ∈ ∅ᶜ := by simp [universal_set]
    have h₂ : x ⊆ ∅ᶜ := by
      intro y h
      simp [universal_set]
    have h₃ : x ∈ P ∅ᶜ := by
      have h := choose_spec (power (∅ᶜ))
      simp_all
    simp_all
  have h₀ := extensionality (∅ᶜ) (P ∅ᶜ)
  exact h₀.mpr h
