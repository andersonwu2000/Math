import MATH.set_theory.Basic
open Classical

axiom power : ∀ A, ∃ P, ∀ B, (B ∈ P) ↔ (B ⊆ A)
notation "P" A => choose (power A)

theorem subs_in_power (A B : univ) : (B ⊆ A) → (B ∈ P A) := by
  intro h₁
  let h₂ := choose_spec (power A)
  exact (h₂ B).mpr h₁

theorem Cantor (onto : f : A ↠ P A) :
  ¬ is_set (fun x => ∃ d : x ∈ A, ¬ x ∈ eval onto.left d) :=
  byContradiction (fun p => by
    have p := Classical.not_not.mp p
    let ⟨T, h₁⟩ := p
    have h₂ : T ∈ P A := by
      have h₂ : T ⊆ A := by
        intros x q
        have ⟨d, _⟩ := (h₁ x).mp q
        exact d
      simp_all [subs_in_power]
    have h₃ : ∃ t, (t ∈ A) ∧ f t T :=
      (onto.right T) h₂
    let ⟨t, h₃⟩ := h₃
    let T' := eval onto.left h₃.left
    have h₄ : T = T' := by
      have h₄ := onto.left.right t T T'
      have h₅ := choose_spec (onto.left.left t h₃.left)
      have h₆ : f t T' := by simp [coherence, T']
      exact h₄ ⟨h₃.left, h₂, h₅.left, h₃.right, h₆⟩
    have h₅ : (t ∈ T) → ¬ t ∈ T := by
      intro h
      have ⟨_, _⟩ := (h₁ t).mp h
      have h₆ : t ∈ T' := by simp_all
      contradiction
    have h₆ : ¬ t ∈ T := by simp_all
    have h₇ : t ∈ T := by
      have h₇ := (h₁ t).mpr
      have h₈ : ¬ t ∈ (eval onto.left h₃.left) := by
        rw [h₄] at h₆
        exact h₆
      simp_all
    contradiction
  )
