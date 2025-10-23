import MATH.set_theory.axiom_EE
import MATH.set_theory.axiom_C
open Classical

theorem universal_set : ∀ x, x ∈ ∅ᶜ := by
  have h₀ := choose_spec empty
  have h₁ := choose_spec (complement ∅)
  simp_all

-- def Russel (x y : univ) : Prop :=
--   if ¬ x ∈ x then y = x else y = ∅

-- theorem Russel_function : Russel : ∅ᶜ ⟶ ∅ᶜ :=
--   have h₀ : left_total Russel (∅ᶜ) (∅ᶜ) := by
--     intro a h
--     simp [universal_set, Russel]
--     by_cases a ∈ a <;> simp_all
--   have h₁ : right_unique Russel (∅ᶜ) (∅ᶜ) := by
--     intros a b c
--     intro ⟨p₀, p₁, p₂, p₃, p₄⟩
--     by_cases a ∈ a <;> simp_all [Russel]
--   ⟨h₀, h₁⟩

-- -- for all x ∈ A, f(x) ∈ C
-- def contain_f (p : f : A ⟶ B) (C : univ) : Prop :=
--   ∀ x, (d : x ∈ A) → (eval p d) ∈ C

-- -- image f = ⋂{D | ∀ x∈A, f(x) ∈ D}
-- def image (p : f : A ⟶ B) (C : univ) : Prop :=
--   (contain_f p C) ∧
--   ∀ D, (contain_f p D) → C ⊆ D

-- theorem defect_image : image Russel_function I →
--   ∃ i, (i ∈ I) ∧ ∀ x, ¬ Russel x i := by
--   simp [image, contain_f]
--   intros h₀ h₁
--   have h₂ : I ∈ I := byContradiction (
--     fun h₃ => by
--       have h₄ : I ∈ ∅ᶜ := by simp [universal_set]
--       have h₅ : Russel I (eval Russel_function h₄) :=
--         by simp [coherence]
--       have h₆ : eval Russel_function h₄ ∈ I := by
--         have h₆ := h₀ I
--         simp_all
--       simp_all [Russel]
--   )
--   have h₃ : ∀ x, ¬ Russel x I := byContradiction (
--     fun h₄ => by
--       have h₅ : non_empty I := ⟨I, h₂⟩
--       simp_all [empty_unique, Russel]
--   )
--   exact ⟨I, h₂, h₃⟩

-- theorem image_of_empty_function (emp : f : ∅ ⟶ A) : image emp ∅ := by
--   simp_all [image, contain_f]
--   apply And.intro
--   . simp_all [choose_spec empty]
--   . intros D h₀ x
--     have h₁ := vacuous_truth (· ∈ D)
--     simp_all
