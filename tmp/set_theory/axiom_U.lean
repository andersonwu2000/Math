import MATH.set_theory.EEC
open Classical

-- union f = ⋂{D | ∀ x ∈ A, f(x) ⊆ D} = {x | ∀ a∈A, x∈f(a)}
-- inter f = ⋃{D | ∀ x ∈ A, D ⊆ f(x)} = {x | ∃ a∈A, x∈f(a)}
axiom intersection : ∀ (p : f : A ⟶ ∅ᶜ), ∃ cap, ∀ x,
  (x ∈ cap) ↔ ∀ a, (d : a ∈ A) → (x ∈ eval p d)
notation "⋂" p => choose (intersection p)

example (p : f : ∅ ⟶ ∅ᶜ) : ∀ x,
  (x ∈ ∅ᶜ) ↔ ∀ a, (d : a ∈ ∅) → (x ∈ eval p d) := by
  intro x
  have h : x ∈ ∅ᶜ := by simp [universal_set]
  simp [h]
  intros x h
  have h := choose_spec empty x
  simp_all

def image_auxiliary_function (p : f : A ⟶ B) (X Y : univ) : Prop :=
  if ∀ a, (d : a ∈ A) → (eval p d) ∈ X
  then Y = X
  else Y = ∅ᶜ

theorem image_auxiliary_function_is_function (p : f : A ⟶ B) :
    (image_auxiliary_function p) : ∅ᶜ ⟶ ∅ᶜ := by
  apply And.intro
  . intro X d
    by_cases h : ∀ a, (d : a ∈ A) → (eval p d) ∈ X
    . have h₀ : image_auxiliary_function p X X := by
        simp_all [image_auxiliary_function]
      exact ⟨X, by simp [universal_set], h₀⟩
    . have h₀ : image_auxiliary_function p X (∅ᶜ) := by
        simp [*, image_auxiliary_function]
      exact ⟨∅ᶜ, by simp [universal_set], h₀⟩
  . intros X Y Z
    intro ⟨p₀, p₁, p₂, p₃, p₄⟩
    by_cases h : ∀ a, (d : a ∈ A) → (eval p d) ∈ X <;>
    simp_all [image_auxiliary_function]

noncomputable
def image (p : f : A ⟶ B) : univ :=
  let p := image_auxiliary_function_is_function p
  choose (intersection p)

theorem image_lemma (p : f : A ⟶ B) :
    ∀ a, (d : a ∈ A) → (eval p d) ∈ (image p) := by
  intro a d
  let p' := image_auxiliary_function_is_function p
  have h₀ : image p = ⋂ p' := by simp_all [image]
  have h₁ := choose_spec (intersection p')
  simp_all
  intros X dX
  by_cases h₂ : ∀ a, (d : a ∈ A) → (eval p d) ∈ X
  . have h₃ : image_auxiliary_function p X X := by
      simp [h₂, image_auxiliary_function]
    have h₄ : X ∈ ∅ᶜ := by simp [universal_set]
    have h₅ : eval p' dX = X := eval_equal p' dX h₄ h₃
    simp_all
  . have h₃ : image_auxiliary_function p X (∅ᶜ) := by
      simp [h₂, image_auxiliary_function]
    have h₄ : ∅ᶜ ∈ ∅ᶜ := by simp [universal_set]
    have h₅ : eval p' dX = ∅ᶜ := eval_equal p' dX h₄ h₃
    simp_all [universal_set]

def Russel (x y : univ) : Prop :=
  if ¬ x ∈ x then y = x else y = ∅

theorem Russel_function : Russel : ∅ᶜ ⟶ ∅ᶜ :=
  have h₀ : left_total Russel (∅ᶜ) (∅ᶜ) := by
    intro a h
    simp [universal_set, Russel]
    by_cases a ∈ a <;> simp_all
  have h₁ : right_unique Russel (∅ᶜ) (∅ᶜ) := by
    intros a b c
    intro ⟨p₀, p₁, p₂, p₃, p₄⟩
    by_cases a ∈ a <;> simp_all [Russel]
  ⟨h₀, h₁⟩

theorem defect_image :
  ∃ i, (i ∈ image Russel_function) ∧ ∀ x, ¬ Russel x i := by
  simp [image]
  let I := image Russel_function
  have h₀ := choose_spec (intersection Russel_function)
  have h₂ : I ∈ I := byContradiction (
    fun h₃ => by
      have h₄ : I ∈ ∅ᶜ := by simp [universal_set]
      have h₅ : Russel I I := by simp_all [Russel]
      have h₆ := eval_equal Russel_function h₄ h₄ h₅
      have h₇ : eval Russel_function h₄ ∈ I :=
        image_lemma Russel_function I h₄
      simp_all [Russel]
  )
  have h₃ : ∀ x, ¬ Russel x I := byContradiction (
    fun h₄ => by
      have h₅ : non_empty I := ⟨I, h₂⟩
      simp_all [empty_unique, Russel]
  )
  exact ⟨I, h₂, h₃⟩
