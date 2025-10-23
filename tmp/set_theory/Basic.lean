
open Classical
set_option autoImplicit true

opaque univ : Type
opaque mem : univ → univ → Prop
notation A "∈" B => mem A B

def subset (A B : univ) : Prop :=
  ∀ x, (x ∈ A) → (x ∈ B)
notation A "⊆" B => subset A B

def left_total (R : univ → univ → Prop) (A B : univ) : Prop :=
  ∀ a, (a ∈ A) → ∃ b, (b ∈ B) ∧ R a b
def right_total (R : univ → univ → Prop) (A B : univ) : Prop :=
  ∀ b, (b ∈ B) → ∃ a, (a ∈ A) ∧ R a b
def left_unique (R : univ → univ → Prop) (A B : univ) : Prop :=
  ∀ a b c, (a ∈ A) ∧ (b ∈ A) ∧ (c ∈ B) ∧ (R a c) ∧ (R b c) → a = b
def right_unique (R : univ → univ → Prop) (A B : univ) : Prop :=
  ∀ a b c, (a ∈ A) ∧ (b ∈ B) ∧ (c ∈ B) ∧ (R a b) ∧ (R a c) → b = c

def function (f : univ → univ → Prop) (A B : univ) : Prop :=
  left_total f A B ∧ right_unique f A B
notation f ":" A "⟶" B => function f A B
def injection (f : univ → univ → Prop) (A B : univ) : Prop :=
  function f A B ∧ left_unique f A B
notation f ":" A "↣" B => injection f A B
def surjection (f : univ → univ → Prop) (A B : univ) : Prop :=
  function f A B ∧ right_total f A B
notation f ":" A "↠" B => surjection f A B
def bijection (f : univ → univ → Prop) (A B : univ) : Prop :=
  function f A B ∧ injection f A B ∧ surjection f A B
notation f ":" A "⇌" B => bijection f A B

noncomputable
def eval (funct : f : A ⟶ B) (p : x ∈ A) : univ :=
  choose (funct.left x p)

theorem coherence (funct : f : A ⟶ B) (p : x ∈ A) :
    f x (eval funct p) := by
  let y := eval funct p
  let h := choose_spec (funct.left x p)
  exact h.right

theorem eval_equal (funct : f : A ⟶ B)
    (h₀ : x ∈ A) (h₁ : y ∈ B) :
    f x y → eval funct h₀ = y := by
  let z := eval funct h₀
  have h := funct.right x y z
  have h₂ := choose_spec (funct.left x h₀)
  intro h₃
  have h₄ : f x z := coherence funct h₀
  have h₅ : y = eval funct h₀ := h ⟨h₀, h₁, h₂.left, h₃, h₄⟩
  simp_all

def is_set (φ : univ → Prop) : Prop :=
  ∃ A, ∀ x, (x ∈ A) ↔ φ x


def ident (A : univ) (x y : univ) : Prop :=
  x = y ∧ (x ∈ A) ∧ (y ∈ A)

theorem ident_bijection (A : univ) : bijection (ident A) A A := by
  let i := ident A
  have h₀ : left_total i A A := by
    intros a h
    have h₁ : i a a := ⟨rfl, h, h⟩
    exact ⟨a, h, h₁⟩
  have h₁ : right_total i A A := by
    intros a h
    have h₁ : i a a := ⟨rfl, h, h⟩
    exact ⟨a, h, h₁⟩
  have h₂ : left_unique i A A := by
    intros a b c
    intro ⟨p₀, p₁, p₂, p₃, p₄⟩
    simp [p₃.left, p₄.left]
  have h₃ : right_unique i A A := by
    intros a b c
    intro ⟨p₀, p₁, p₂, p₃, p₄⟩
    have h₃ : b = a := by simp [p₃.left]
    simp_all [p₄.left]
  have h₄ : function i A A := ⟨h₀, h₃⟩
  have h₅ : injection i A A := ⟨h₄, h₂⟩
  have h₆ : surjection i A A := ⟨h₄, h₁⟩
  exact ⟨h₄, h₅, h₆⟩
