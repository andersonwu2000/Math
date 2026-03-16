
structure FuncTheory (φ : Type → Prop) where
  func : φ A → φ B → φ (A → B)

structure ProdTheory (φ : Type → Prop) where
  unit : φ Unit
  prod : φ A → φ B → φ (A × B)

structure SimpTheory (φ : Type → Prop) where
  unit : φ Unit
  prod : φ A → φ B → φ (A × B)
  func : φ A → φ B → φ (A → B)

structure PiTheory (φ : Type → Prop) where
  pi    (f : A → Type) : φ A → (∀ a, φ (f a)) → φ (∀ a, f a)

structure SigmaTheory (L : List Type) (φ : Type → Prop) where
  sigma (f : A → Type) : φ A → (∀ a, φ (f a)) → φ (Σ a, f a)

structure DependTheory (L : List Type) (φ : Type → Prop) where
  unit : φ Unit
  empty : φ Empty
  prod : φ A → φ B → φ (A × B)
  func : φ A → φ B → φ (A → B)
  pi    (f : A → Type) : φ A → (∀ a, φ (f a)) → φ (∀ a, f a)
  sigma (f : A → Type) : φ A → (∀ a, φ (f a)) → φ (Σ a, f a)


section Examples

example (φ : Type → Prop) (L : List Type) :
  DependTheory L φ → SimpTheory φ :=
  fun ⟨h₀, _, h₁, h₂, _, _⟩ => ⟨h₀, h₁, h₂⟩

example(T : FuncTheory φ) (hA : φ A) (hB : φ B) :
  {X : Type // φ X} :=
  ⟨A → B, T.func hA hB⟩

private
inductive eg_theory (L : List Type) where
  | basic (A : Type) {p : A ∈ L}
  | func  : eg_theory L → eg_theory L → eg_theory L
  | prod  : eg_theory L → eg_theory L → eg_theory L

@[simp]
private
def eg_generator (L : List Type) : eg_theory L → Type
  | .basic A => A
  | .func A B => eg_generator L A → eg_generator L B
  | .prod A B => eg_generator L A × eg_generator L B
private
def is_type (L : List Type) (A : Type) :=
  ∃ t, A = eg_generator L t

example : SimpTheory (is_type [Nat, Unit]) := ⟨
  ⟨.basic Unit (p := by simp), by simp⟩,
  fun ⟨A, _⟩ ⟨B, _⟩ => ⟨.prod A B, by simp_all⟩,
  fun ⟨A, _⟩ ⟨B, _⟩ => ⟨.func A B, by simp_all⟩
  ⟩
