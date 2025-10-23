section Syntax

universe u

abbrev BasicTypes := List (Type u)

abbrev ListToType (L : BasicTypes) := {A : Type u // A ∈ L}

inductive Var where
  | num : Nat → Var

-- S ::= x | A type | S → S | S S | λx:S S
inductive Syn (L : BasicTypes) where
  | var   : Var → Syn L
  | basic : ListToType L → Syn L
  | hom   : Syn L → Syn L → Syn L
  | app   : Syn L → Syn L → Syn L
  | lamb  : Var → Syn L → Syn L → Syn L

abbrev Context (L : BasicTypes) := List (Var × Syn L)

inductive Body (L : BasicTypes) where
  | type : Syn L → Body L
  | eq   : Syn L → Syn L → Body L
  | mem  : Syn L → Syn L → Body L
  | eqm  : Syn L → Syn L → Syn L → Body L

-- Γ ⊢ B
abbrev Form (L : BasicTypes) := Context L × Body L
abbrev Vdash (Γ : Context L) (B : Body L) : Form L := ⟨Γ, B⟩
infix:50 " ⊢ " => Vdash

-- Subst S t x  :=  S[t/x]
@[simp]
def Subst (S t : Syn L) (x : Var) : Syn L :=
  let ⟨n⟩ := x
  match S with
  | Syn.var ⟨m⟩ => if n = m then t else S
  | Syn.basic _   => S
  | Syn.hom S₀ S₁ => Syn.hom (Subst S₀ t x) (Subst S₁ t x)
  | Syn.app S₀ S₁ => Syn.app (Subst S₀ t x) (Subst S₁ t x)
  | Syn.lamb ⟨m⟩ S₀ S₁ => if n = m
    then S else Syn.lamb x (Subst S₀ t x) (Subst S₁ t x)

@[simp]
def Free (x : Var) : Syn L → Prop
  | Syn.var y => x = y
  | Syn.basic _   => False
  | Syn.hom S₀ S₁ => Free x S₀ ∨ Free x S₁
  | Syn.app S₀ S₁ => Free x S₀ ∨ Free x S₁
  | Syn.lamb y S₀ S₁ => (¬ x = y) ∧ (Free x S₀ ∨ Free x S₁)

end Syntax

section Deduction
open Body

-- S = Syn.basic A   ⇒   Γ ⊢ S type
@[simp]
def Rule₀ (F : Form L) : Prop :=
  let ⟨_, B⟩ := F
  match B with
  | type S => match S with
    | Syn.basic _ => True
    | _ => False
  | _ => False

-- Γ ⊢ A type        ⇒   Γ ⊢ A = A
-- Γ ⊢ A type        ⇒   Γ, x:A ⊢ x : A
-- Γ ⊢ A₀ = A₁       ⇒   Γ ⊢ A₁ = A₀
-- Γ ⊢ S₀ = S₁ : A   ⇒   Γ ⊢ S₁ = S₀ : A
-- Γ ⊢ S : A         ⇒   Γ ⊢           S = S : A
-- Γ ⊢ S : A₀ → A₁   ⇒η  Γ ⊢ (λx:A₀ S) x = S : A₀ → A₁   if ¬ Free x S
-- Γ, x:A₀ ⊢ S : A₁  ⇒   Γ ⊢ (λx:A₀ S) : A₀ → A₁
@[simp]
def Rule₁ (F₁ F : Form L) : Prop :=
  let ⟨Γ₁, B₁⟩ := F₁
  let ⟨Γ, B⟩ := F
  match B₁, B with
  | type A, eq  S₁ S₂ => A = S₁ ∧ A = S₂ ∧ Γ = Γ₁
  | type A, mem S₁ S₂ => match S₁ with
    | Syn.var x => A = S₂ ∧ Γ = Γ₁ ++ [(x, S₂)]
    | _ => False
  | eq  A₀ A₁, eq S₀ S₁ => A₀ = S₁ ∧ A₁ = S₀ ∧ Γ = Γ₁
  | eqm S₀ S₁ A, eqm S₃ S₄ S₅ => S₀ = S₄ ∧ S₁ = S₃ ∧ A = S₅ ∧ Γ = Γ₁
  | mem S A, eqm S₀ S₁ S₂ =>
    (S = S₀ ∧ S = S₁ ∧ A = S₂ ∧ Γ = Γ₁) ∨
    match A, S₀ with  -- η
      | Syn.hom A₀ _, Syn.app f S₃ => match f with
        | Syn.lamb x A₂ S₄ => (¬ Free x S) ∧ S = S₁ ∧ S₁ = S₄ ∧
          A = S₂ ∧ A₀ = A₂ ∧ S₃ = Syn.var x ∧ Γ = Γ₁
        | _ => False
      | _, _ => False
  | mem S A₁, mem S₀ S₁ => match Γ₁.getLast? with
    | some ⟨x, A₀⟩ =>
      S₀ = Syn.lamb x A₀ S ∧ S₁ = Syn.hom A₀ A₁ ∧ Γ = Γ₁.dropLast
    | none => False
  | _, _ => False

-- Γ ⊢ A₀ type           Γ ⊢ A₁ type    ⇒   Γ ⊢ A₀ → A₁ type
-- Γ ⊢ A type            Γ ⊢ ?          ⇒   Γ, x:A ⊢ ?
-- Γ ⊢ A₀ = A₁           Γ ⊢ A₁ = A₂    ⇒   Γ ⊢ A₀ = A₂
-- Γ ⊢ S : A₀            Γ ⊢ A₀ = A₁    ⇒   Γ ⊢ S : A₁
-- Γ ⊢ S₀ = S₁ : A₀      Γ ⊢ A₀ = A₁    ⇒   Γ ⊢ S₀ = S₁ : A₁
-- Γ, x:A₂ ⊢ S₀ = S₁:A₀  Γ ⊢ A₁ = A₂    ⇒α  Γ ⊢ λx:A₁ S₀ = λx:A₂ S₁ : A₁ → A₀
-- Γ ⊢ S₀ = S₁ : S       Γ ⊢ S₁ = S₂:S  ⇒   Γ ⊢ S₀ = S₂ : S
-- Γ ⊢ S₀ : A₀ → A₁      Γ ⊢ S₁ : A₀    ⇒   Γ ⊢ S₀ S₁ : A₁
-- Γ, x:A₀ ⊢ S₀ : A₁     Γ ⊢ S₁ : A₀    ⇒β  Γ ⊢ (λx:A₀ S₀) S₁ = S₀[S₁/x] : A₁
@[simp]
def Rule₂ (F₁ F₂ F : Form L) : Prop :=
  let ⟨Γ₁, B₁⟩ := F₁
  let ⟨Γ₂, B₂⟩ := F₂
  let ⟨Γ, B⟩ := F
  match B₁, B₂, B with
  | type A₀, type A₁, type A₂ =>
    (A₂ = Syn.hom A₀ A₁ ∧ Γ = Γ₁ ∧ Γ = Γ₂) ∨
    match Γ.getLast? with
      | some ⟨_, S⟩ => B = B₂ ∧ Γ₁ = Γ₂ ∧ Γ.dropLast = Γ₁ ∧ S = A₀
      | none => False
  | type A, _, _ => match Γ.getLast? with
    | some ⟨_, S⟩ => B = B₂ ∧ Γ₁ = Γ₂ ∧ Γ.dropLast = Γ₁ ∧ S = A
    | none => False
  | eq A₀ A₁, eq A₂ A₃, eq S₀ S₁ =>
    A₁ = A₂ ∧ A₀ = S₀ ∧ A₃ = S₁ ∧ Γ = Γ₁ ∧ Γ = Γ₂
  | mem S A₀, eq A₁ A₂, mem S₄ S₅ =>
    S = S₄ ∧ A₀ = A₁ ∧ A₂ = S₅ ∧ Γ = Γ₁ ∧ Γ = Γ₂
  | eqm S₀ S₁ A₀, eq A₁ A₂, eqm S₃ S₄ S₅ =>
    (A₀ = A₁ ∧ S₀ = S₃ ∧ S₁ = S₄ ∧ A₂ = S₅ ∧ Γ = Γ₁ ∧ Γ = Γ₂) ∨
    match Γ₁.getLast? with  -- α
      | some ⟨x, A⟩ => S₃ = Syn.lamb x A₁ S₀ ∧ S₄ = Syn.lamb x A₂ S₁ ∧
        A = A₂ ∧ S₅ = Syn.hom A₁ A₀ ∧ Γ = Γ₂ ∧ Γ = Γ₁.dropLast
      | none => False
  | eqm S₀ S₁ S₂, eqm S₃ S₄ S₅, eqm S₆ S₇ S₈ =>
    S₂ = S₅ ∧ S₅ = S₈ ∧ S₁ = S₃ ∧ S₀ = S₆ ∧ S₄ = S₇ ∧ Γ = Γ₁ ∧ Γ = Γ₂
  | mem S₀ A₀, mem S₁ A₁, mem S₂ A₂ =>
    S₂ = Syn.app S₀ S₁ ∧ A₀ = Syn.hom A₁ A₂ ∧ Γ = Γ₁ ∧ Γ = Γ₂
  | mem S₀ A₁, mem S₁ A₂, eqm S₂ S₃ A₃ =>
    match Γ₁.getLast? with  -- β
      | some ⟨x, A₀⟩ =>
          A₁ = A₃ ∧ A₀ = A₂ ∧ Γ = Γ₂ ∧ Γ = Γ₁.dropLast ∧
          S₂ = Syn.app (Syn.lamb x A₀ S₀) S₁ ∧ S₃ = Subst S₀ S₁ x
      | none => False
  | _, _, _ => False

inductive Judgment : Form L → Prop where
  | Rule₀ F : Rule₀ F → Judgment F
  | Rule₁ F₁ F : Rule₁ F₁ F → Judgment F₁ → Judgment F
  | Rule₂ F₁ F₂ F :
    Rule₂ F₁ F₂ F → Judgment F₁ → Judgment F₂ → Judgment F

end Deduction



section Example

abbrev L := [Unit, Empty, Nat, Bool, Prop]

def x₀ : Var := Var.num 0
def x₁ : Var := Var.num 1
def X₀ : Syn L := Syn.var x₀
def X₁ : Syn L := Syn.var x₁
def N : Syn L := Syn.basic ⟨Nat, by simp⟩
def U : Syn L := Syn.basic ⟨Unit, by simp⟩
def U_U : Syn L := Syn.hom U U
def N_U : Syn L := Syn.hom N U
def N_N : Syn L := Syn.hom N N

open Body

def F₀ : Form L := [] ⊢ type N
theorem h₀ : Judgment F₀ :=
  -- N = Syn.basic Nat    ⇒  [] ⊢ N type
  Judgment.Rule₀ F₀ trivial

def F₁ : Form L := [] ⊢ type U
theorem h₁ : Judgment F₁ :=
  -- U = Syn.basic Unit   ⇒  [] ⊢ U type
  Judgment.Rule₀ F₁ trivial

def F₂ : Form L := [] ⊢ type N_U
theorem h₂ : Judgment F₂ :=
  -- [] ⊢ U type   [] ⊢ N type   ⇒   [] ⊢ U → N type
  have h' : Rule₂ F₀ F₁ F₂ := by simp [F₁, F₀, F₂, N_U]
  Judgment.Rule₂ F₀ F₁ F₂ h' h₀ h₁

def F₃ := [(x₀, U)] ⊢ mem X₀ U
theorem h₃ : Judgment F₃ :=
  -- [] ⊢ U type   ⇒  [x₀:U] ⊢ x₀ : U
  have h : Rule₁ F₁ F₃ := by simp [F₁, F₃, X₀]
  Judgment.Rule₁ F₁ F₃ h h₁

def F₄ := [(x₀, U)] ⊢ type N
theorem h₄ : Judgment F₄ :=
  -- [] ⊢ U type       [] ⊢ N type   ⇒   [x₀:U] ⊢ N type
  have h : Rule₂ F₁ F₀ F₄ := by simp [F₁, F₄, F₀]
  Judgment.Rule₂ F₁ F₀ F₄ h h₁ h₀

def F₅ := [(x₀, U), (x₁, N)] ⊢ mem X₀ U
theorem h₅ : Judgment F₅ :=
  -- [x₀:U] ⊢ N type   [x₀:U] ⊢ x₀ : U   ⇒   [x₀:U, x₁:N] ⊢ x₀ : U
  have h : Rule₂ F₄ F₃ F₅ := by simp [F₄, F₃, F₅]
  Judgment.Rule₂ F₄ F₃ F₅ h h₄ h₃

def f₆ := Syn.lamb x₁ N X₀
def F₆ := [(x₀, U)] ⊢ mem f₆ N_U
theorem h₆ : Judgment F₆ :=
  -- [x₀:U, x₁:N] ⊢ x₀ : U   ⇒   [x₀:U] ⊢ (λx₁:N x₀) : N → U
  have h : Rule₁ F₅ F₆ := by simp [F₅, F₆, N_U, f₆]
  Judgment.Rule₁ F₅ F₆ h h₅

def F₇ := [(x₀, U)] ⊢ type U
theorem h₇ : Judgment F₇ :=
  Judgment.Rule₂ F₁ F₁ F₇ (by simp [F₁, F₇]) h₁ h₁

-- ⇒β    [x₀:U]  ⊢  (λx₁:U x₁) x₀ = x₁[x₀/x₁] : U
def f₈ := Syn.lamb x₁ U X₁
def F₈ := [(x₀, U)] ⊢ eqm (Syn.app f₈ X₀) (Subst X₁ X₀ x₁) U
theorem h₈ : Judgment F₈ :=
  -- [x₀:U, x₁:U] ⊢ x₁ : U
  let F := [(x₀, U), (x₁, U)] ⊢ mem X₁ U
  have lemma₁ : Judgment F :=
    Judgment.Rule₁ F₇ F (by simp [F₇, F, X₁]) h₇

  -- [x₀:U] ⊢ x₀ : U
  let F' := [(x₀, U)] ⊢ mem X₀ U
  have lemma₂ : Judgment F' :=
    Judgment.Rule₁ F₁ F' (by simp [F₁, F', X₀]) h₁

  -- ⇒β   [x₀:U]  ⊢  (λx₁:U x₁) x₀ = x₁[x₀/x₁] : U
  have h : Rule₂ F F' F₈ := by simp [F, F', F₈, f₈]
  Judgment.Rule₂ F F' F₈ h lemma₁ lemma₂

-- ⇒α    [x₀:U] ⊢ λx₁:U S₀ = λx₁:U S₁ : U → U
def S₀ := Syn.app f₈ X₀
def S₁ := Subst X₁ X₀ x₁
def F₉ := [(x₀, U)] ⊢ eqm (Syn.lamb x₁ U S₀) (Syn.lamb x₁ U S₁) U_U
theorem h₉ : Judgment F₉ :=
  let F := [] ⊢ eq U U
  have lemma₁ : Judgment F :=
    Judgment.Rule₁ F₁ F (by simp [F₁, F]) h₁

  -- [x₀:U] ⊢ U = U
  let F' := [(x₀, U)] ⊢ eq U U
  have lemma₂ : Judgment F' :=
    Judgment.Rule₂ F₁ F F' (by simp [F₁, F, F']) h₁ lemma₁

  -- [x₀:U, x₁:U] ⊢ S₀ = S₁:U
  let F'' := [(x₀, U), (x₁, U)] ⊢ eqm S₀ S₁ U
  have lemma₃ : Judgment F'' :=
    have h : Rule₂ F₇ F₈ F'' := by simp [F₇, F₈, F'', S₀, S₁]
    Judgment.Rule₂ F₇ F₈ F'' h h₇ h₈

  -- ⇒α    [x₀:U] ⊢ λx₁:U S₀ = λx₁:U S₁ : U → U
  Judgment.Rule₂ F'' F' F₉ (by simp [F'', F', F₉, U_U]) lemma₃ lemma₂
