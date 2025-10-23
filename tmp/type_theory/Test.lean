import Lean.Meta
import Mathlib.CategoryTheory.Monoidal.Types.Basic

open Lean

def printConstructors (constName : Name) : MetaM Unit := do
  -- 根據名稱獲取常量信息
  let some constInfo := (← getEnv).find? constName | throwError "Unknown constant {constName}"

  -- 檢查常量是否為歸納類型
  let ConstantInfo.inductInfo { ctors, .. } := constInfo
    | throwError "{constName} is not an inductive type"

  -- 打印構造子列表
  IO.println s!"Constructors for {constName}:"
  for constructor in ctors do
    IO.println s!"- {constructor}"

#eval printConstructors `Nat

variable (Context Body : Type)


structure Tree (B : Type u) where
  premisses : List (Tree B)
  conclusion : B × B

mutual
def auxiliary' : List (Tree α) → List (α × α)
  | [] => []
  | head :: tail => get_conclusions' head ++ auxiliary' tail

def get_conclusions' : Tree α → List (α × α)
  | ⟨P, C⟩ => C :: auxiliary' P
end

def Tree₀ : Tree Nat :=
  ⟨[], ⟨0, 1⟩⟩
def Tree₁ : Tree Nat :=
  ⟨[Tree₀, Tree₀], ⟨1, 2⟩⟩

def cons := get_conclusions' Tree₁
#reduce cons

def types_to_premiss : List (Type u) → Type u → Type u
  | [], T => T
  | head :: tail, T => head → types_to_premiss tail T

def Form := {A : Type // A ∈ [Nat, Bool]}

variable (R₀ : Form → Prop)
variable (R₁ : Form → Form → Prop)
variable (R₂ : Form → Form → Form → Prop)

inductive Rules : Form → Prop where
  | Rule₀ F : R₀ F → Rules F
  | Rule₁ F₁ F : R₁ F₁ F → Rules F₁ → Rules F
  | Rule₂ F₁ F₂ F : R₂ F₁ F₂ F → Rules F₁ → Rules F₂ → Rules F

-- Γ ⊢ A type
-- Γ ⊢ A = B
-- Γ ⊢ x : A
-- Rule₂
