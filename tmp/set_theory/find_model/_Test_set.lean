import MATH.set.Test
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.SetLike.Basic
import Mathlib.Logic.Small.Basic


universe u

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
@[pp_with_univ]
def ZFSet : Type (u + 1) :=
  Quotient PSet.setoid.{u}

namespace ZFSet

/-- Turns a pre-set into a ZFC set. -/
def mk : PSet → ZFSet :=
  Quotient.mk''

@[simp]
theorem mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x) :=
  rfl

@[simp]
theorem mk_out : ∀ x : ZFSet, mk x.out = x :=
  Quotient.out_eq

/-- A set function is "definable" if it is the image of some n-ary `PSet`
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
class Definable (n) (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) where
  /-- Turns a definable function into an n-ary `PSet` function. -/
  out : (Fin n → PSet.{u}) → PSet.{u}
  /-- A set function `f` is the image of `Definable.out f`. -/
  mk_out xs : mk (out xs) = f (mk <| xs ·) := by simp

attribute [simp] Definable.mk_out

/-- An abbrev of `ZFSet.Definable` for unary functions. -/
abbrev Definable₁ (f : ZFSet.{u} → ZFSet.{u}) := Definable 1 (fun s ↦ f (s 0))

/-- A simpler constructor for `ZFSet.Definable₁`. -/
abbrev Definable₁.mk {f : ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u}) (mk_out : ∀ x, ⟦out x⟧ = f ⟦x⟧) :
    Definable₁ f where
  out xs := out (xs 0)
  mk_out xs := mk_out (xs 0)

/-- Turns a unary definable function into a unary `PSet` function. -/
abbrev Definable₁.out (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f] :
    PSet.{u} → PSet.{u} :=
  fun x ↦ Definable.out (fun s ↦ f (s 0)) ![x]

lemma Definable₁.mk_out {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f]
    {x : PSet} :
    .mk (out f x) = f (.mk x) :=
  Definable.mk_out ![x]

/-- An abbrev of `ZFSet.Definable` for binary functions. -/
abbrev Definable₂ (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) := Definable 2 (fun s ↦ f (s 0) (s 1))

/-- A simpler constructor for `ZFSet.Definable₂`. -/
abbrev Definable₂.mk {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u} → PSet.{u}) (mk_out : ∀ x y, ⟦out x y⟧ = f ⟦x⟧ ⟦y⟧) :
    Definable₂ f where
  out xs := out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)

/-- Turns a binary definable function into a binary `PSet` function. -/
abbrev Definable₂.out (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f] :
    PSet.{u} → PSet.{u} → PSet.{u} :=
  fun x y ↦ Definable.out (fun s ↦ f (s 0) (s 1)) ![x, y]

lemma Definable₂.mk_out {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} [Definable₂ f]
    {x y : PSet} :
    .mk (out f x y) = f (.mk x) (.mk y) :=
  Definable.mk_out ![x, y]

instance (f) [Definable₁ f] (n g) [Definable n g] :
    Definable n (fun s ↦ f (g s)) where
  out xs := Definable₁.out f (Definable.out g xs)

instance (f) [Definable₂ f] (n g₁ g₂) [Definable n g₁] [Definable n g₂] :
    Definable n (fun s ↦ f (g₁ s) (g₂ s)) where
  out xs := Definable₂.out f (Definable.out g₁ xs) (Definable.out g₂ xs)

instance (n) (i) : Definable n (fun s ↦ s i) where
  out s := s i

lemma Definable.out_equiv {n} (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) [Definable n f]
    {xs ys : Fin n → PSet} (h : ∀ i, xs i ≈ ys i) :
    out f xs ≈ out f ys := by
  rw [← Quotient.eq_iff_equiv, mk_eq, mk_eq, mk_out, mk_out]
  exact congrArg _ (funext fun i ↦ Quotient.sound (h i))

lemma Definable₁.out_equiv (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f]
    {x y : PSet} (h : x ≈ y) :
    out f x ≈ out f y :=
  Definable.out_equiv _ (by simp [h])

lemma Definable₂.out_equiv (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f]
    {x₁ y₁ x₂ y₂ : PSet} (h₁ : x₁ ≈ y₁) (h₂ : x₂ ≈ y₂) :
    out f x₁ x₂ ≈ out f y₁ y₂ :=
  Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

end ZFSet

namespace Classical

open PSet ZFSet

/-- All functions are classically definable. -/
noncomputable def allZFSetDefinable {n} (F : (Fin n → ZFSet.{u}) → ZFSet.{u}) : Definable n F where
  out xs := (F (mk <| xs ·)).out

end Classical

namespace ZFSet

open PSet

theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq

theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h

theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotient.exact

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
protected def Mem : ZFSet → ZFSet → Prop :=
  Quotient.lift₂ (· ∈ ·) fun a b c d (hx : _ ∧ _) (hy : _ ∧ _) =>
    propext (by simp_all)

instance : Membership ZFSet ZFSet where
  mem t s := ZFSet.Mem s t
