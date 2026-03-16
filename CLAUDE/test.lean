import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const

/-!
# Limits/Cone.lean

Limit / colimit cone。

## 定義
- `IsLimit` — `X` 是 `F` 的 limit（couniversal cone）
- `IscoLimit` — `X` 是 `F` 的 colimit（universal cocone）

## 定理
### `Limit.Canonical` / `coLimit.Canonical`
- `.IsLimit` — `Hom[Δᵒᵖ[X], F]` 是 `Hom[X, F–]` 的 limit（及對偶）
-/

-- set_option trace.Meta.synthInstance true
-- set_option profiler true
-- set_option trace.Meta.Tactic.simp.numSteps true
-- set_option trace.Meta.Tactic.simp.rewrite true

namespace CategoryTheory

/-- `IsLimit F X` means `X` is the limit of `F`.

In other words, `Hom[Δᵒᵖ–, F] ≅ Hom[–, X]  (≅ Hom[–, lim F])`. -/
abbrev IsLimit {F : J ⥤ C} (Cone : Δ[X] ⇒ F) : Prop :=
  IscoUniversal (D := ⟦J, C⟧) Cone

namespace Limit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.Cone : Δ[Hom[Δᵒᵖ[X], F]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by
    ext α
    simpa using α.naturality f

/-- `Hom[Δᵒᵖ[X], F]` is the limit of `Hom[X, F–]`.

In other words, `Hom[Δᵒᵖ[X], F] ≅ lim Hom[X, F–]` -/
def Canonical.IsLimit : IsLimit (Cone F X) :=
  fun A (φ : Δ[A] ⇒ Hom[X,F–]) => ⟨
    fun a : A => {
      app j := φ·j a,
      naturality f := by
        let p := φ.naturality f
        simp at p
        simp_all},
    by aesop_cat,
    by aesop_cat⟩

end Limit

/-- `IscoLimit F X` means `X ≅ colim F` is the colimit of `F`.

In other words, `Hom[X, –] ≅ Hom[F, Δ–]` -/
abbrev IscoLimit {F : J ⥤ C} (coCone : F ⇒ Δ[X]) : Prop :=
  IsUniversal (C := ⟦J, C⟧) coCone

namespace coLimit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.Cone : Δ[Hom[F, Δᵒᵖ[X]]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by
    ext α
    simpa using α.naturality f

def Canonical.IsLimit : IsLimit (Cone F X) :=
  fun A (φ : Δ[A] ⇒ Hom[X,F–]) => ⟨
    fun a : A => {
      app j := φ·j a,
      naturality f := by
        let p := φ.naturality f
        simp at p
        simp_all},
    by aesop,
    by aesop⟩

end coLimit

end CategoryTheory
