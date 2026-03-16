import MATH.Category.Limits.Basic

/-!
# Limits/Canonical.lean

Canonical limit：`Hom[Δᵒᵖ[X], F]` 是 `Hom[X, F–]` 的 limit（及對偶）。

## 定理
### `HasLimit`
- `.unique` — limit 在 iso 下唯一
### `HascoLimit`
- `.unique` — colimit 在 iso 下唯一
### `Limit.Canonical`
- `.HasLimit` — `Hom[Δᵒᵖ[X], F] ≅ lim Hom[X, F–]`
### `coLimit.Canonical`
- `.HasLimit` — `Hom[F, Δᵒᵖ[X]] ≅ lim Hom[X, F–]`
-/

namespace CategoryTheory

namespace Limit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.Cone : Δ[Hom[Δᵒᵖ[X], F]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by ext α; simpa using α.naturality f

/-- `Hom[Δᵒᵖ[X], F] ≅ lim Hom[X, F–]` -/
@[reducible]
noncomputable def Canonical.HasLimit : HasLimit (Hom[X, F–]) :=
  HasLimit.ofCone Hom[Δᵒᵖ[X], F] (Cone F X)
    (fun A (φ : Δ[A] ⇒ Hom[X,F–]) => ⟨
      fun a : A => {
        app j := φ·j a,
        naturality f := by
          let p := φ.naturality f
          simp at p; simp_all},
      by aesop_cat,
      by aesop_cat⟩)

end Limit

namespace coLimit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.cone : Δ[Hom[F, Δᵒᵖ[X]]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by ext α; simpa using α.naturality f

/-- `Hom[F, Δᵒᵖ[X]] ≅ lim Hom[X, F–]` -/
@[reducible]
noncomputable def Canonical.HasLimit : HasLimit (Hom[X, F–]) :=
  HasLimit.ofCone (Hom[F, Δᵒᵖ[X]]) (Canonical.cone F X)
    (fun A (φ : Δ[A] ⇒ Hom[X,F–]) => ⟨
      fun a : A => {
        app j := by simp only [Diagonal]; exact φ·j a,
        naturality f := by
          let p := φ.naturality f
          simp at p; simp_all},
      by aesop_cat,
      by aesop_cat⟩)

end coLimit

end CategoryTheory
