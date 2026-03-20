import MATH.Category.Limits.Basic

/-!
# Limits/Canonical.lean

Canonical limit：`Hom[Δᵒᵖ[X], F]` 是 `Hom[X, F–]` 的 limit（及對偶）。

## 定理
### `Limit`
- `.Canonical.Limit` — `Hom[Δᵒᵖ[X], F] ≅ lim Hom[X, F–]`
### `CoLimit`
- `.Canonical.Limit` — `Hom[F, Δᵒᵖ[X]] ≅ lim Hom[X, F–]`
-/

namespace CategoryTheory

namespace Limit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.Cone : Δ[Hom[Δᵒᵖ[X], F]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by ext α; simpa using α.naturality f

/-- `Hom[Δᵒᵖ[X], F] ≅ lim Hom[X, F–]` -/
@[reducible]
noncomputable def Canonical.Limit : Limit (Hom[X, F–]) :=
  ({ obj  := Hom[Δᵒᵖ[X], F]
     cone := Canonical.Cone F X
     lift := fun {A} (φ : Δ[A] ⇒ Hom[X, F–]) (a : A) => {
       app j := φ·j a
       naturality f := by let p := φ.naturality f; simp at p; simp_all }
     lift_π     := by aesop_cat
     lift_unique := fun φ k hk => funext fun a =>
       NatTrans.ext (funext fun j => congrFun (hk j) a)
   } : LimitData (Hom[X, F–])).toLimit

end Limit

-- ─── CoLimit ──────────────────────────────────────────────────────────────

namespace CoLimit

variable (F : J ⥤ C) (X : C.obj)

def Canonical.cone : Δ[Hom[F, Δᵒᵖ[X]]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by ext α; simpa using α.naturality f

/-- `Hom[F, Δᵒᵖ[X]] ≅ lim Hom[X, F–]` -/
@[reducible]
noncomputable def Canonical.Limit : Limit (Hom[X, F–]) :=
  ({ obj  := Hom[F, Δᵒᵖ[X]]
     cone := Canonical.cone F X
     lift := fun {A} (φ : Δ[A] ⇒ Hom[X, F–]) (a : A) => {
       app j := by dsimp [Diagonal]; exact φ·j a
       naturality f := by let p := φ.naturality f; simp at p; simp_all }
     lift_π     := by aesop_cat
     lift_unique := by
       intro A φ k hk; funext a
       apply NatTrans.ext; funext j; exact congrFun (hk j) a
   } : LimitData (Hom[X, F–])).toLimit

end CoLimit

end CategoryTheory
