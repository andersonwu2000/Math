import MATH.Category.Limits.Basic

/-!
# Limits/Canonical.lean

Canonical limit：cones / cocones 作為 Hom 函子的 limit。

## 定理
### `Limit`
- `.Canonical.Limit` — `Cone(X, F) = Δ[X] ⇒ F` 是 `Hom[X, F–] : J ⥤ Types` 的 limit
### `CoLimit`
- `.Canonical.Limit` — `Cocone(F, X) = F ⇒ Δ[X]` 是 `Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types` 的 limit
-/

namespace CategoryTheory

-- ─── Limit ────────────────────────────────────────────────────────────────────

namespace Limit

variable (F : J ⥤ C) (X : C.obj)

/-- Canonical cone：`Hom[Δᵒᵖ[X], F] → Hom[X, F[j]]` 由 `φ ↦ φ·j` 給出 -/
def Canonical.cone : Δ[Hom[Δᵒᵖ[X], F]] ⇒ Hom[X, F–] where
  app j φ := φ·j
  naturality f := by ext α; simpa using α.naturality f

/-- `Cone(X, F) = Δ[X] ⇒ F` 是 `Hom[X, F–] : J ⥤ Types` 的 limit -/
instance Canonical.Limit : Limit (Hom[X, F–]) :=
  ({ obj  := Hom[Δᵒᵖ[X], F]
     cone := Canonical.cone F X
     lift := fun {A} (φ : Δ[A] ⇒ Hom[X, F–]) (a : A) => {
       app j := φ·j a
       naturality f := by simpa using congrFun (φ.naturality f) a }
     lift_π     := by aesop_cat
     lift_unique := fun φ k hk => funext fun a =>
       NatTrans.ext (funext fun j => congrFun (hk j) a)
   } : LimitData (Hom[X, F–])).toLimit

end Limit

-- ─── CoLimit ──────────────────────────────────────────────────────────────────

namespace CoLimit

variable (F : J ⥤ C) (X : C.obj)

/-- Canonical cone：`Hom[F, Δ[X]] → Hom[F[j], X]` 由 `φ ↦ φ·j` 給出 -/
def Canonical.cone : Δ[Hom[F, Δ[X]]] ⇒ Hom[Fᵒᵖ–, X] where
  app j (φ : F ⇒ Δ[X]) := φ·j
  naturality f := by ext φ; simp

/-- `Cocone(F, X) = F ⇒ Δ[X]` 是 `Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types` 的 limit -/
instance Canonical.Limit : Limit (Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types) :=
  ({ obj  := F ⇒ Δ[X]
     cone := Canonical.cone F X
     lift := fun {A} (φ : Δ[A] ⇒ Hom[Fᵒᵖ–, X]) (a : A) => {
       app j := φ·j a
       naturality f := by simpa using (congrFun (φ.naturality f) a).symm }
     lift_π     := by aesop_cat
     lift_unique := fun φ k hk => funext fun a =>
       NatTrans.ext (funext fun j => congrFun (hk j) a)
   } : @LimitData (Jᵒᵖ) Types Hom[Fᵒᵖ–, X]).toLimit

end CoLimit

end CategoryTheory
