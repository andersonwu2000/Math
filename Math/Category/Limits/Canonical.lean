import MATH.Category.Limits.Basic

/-!
# Limits/Canonical.lean

Canonical limit：cones / cocones 作為 Hom 函子的 limit。
直接構造 `rep : Hom[Δᵒᵖ–, F] ≅ Hom[–, obj]` 的 NatIso。

## 定理
### `Limit`
- `.Canonical.Limit` — `Cone(X, F) = Δ[X] ⇒ F` 是 `Hom[X, F–] : J ⥤ Types` 的 limit
### `CoLimit`
- `.Canonical.Limit` — `Cocone(F, X) = F ⇒ Δ[X]` 是 `Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types` 的 limit
-/

namespace CategoryTheory

-- ─── Limit ────────────────────────────────────────────────────────────────────

namespace Limit

variable (F : J ⥤ C) (X : C.obj) (A : Types.obj)

private def forward (φ : Δᵒᵖ[A] ⇒ Hom[X, F–]) : A → Hom[Δᵒᵖ[X], F] :=
  fun a => {
    app j := φ·j a
    naturality f := by simpa using congrFun (φ.naturality f) a }

private def backward (g : A → Hom[Δᵒᵖ[X], F]) : Δᵒᵖ[A] ⇒ Hom[X, F–] :=
  { app j a := (g a)·j
    naturality f := by ext a; simpa using (g a).naturality f }

/-- `Cone(X, F) = Δ[X] ⇒ F` 是 `Hom[X, F–] : J ⥤ Types` 的 limit -/
instance Canonical.Limit : Limit (Hom[X, F–]) where
  obj := Hom[Δᵒᵖ[X], F]
  rep := {
    hom := { app A := forward F X A }
    inv := { app A := backward F X A }
  }

end Limit

-- ─── CoLimit ──────────────────────────────────────────────────────────────────

namespace CoLimit

variable (F : J ⥤ C) (X : C.obj) (A : Types.obj)

private def forward (φ : Δᵒᵖ[A] ⇒ Hom[Fᵒᵖ–, X]) : A → Hom[F, Δ[X]] :=
  fun a => {
    app j := φ·j a
    naturality f := by simpa using (congrFun (φ.naturality f) a).symm }

private def backward (g : A → Hom[F, Δ[X]]) : Δᵒᵖ[A] ⇒ Hom[Fᵒᵖ–, X] :=
  { app j a := (g a)·j }

/-- `Cocone(F, X) = F ⇒ Δ[X]` 是 `Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types` 的 limit -/
instance Canonical.Limit : Limit (Hom[Fᵒᵖ–, X] : Jᵒᵖ ⥤ Types) where
  obj := F ⇒ Δ[X]
  rep := {
    hom := { app A := forward F X A }
    inv := { app A := backward F X A }
  }

end CoLimit

end CategoryTheory
