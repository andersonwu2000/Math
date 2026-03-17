import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const
import MATH.Category.Limits.Canonical

/-!
# Limits/Complete.lean

Complete category。

## 定義
- `Complete C` — `C` 具有所有 limit：對任意 `J` 與 `F : J ⥤ C`，`F` 有 limit
- `coComplete C` — `C` 具有所有 colimit：對任意 `J` 與 `F : J ⥤ C`，`F` 有 colimit

## 定理
- `Types.complete` — `Types` 是 complete，`lim F ≅ Hom[Δᵒᵖ[PUnit], F]`
- `Limit.prop` — `Hom[Δᵒᵖ–, F] ≅ lim Hom[–, F–]`（natural in X）
- `coLimit.prop` — `Hom[F, Δᵒᵖ–] ≅ lim Hom[F–, –]`（natural in X）
-/

namespace CategoryTheory

/-- `Complete C`：對任意 small index category `J` 和函子 `F : J ⥤ C`，`F` 有 limit -/
class Complete (C : Category) where
  lim {J : Category.{u, v}} : ⟦J, C⟧ ⥤ C
  adj {J : Category.{u, v}} : Δ ⊣[C, ⟦J, C⟧] lim

/-- `coComplete C`：對任意 small index category `J` 和函子 `F : J ⥤ C`，`F` 有 colimit -/
class coComplete (C : Category) where
  hascoLimit {J : Category.{u, v}} (F : J ⥤ C) : HascoLimit F

/-! ### Types 是 complete 的

Note.tex 證明：`Hom[1, F–] ≅ F`，由 Canonical 得
`Hom[Δᵒᵖ[1], F] ≅ lim Hom[1, F–] ≅ lim F`。
直接用 `Hom[PUnit, F–] ≅ F` 與 `Canonical.HasLimit` 轉移 limit。 -/

/-- `Types` 是 complete：`lim F = NatTrans (Δ[PUnit]) F` -/
noncomputable instance Types.complete : Complete Types where
  lim {J : Category} : ⟦J, Types⟧ ⥤ Types :=
    Hom[(Δ[PUnit] : J ⥤ Types), –]
  adj := sorry

end CategoryTheory
