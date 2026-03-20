import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const
import MATH.Category.Limits.Basic

universe u v

/-!
# Limits/Complete.lean

Complete category。

## 定義
- `Complete C` — 存在 limit functor `lim` 使得 `Δ ⊣ lim`
- `ShapeComplete` — `C` 對 shape `J` 的所有 functor 都有 limit
- `CoComplete C` — 存在 colimit functor `colim` 使得 `colim ⊣ Δ`
- `ShapeCoComplete` — colimit 版本

## 定理
### `Complete` / `ShapeComplete`
- `.instShapeComplete` — `Complete C` ⟹ `ShapeComplete J C`（由 `Δ ⊣ lim` 推導）
- `.instLimit` — `ShapeComplete J C` ⟹ `Limit F`
### `CoComplete` / `ShapeCoComplete`
- `.instShapeCoComplete` — `CoComplete C` ⟹ `ShapeCoComplete J C`（由 `colim ⊣ Δ` 推導）
- `.instCoLimit` — `ShapeCoComplete J C` ⟹ `CoLimit F`
-/

namespace CategoryTheory

/-- `Complete C`：存在 limit functor `lim : ⟦J, C⟧ ⥤ C` 使得 `Δ ⊣ lim` -/
class Complete (C : Category) where
  lim {J : Category.{u, v}} : ⟦J, C⟧ ⥤ C
  adj {J : Category.{u, v}} : Δ ⊣[C, ⟦J, C⟧] lim

/-- `C` 對 shape `J` 的所有 functor 都有 limit -/
class ShapeComplete (J C : Category) where
  hasLimit (F : J ⥤ C) : Limit F

/-- `Complete C` 蘊含 `ShapeComplete J C`：`lim[F]` 是 `F` 的 limit -/
instance (priority := 100) Complete.instShapeComplete
    [h : Complete.{u, v} C] {J : Category.{u, v}} : ShapeComplete J C where
  hasLimit F := { lim := h.lim[F], universal := h.adj.CoUniversal F }

instance (priority := 100) ShapeComplete.instLimit
    [h : ShapeComplete J C] {F : J ⥤ C} : Limit F :=
  h.hasLimit F

/-- `CoComplete C`：存在 colimit functor `colim : ⟦J, C⟧ ⥤ C` 使得 `colim ⊣ Δ` -/
class CoComplete (C : Category) where
  colim {J : Category.{u, v}} : ⟦J, C⟧ ⥤ C
  adj {J : Category.{u, v}} : colim ⊣[⟦J, C⟧, C] Δ

/-- `C` 對 shape `J` 的所有 functor 都有 colimit -/
class ShapeCoComplete (J C : Category) where
  hascolimit (F : J ⥤ C) : CoLimit F

/-- `CoComplete C` 蘊含 `ShapeCoComplete J C`：`colim[F]` 是 `F` 的 colimit -/
instance (priority := 100) CoComplete.instShapeCoComplete
    [h : CoComplete.{u, v} C] {J : Category.{u, v}} : ShapeCoComplete J C where
  hascolimit F := { colim := h.colim[F], universal := h.adj.Universal F }

instance (priority := 100) ShapeCoComplete.instCoLimit
    [h : ShapeCoComplete J C] {F : J ⥤ C} : CoLimit F :=
  h.hascolimit F

end CategoryTheory
