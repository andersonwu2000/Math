import MATH.Category.Adjunction.Basic

/-!
## Functor/Representable.lean

本檔案定義 representability 相關構造：

- `Types.Represent_by_Unit`：在 `Types` category 中，`Unit` 所表示的 functor isomorphism
  `Hom[Unit, F–] ≅ F`，即以單點集（`Unit`）為來源的函數與集合元素之間的自然對應。
-/

-- 在 `Types` category 中，`Unit` 所表示的 functor isomorphism：`Hom[Unit, F–] ≅ F`。
-- 即以單點集（`Unit`）為來源的函數與集合元素之間的自然對應。 -
-- abbrev Types.Represent_by_Unit (F : C ⥤ Types) :
--   Hom[Unit, F—] ≅ F where
--     hom := {app := fun X a => a Unit.unit}
--     inv := {app := fun X a u => a}
