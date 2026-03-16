import MATH.Category.Basic

/-!
# Functor/Basic.lean

Functor 與 category of categories。

## 定義
- `Functor` — functor `C ⥤ D`（obj、map、map_id、map_comp）
- `Functor.op` — opposite functor `Fᵒᵖ : Cᵒᵖ ⥤ Dᵒᵖ`
- `Cat` — category of categories
-/

namespace CategoryTheory

/-- `Functor F : C ⥤ D`：object mapping `obj`、morphism mapping `map`，保持 `map_id`、`map_comp`。 -/
structure Functor (C D : Category) where
  obj : C.obj → D.obj
  map : (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id X : map (𝟙 X) = 𝟙 (obj X) := by aesop_cat
  map_comp (g : Y ⟶ Z) (f : X ⟶ Y):
    map (g ○ f) = map g ○ map f := by aesop_cat

notation:30 C " ⥤ " D => Functor C D
notation:max F "[" X "]" => Functor.obj F X
notation:max F "[" f "]" => Functor.map F f
attribute [simp, grind =, grind _=_] Functor.map_id Functor.map_comp

namespace Functor

/-- Opposite functor `Fᵒᵖ : Cᵒᵖ ⥤ Dᵒᵖ` -/
abbrev op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := F.obj
  map := F.map
  map_comp g f := F.map_comp f g

notation F "ᵒᵖ" => Functor.op F

end Functor

/-- `Cat`：以 category 為 object、functor 為 morphism 的 category -/
@[simp]
def Cat : Category where
  obj := Category
  hom C D := C ⥤ D
  id C := {obj := id, map := id}
  comp G F :=
    {obj := G.obj ∘ F.obj, map := G.map ∘ F.map}

end CategoryTheory
