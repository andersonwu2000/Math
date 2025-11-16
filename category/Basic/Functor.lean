import MATH.Category.Basic.Category

namespace category

structure Functor (C D : Category) where
  obj : C.obj → D.obj
  map : (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id X : map (𝟙 X) = 𝟙 (obj X) := by
    first | intros; simp; rfl | simp [Category.id]
  map_comp (g : Y ⟶ Z) (f : X ⟶ Y):
    map (g ∘ f) = map g ∘ map f := by
    first | dsimp; simp | simp [Category.comp]

notation:30 C "⥤" D => Functor C D
notation:max F "[" X "]" => Functor.obj F X
notation:max F "[" f "]" => Functor.map F f
attribute [simp] Functor.map_id Functor.map_comp
attribute [grind =] Functor.map_id

namespace Functor

abbrev Const (X : C.obj) : J ⥤ C where
  obj j := X
  map f := 𝟙 X

abbrev op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj := F.obj
  map := F.map
  map_comp g f := F.map_comp f g

notation F "ᵒᵖ" => Functor.op F

end Functor

@[simp]
def Cat : Category where
  obj := Category
  hom C D := C ⥤ D
  id C := {obj := id, map := id}
  comp G F :=
    {obj := G.obj ∘ F.obj, map := G.map ∘ F.map}
