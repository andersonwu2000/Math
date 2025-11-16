import Mathlib.Tactic.PPWithUniv
import Mathlib.Tactic.Common
import Mathlib.Tactic.StacksAttribute
import Mathlib.Tactic.TryThis

universe u v

namespace category

structure Category where
  obj : Type u
  hom : obj → obj → Type v
  id X : hom X X
  comp : hom Y Z → hom X Y → hom X Z
  id_comp (f : hom X Y) : comp f (id X) = f := by simp
  comp_id (f : hom X Y) : comp (id Y) f = f := by simp
  assoc (f : hom Y Z) (g : hom X Y) (h : hom W X) :
    comp (comp f g) h = comp f (comp g h) := by
      first | intros; rfl | simp

notation:50 X "⟶[" C "]" Y => @Category.hom C X Y
notation:90 "𝟙[" C "]" X:91 => @Category.id C X
notation:60 g:61 "∘[" C "]" f:60 =>
  Category.comp (self := C) g f

notation:50 X "⟶" Y => @Category.hom _ X Y
notation:90 "𝟙" X:91 => @Category.id _ X
notation:60 g:61 "∘" f:60 => @Category.comp _ _ _ _ g f

attribute [trans] Category.comp
attribute [grind =] Category.id_comp Category.comp_id
attribute [simp] Category.id_comp Category.comp_id Category.assoc

namespace Category
variable (C : Category)

abbrev hom.dom (_ : X ⟶[C] Y) := X
abbrev hom.cod (_ : X ⟶[C] Y) := Y

abbrev op : Category where
  obj := C.obj
  hom X Y := C.hom Y X
  id X := 𝟙 X
  comp f g := g ∘ f

notation C "ᵒᵖ" => Category.op C

abbrev hom.op (f : X ⟶[C] Y) :
  Y ⟶[Cᵒᵖ] X := f

abbrev obj.op (X : Cᵒᵖ.obj) : C.obj := X

end Category

namespace Whisker

variable (h : X ⟶[C] Y)

@[simp]
theorem right_cancel :
  f = g → f ∘ h = g ∘ h := by intro w; rw [w]

@[simp]
theorem left_cancel  :
  f = g → h ∘ f = h ∘ g := by intro w; rw [w]

end Whisker
