import Mathlib.Tactic.Common
import MATH.Category.Tactic.Init

universe u v

/-!
# Basic.lean

Category 的基礎結構。

## 定義
- `Category` — object、morphism、identity、composition + 公理
- `Category.op` — opposite category `Cᵒᵖ`

## 定理
### `Whisker`
- `.right_cancel` / `.left_cancel` — cancellation
- `.triple_cancel` — 三重消去
-/

namespace CategoryTheory

/-- `Category`：object、morphism、identity、composition，滿足 `id_comp`、`comp_id`、`assoc`。 -/
structure Category where
  obj : Type u
  hom : obj → obj → Type v
  id X : hom X X
  comp : hom Y Z → hom X Y → hom X Z
  id_comp (f : hom X Y) : comp f (id X) = f := by aesop_cat
  comp_id (f : hom X Y) : comp (id Y) f = f := by aesop_cat
  assoc (f : hom Y Z) (g : hom X Y) (h : hom W X) :
    comp (comp f g) h = comp f (comp g h) := by aesop_cat

-- 帶明確 category 的 notation
notation:50 X " ⟶[" C "] " Y => @Category.hom C X Y
notation:90 "𝟙[" C "] " X:91 => @Category.id C X
notation:60 g:61 " ○[" C "] " f:60 =>
  Category.comp (self := C) g f

-- 省略 category 的簡潔 notation
notation:50 X " ⟶ " Y => @Category.hom _ X Y
notation:90 "𝟙" X:91 => @Category.id _ X
notation:90 "𝟙" => @Category.id _ _
notation:60 g:61 " ○ " f:60 => @Category.comp _ _ _ _ g f

attribute [trans] Category.comp
attribute [simp] Category.id_comp Category.comp_id Category.assoc
attribute [grind =] Category.id_comp Category.comp_id
attribute [grind _=_] Category.assoc

-- ─── Category ──────────────────────────────────────────────────────────────

namespace Category
variable (C : Category)

abbrev hom.dom (_ : X ⟶[C] Y) := X
abbrev hom.cod (_ : X ⟶[C] Y) := Y

/-- Opposite category `Cᵒᵖ`：morphism 方向反轉 -/
abbrev op : Category where
  obj := C.obj
  hom X Y := C.hom Y X
  id X := 𝟙 X
  comp f g := g ○ f

notation C "ᵒᵖ" => Category.op C

abbrev hom.op (f : X ⟶[C] Y) : Y ⟶[Cᵒᵖ] X := f
abbrev obj.op (X : Cᵒᵖ.obj) : C.obj := X

end Category

-- ─── Whisker ───────────────────────────────────────────────────────────────

namespace Whisker
variable (h : X ⟶[C] Y)

lemma right_cancel : f = g → f ○ h = g ○ h := congrArg (· ○ h)
lemma left_cancel : f = g → h ○ f = h ○ g := congrArg (h ○ ·)

/-- 三重消去：(a ○ b ○ c) ○ (d ○ g ○ f) = 𝟙，其中 c ○ d = 𝟙、b ○ g = 𝟙、a ○ f = 𝟙 -/
@[simp, grind =]
lemma triple_cancel
    (p1 : c ○ d = 𝟙) (p2 : b ○ g = 𝟙) (p3 : a ○ f = 𝟙) :
    (a ○ b ○ c) ○ (d ○ g ○ f) = 𝟙 := by
  grind

end Whisker
end CategoryTheory
