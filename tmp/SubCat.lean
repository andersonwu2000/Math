import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Limits.Shapes.Products

namespace CategoryTheory

class SubCatStruct (cat : Category.{v, u} C) : Type (max u v) where
  obj : C → Prop
  Hom {X Y} : obj X → obj Y → (X ⟶ Y) → Prop
  id {X} (h : obj X) : Hom h h (𝟙 X)
  comp : ∀ {X Y Z} {hX : obj X} {hY : obj Y} {hZ : obj Z}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Hom hX hY f → Hom hY hZ g → Hom hX hZ (f ≫ g)

instance SubCategory {cat : Category C} (S : SubCatStruct cat) :
  Category {x : C // S.obj x} where
  Hom  := fun ⟨X, hX⟩ ⟨Y, hY⟩ => {f : X ⟶ Y // S.Hom hX hY f}
  id   := fun ⟨X, hX⟩ => ⟨𝟙 X, S.id hX⟩
  comp := fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g, S.comp f g hf hg⟩

def Δ [Category C] [Category J] (X : C) : J ⥤ C where
  obj A := X
  map f := 𝟙 X

instance Types : Category Type where
  Hom a b  := a → b
  id _     := id
  comp f g := g ∘ f

instance : Coe (Type → Prop) (Type 1) where
  coe φ := {A : Type // φ A}

instance Types.FullSub (φ : Type → Prop) : Category ↑φ where
  Hom := fun ⟨X, _⟩ ⟨Y, _⟩ => X → Y
  id _ := id
  comp := fun f g => g ∘ f

@[ext]
theorem Types_ext {φ : Type → Prop} {X Y : ↑φ}
    (f g : X ⟶ Y) (h : ∀ a : X.1, f a = g a) :
    f = g := by
  funext x
  exact h x

abbrev Types.SelfProd (φ : Type → Prop) [Category ↑φ] :=
  ∀ (A : ↑φ) (f : A.1 → ↑φ),
  Limits.HasLimit (Discrete.functor f)

abbrev Types.SelfCoprod (φ : Type → Prop) [Category ↑φ] :=
  ∀ (A : ↑φ) (f : A.1 → ↑φ),
  Limits.HasColimit (Discrete.functor f)

section propositional_logic

instance PropLogicStruct : SubCatStruct Types (C := Type) where
  obj X := X = Unit ∨ X = Empty
  Hom hX hY f := True
  id h := True.intro
  comp f g := by simp_all

def PropLogic := SubCategory PropLogicStruct

#check PropLogic

def hE : PropLogicStruct.obj Empty := by simp [PropLogicStruct]
def hU : PropLogicStruct.obj Unit  := by simp [PropLogicStruct]

def imp : PropLogic.Hom ⟨Empty, hE⟩ ⟨Unit, hU⟩ :=
  let f : Types.Hom Empty Unit := fun _ => Unit.unit
  ⟨f, by simp_all [PropLogicStruct]⟩
