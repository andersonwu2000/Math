import Mathlib.CategoryTheory.Adjunction.Basic

-- namespace category

-- Basic
--  Functor ProductCat Transformation Hom Adjunction
--  EpiMono Iso

-- class Monoid extends Category where
--   obj := Unit

-- instance Mon : Category where
--   obj := Monoid
--   hom M N := M.toCategory ⥤ N.toCategory
--   id M := 𝟙[Cat] M.toCategory
--   comp g f := Cat.comp g f

-- instance NAT : Monoid where
--   hom _ _ := Nat
--   id _ := 0
--   comp x y := x + y
--   assoc := Nat.add_assoc
namespace CategoryTheory

open Category Functor
namespace Adjunction
universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

theorem homEquiv_naturality_left' (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [CoreHomEquiv.homEquiv_naturality_left_symm]
  simp only [Equiv.symm_apply_apply]
