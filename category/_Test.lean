import MATH.category.Hom

namespace category

-- Basic
--  Functor ProductCat Transformation Hom Adjunction
--  EpiMono Iso

class Monoid extends Category where
  obj := Unit

instance Mon : Category where
  obj := Monoid
  hom M N := M.toCategory ⥤ N.toCategory
  id M := 𝟙[Cat] M.toCategory
  comp g f := Cat.comp g f

instance NAT : Monoid where
  hom _ _ := Nat
  id _ := 0
  comp x y := x + y
  assoc := Nat.add_assoc
