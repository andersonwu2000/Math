import MATH.category.Hom

open CategoryTheory
namespace SetTheory

instance Discrete (A : Type u) : Category where
  obj := A
  hom X Y := PLift (X = Y)
  id X := PLift.up rfl
  comp {Y Z X} g f :=
    PLift.up (Eq.trans f.down g.down)

instance Bool : Category where
  obj := Prop
  hom p q := PLift (p → q)
  id p := PLift.up (by simp)
  comp {Y Z X} p q := PLift.up (by
    intros x
    exact p.down (q.down x))

instance Set : Category where
  obj := Category
  hom X Y := Discrete X.obj ⥤ Discrete Y.obj
  id X := ⟨id, id, by simp, by simp⟩
  comp g f := g ∘[Cat] f

abbrev Power (A : Type u) := Discrete A ⥤ Bool
notation "𝒫" A => Power A

abbrev Subset (A B : 𝒫 C) := A ⇒ B
notation A "⊆" B => Subset A B
