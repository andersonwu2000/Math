import MATH.category.Types

namespace category
-- set_option trace.Meta.synthInstance true
-- set_option profiler true

@[simp]
def Hom : Cᵒᵖ × C ⥤ Types where
  obj X := X.1 ⟶[C] X.2
  map f h := f.2 ∘ h ∘ f.1.op

abbrev post_comp (f : X ⟶[C] Y) :
  Hom[·, X] ⇒ Hom[·, Y] where
  app Z h := f ∘ h

abbrev pre_comp (f : Y ⟶[Cᵒᵖ] X) :
  Hom[Y, ·] ⇒ Hom[X, ·] where
  app Z h := h ∘ f.op

abbrev Tansformation.HorizontalFunctor :
  ⟦D, E⟧ × ⟦C, D⟧ ⥤ ⟦C, E⟧ where
  obj X := X.1 ∘[Cat] X.2
  map α := α.1 ◫ α.2
