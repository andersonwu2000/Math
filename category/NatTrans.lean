import MATH.category.Functor

namespace category

@[ext]
structure NatTrans (F G : C ⥤ D) where
  app X : F[X] ⟶ G[X]
  naturality (f : X ⟶[C] Y) :
    app Y ∘ F[f] = G[f] ∘ app X := by simp

namespace NatTrans

notation:30 F "⇒[" C "," D "]" G => @NatTrans C D F G
notation:30 F "⇒" G => NatTrans F G
notation α "·" X:101 => app α X
attribute [simp] naturality
attribute [grind _=_] naturality

@[simp, grind =]
theorem func_naturality
  (F : D ⥤ E) (α : G ⇒[C, D] H)
  (f : X ⟶ Y) (h : Z ⟶ F[G[X]]) :
    F[α·Y]  ∘ F[G[f]] ∘ h =
    F[H[f]] ∘ F[α·X]  ∘ h := by
  rw [←E.assoc, ←F.map_comp]
  simp

@[simp, grind =]
theorem naturality_assoc
  (α : F ⇒[C, D] G) (f : X ⟶ Y) (h : Z ⟶ F[X]) :
    α·Y ∘ F[f] ∘ h = G[f] ∘ α·X ∘ h :=
  func_naturality (𝟙[Cat] D) α f h


abbrev HorizontalComp
  (α : F ⇒[C, D] G) (β : H ⇒[D, E] K) :
  H ∘[Cat] F ⇒ K ∘[Cat] G where
  app X := K[α·X] ∘ β·(F[X])

notation:60 β:61 "◫" α:60 => HorizontalComp α β


end NatTrans

abbrev FunctorCat (C D : Category) : Category where
  obj := C ⥤ D
  hom F G := NatTrans F G
  id F := {app X := 𝟙 F[X]}
  comp β α := {app X := β·X ∘ α·X}

notation "⟦" C "," D "⟧" => FunctorCat C D

abbrev Functor.const : C ⥤ ⟦J, C⟧ where
  obj X := {
    obj := fun j => X,
    map := fun f => 𝟙 X }
  map f := {app := fun j => f}
