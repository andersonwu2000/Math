import MATH.category.NatTrans

namespace category

@[simp]
def ProductCat (C D : Category) : Category where
  obj := C.obj × D.obj
  hom X Y := C.hom X.1 Y.1 × D.hom X.2 Y.2
  id X := (𝟙 X.1, 𝟙 X.2)
  comp f g := (f.1 ∘ g.1, f.2 ∘ g.2)

notation:50 C:51 "×" D:50 => ProductCat C D

namespace ProductCat

def Swap : C × D ⥤ D × C where
  obj X := (X.2, X.1)
  map f := (f.2, f.1)

def fst : C × D ⥤ C where
  obj X := X.1
  map f := f.1

def snd : C × D ⥤ D where
  obj X := X.2
  map f := f.2

namespace Functor
variable (F : C × D ⥤ E) (X : C.obj) (Y : D.obj)

notation F "[" X "," Y "]" => Functor.obj F (X, Y)
notation F "[" f "," g "]" => Functor.map F (f, g)

@[simp, grind =]
theorem id:
  𝟙 F[X, Y] = F[𝟙 X, 𝟙 Y] :=
  (F.map_id (X, Y)).symm

@[simp, grind =]
theorem comp  :
  F.map f ∘ F.map g = F.map (f.1 ∘ g.1, f.2 ∘ g.2) :=
  Eq.symm (F.map_comp f g)

abbrev fix_left : D ⥤ E where
  obj A := F[X, A]
  map f := F[𝟙 X, f]

abbrev fix_right : C ⥤ E where
  obj A := F[A, Y]
  map f := F[f, 𝟙 Y]

notation F "[·"  "," X "]" => fix_right F X
notation F "[" X "," "·]" => fix_left F X

abbrev comp_left (G : B ⥤ C) : B × D ⥤ E where
  obj := fun (X, Y) => F[G[X], Y]
  map := fun (f, g) => F[G[f], g]

abbrev comp_right (G : B ⥤ D) : C × B ⥤ E where
  obj := fun (X, Y) => F[X, G[Y]]
  map := fun (f, g) => F[f, G[g]]

abbrev comp_both (G : A ⥤ C) (H : B ⥤ D) :
  A × B ⥤ E where
  obj := fun (X, Y) => F[G[X], H[Y]]
  map := fun (f, g) => F[G[f], H[g]]

notation F "[" G "·" "," "·]" => comp_left F G
notation F "[·" "," G "·]" => comp_right F G
notation F "[" G "·" "," H "·]" => comp_both F G H

abbrev comp_fix (G : B ⥤ C) : B ⥤ E where
  obj := fun X => F[G[X], Y]
  map := fun f => F[G[f], 𝟙 Y]

abbrev fix_comp (G : B ⥤ D) : B ⥤ E where
  obj := fun Y => F[X, G[Y]]
  map := fun f => F[𝟙 X, G[f]]

notation F "[" G "·" "," Y "]" => comp_fix F Y G
notation F "[" Y  "," G "·]" => fix_comp F Y G

end Functor

@[simp]
lemma comp_left_fix_left
  (F : C × D ⥤ E) (G : B ⥤ C) (X) :
  F[G·, ·][X, ·] = F[G[X], ·] := by simp

@[simp]
lemma comp_right_fix_right
  (F : C × D ⥤ E) (G : B ⥤ D) (X) :
  F[·, G·][·, X] = F[·, G[X]] := by simp

@[simp]
lemma comp_left_fix_right
  (F : C × D ⥤ E) (G : B ⥤ C) (X) :
  F[G·, ·][·, X] = F[G·, X] := by simp

@[simp]
lemma comp_right_fix_left
  (F : C × D ⥤ E) (G : B ⥤ D) (X) :
  F[·, G·][X, ·] = F[X, G·] := by simp

section NatTrans
variable {F G : C × D ⥤ E} (α : F ⇒ G)


abbrev NatTrans_fix_left (X : C.obj) :
  Functor.fix_left F X ⇒ Functor.fix_left G X where
  app Y := α|(X, Y)

abbrev NatTrans_fix_right (Y : D.obj) :
  Functor.fix_right F Y ⇒ Functor.fix_right G Y where
  app X := α|(X, Y)

notation α "(" "·" "," X ")" => NatTrans_fix_right α X
notation α "(" X "," "·)" => NatTrans_fix_left α X


end NatTrans
end ProductCat
