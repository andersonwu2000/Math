import MATH.category.ProductCat

/-
Notation
` X ≅ Y `    : Iso X Y
` X ≅[C] Y ` : @Iso C X Y
` F ≅ G `    : NatIso F G

* Iso
    op
    refl symm comp : equivalence relation
* Category.hom
    IsIso
    Iso : IsIso to Iso
* Iso.IsIso
* Fcuntor
    mapIso : X ≅ Y → F(X) ≅ F(Y)
* NatTrans
    NatIso : natural isomorphism
      by_components : made NatIso by components
      app
      IsIso : components are Iso
-/
-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category

structure Iso {C} (X Y) where
  hom : X ⟶[C] Y
  inv : Y ⟶[C] X
  inv_hom_id : inv ∘ hom = 𝟙 X := by
    first | grind | simp; rfl | simp
  hom_inv_id : hom ∘ inv = 𝟙 Y := by
    first | grind | simp; rfl | simp

notation X "≅[" C "]" Y => @Iso C X Y
notation X "≅" Y => Iso X Y
attribute [simp, grind =] Iso.hom_inv_id Iso.inv_hom_id


namespace Iso

@[ext, grind ext]
theorem ext {i j : X ≅ Y}
  (p : i.hom = j.hom) : i = j := by
  suffices i.inv = j.inv by grind [Iso]
  have : i.inv = i.inv ∘ i.hom ∘ j.inv := by simp_all
  rw [←Category.assoc, i.inv_hom_id, Category.comp_id] at *
  assumption

abbrev op (i : X ≅[C] Y) : Y ≅[Cᵒᵖ] X where
  hom := i.hom
  inv := i.inv

@[refl]
abbrev refl : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

@[symm]
abbrev symm (i : X ≅ Y) : Y ≅ X where
  hom := i.inv
  inv := i.hom

@[trans]
abbrev trans
  (i : X ≅ Y) (j : Y ≅ Z) : X ≅ Z where
  hom := j.hom ∘ i.hom
  inv := i.inv ∘ j.inv

end Iso
namespace Category.hom
variable (f : X ⟶ Y)

class IsIso  where
  inv : Y ⟶ X
  id_left : inv ∘ f = 𝟙 X := by
    first | grind | simp
  id_right : f ∘ inv = 𝟙 Y := by
    first | grind | simp

abbrev inv [p : f.IsIso] : Y ⟶ X := p.inv

def Iso [p : f.IsIso] : X ≅ Y where
  hom := f
  inv := f.inv
  inv_hom_id := p.id_left
  hom_inv_id := p.id_right

lemma Iso_hom_eq [f.IsIso] : f = f.Iso.hom := rfl

@[simp, grind =]
lemma Iso.inv_hom_id [f.IsIso] :
  f.Iso.inv ∘ f = 𝟙 X := by
  conv in f => rw [f.Iso_hom_eq]
  exact f.Iso.inv_hom_id

@[simp, grind =]
lemma Iso.hom_inv_id [f.IsIso] :
  f ∘ f.Iso.inv = 𝟙 Y := by
  conv in f => rw [f.Iso_hom_eq]
  exact f.Iso.hom_inv_id

@[simp, grind =]
theorem hom_inv_id_assoc
  (f : X ⟶ Y) [IsIso f] (g : Z ⟶ X) :
  f.Iso.inv ∘ f ∘ g = g :=
  by simp [←Category.assoc]

end Category.hom

instance Iso.IsIso (i : X ≅ Y) : i.hom.IsIso where
  inv := i.inv

namespace Functor
variable (F : C ⥤ D)

lemma map_iso_eq
  (f : X ⟶ Y) [f.IsIso] :
  F[f] = F[f.Iso.hom] := rfl

@[simp, grind =]
lemma map_hom_inv_id (i : X ≅ Y) :
  F[i.hom] ∘ F[i.inv] = 𝟙 F[Y] := by grind

@[simp, grind =]
lemma map_inv_hom_id (i : X ≅ Y) :
  F[i.inv] ∘ F[i.hom] = 𝟙 F[X] := by grind

abbrev mapIso (i : X ≅ Y) : F[X] ≅ F[Y] where
  hom := F[i.hom]
  inv := F[i.inv]

end Functor

abbrev NatIso (F G : C ⥤ D) := F ≅[⟦C, D⟧] G

notation F "≅" G => NatIso F G

namespace NatIso

abbrev ofComponents
  (α : F ⇒[C, D] G) (eq : ∀ X, (α·X).IsIso) : F ≅ G where
  hom := α
  inv := {
    app X := (α·X).Iso.inv,
    naturality {X Y} f := calc
      _ = (α·Y).Iso.inv ∘ (α·Y ∘ F[f]) ∘ (α·X).Iso.inv :=
        by simp
      _ = ((α·Y).Iso.inv ∘ α·Y) ∘ F[f] ∘ (α·X).Iso.inv :=
        by simp only [D.assoc]
      _ = F[f] ∘ (α·X).Iso.inv :=
        by simp}

variable {F G : C ⥤ D} (α : F ≅ G)

abbrev app (X : C.obj) := (α.hom·X)
notation α "·" X:101 => app α X

@[simp, grind =]
theorem inv_hom_id_app (X : C.obj) :
  α.inv.app X ∘ α·X = 𝟙 F[X] := by
  let h := α.inv_hom_id
  simp at h
  exact congrFun h X

@[simp, grind =]
theorem hom_inv_id_app (X : C.obj) :
  α·X ∘ α.inv.app X = 𝟙 G[X] := by
  let h := α.hom_inv_id
  simp at h
  exact congrFun h X

instance IsIso (X : C.obj) : (α·X).IsIso where
  inv := α.inv·X

instance IsIso_inv (X : C.obj) : (α.inv·X).IsIso where
  inv := α·X

end NatIso
