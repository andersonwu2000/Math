import MATH.Category.Basic.NatTrans
import MATH.Category.Hom.EpiMono

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
  inv_hom_id : inv ∘ f = 𝟙 X := by
    first | grind | simp
  hom_inv_id : f ∘ inv = 𝟙 Y := by
    first | grind | simp

abbrev inv [f.IsIso] : Y ⟶ X := IsIso.inv f

def asIso [p : f.IsIso] : X ≅ Y where
  hom := f
  inv := p.inv
  inv_hom_id := p.inv_hom_id
  hom_inv_id := p.hom_inv_id

end Category.hom
namespace IsIso
variable (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp, grind =]
lemma hom_eq [f.IsIso] :
  f.asIso.hom = f := rfl

@[simp, grind =]
lemma inv_eq [f.IsIso] :
  f.asIso.inv = f.inv := rfl

@[simp, grind =]
lemma inv_hom_id' [f.IsIso] : f.inv ∘ f = 𝟙 X := by
  rw [←inv_eq]
  exact f.asIso.inv_hom_id

@[simp, grind =]
lemma hom_inv_id' [f.IsIso] : f ∘ f.inv = 𝟙 Y := by
  rw [←inv_eq]
  exact f.asIso.hom_inv_id

@[simp, grind =]
theorem hom_inv_id_assoc
  [f.IsIso] : f.inv ∘ f ∘ h = h :=
  by simp [←Category.assoc]

instance id : (𝟙 X).IsIso where
  inv := 𝟙 X

instance inv_isIso [f.IsIso] : f.inv.IsIso where
  inv := f

instance comp_isIso [f.IsIso] [g.IsIso] : (g ∘ f).IsIso where
  inv := f.inv ∘ g.inv

@[simp, grind =]
theorem inv_id : (𝟙 X).inv = 𝟙 X := rfl

@[simp, grind =]
theorem inv_comp [f.IsIso] [g.IsIso] :
  (g ∘ f).inv = f.inv ∘ g.inv := rfl

instance IsSplitMono [f.IsIso] : f.IsSplitMono where
  left_inv := f.inv
  inv_hom_id := f.asIso.inv_hom_id

instance IsSplitEpi [f.IsIso] : f.IsSplitEpi where
  right_inv := f.inv
  hom_inv_id := f.asIso.hom_inv_id

instance IsMono [f.IsIso] : f.IsMono :=
  IsSplitMono.IsMono f

instance IsEpi [f.IsIso] : f.IsEpi :=
  IsSplitEpi.IsEpi f

end IsIso

instance SplitMono_Epi_IsIso (f : X ⟶ Y)
  [f.IsSplitMono] [f.IsEpi] : f.IsIso where
  inv := f.left_inv
  inv_hom_id := f.asSplitMono.inv_hom_id
  hom_inv_id := by
    have p : f ∘ 𝟙 X = 𝟙 Y ∘ f := by simp
    rw [←f.asSplitMono.inv_hom_id, ←Category.assoc] at p
    apply f.asEpi.left_uni at p
    simp_all

instance SplitEpi_Mono_IsIso (f : X ⟶ Y)
  [f.IsSplitEpi] [f.IsMono] : f.IsIso where
  inv := f.right_inv
  hom_inv_id := f.asSplitEpi.hom_inv_id
  inv_hom_id := by
    have p : 𝟙 Y ∘ f = f ∘ 𝟙 X := by simp
    rw [←f.asSplitEpi.hom_inv_id, Category.assoc] at p
    apply f.asMono.right_uni at p
    simp_all

instance Iso.IsIso (i : X ≅ Y) : i.hom.IsIso where
  inv := i.inv

instance Iso.inv_IsIso (i : X ≅ Y) : i.inv.IsIso where
  inv := i.hom


namespace Functor
variable (f : X ⟶[C] Y) (F : C ⥤ D)

lemma map_iso_eq [f.IsIso] :
  F[f] = F[f.asIso.hom] := rfl

@[simp, grind =]
lemma map_hom_inv_id (i : X ≅ Y) :
  F[i.hom] ∘ F[i.inv] = 𝟙 F[Y] := by grind

@[simp, grind =]
lemma map_inv_hom_id (i : X ≅ Y) :
  F[i.inv] ∘ F[i.hom] = 𝟙 F[X] := by grind

def mapIso (i : X ≅ Y) : F[X] ≅ F[Y] where
  hom := F[i.hom]
  inv := F[i.inv]

@[simp, grind =]
lemma mapIso_hom (i : X ≅ Y) :
  (F.mapIso i).hom = F.map i.hom := rfl

@[simp, grind =]
lemma mapIso_inv (i : X ≅ Y) :
  (F.mapIso i).inv = F.map i.inv := rfl

instance mapIsIso [f.IsIso] : F[f].IsIso where
  inv := F[f.inv]

@[simp, grind =]
theorem map_inv [f.IsIso] :
  F[f.inv] = F[f].inv := rfl

end Functor

abbrev NatIso (F G : C ⥤ D) := F ≅[⟦C, D⟧] G

notation F "≅" G => NatIso F G

namespace NatIso

abbrev ofComponents
  (α : F ⇒[C, D] G) (eq : ∀ X, (α·X).IsIso) : F ≅ G where
  hom := α
  inv := {
    app X := (α·X).asIso.inv,
    naturality {X Y} f := calc
      _ = (α·Y).inv ∘ (α·Y ∘ F[f]) ∘ (α·X).inv :=
        by simp
      _ = ((α·Y).inv ∘ α·Y) ∘ F[f] ∘ (α·X).inv :=
        by simp only [D.assoc]
      _ = F[f] ∘ (α·X).inv :=
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

instance inv_IsIso (X : C.obj) : (α.inv·X).IsIso where
  inv := α·X

end NatIso
