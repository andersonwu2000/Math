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
set_option trace.Meta.synthInstance true
set_option profiler true

namespace category
variable {C : Category}

structure Iso (X Y : C.obj) where
  hom : X ⟶ Y
  inv : Y ⟶ X
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
variable {C : Category} {X Y : C.obj} (f : X ⟶ Y)

class IsIso  where
  inv : Y ⟶ X
  inv_hom_id : inv ∘ f = 𝟙 X := by
    first | grind | simp
  hom_inv_id : f ∘ inv = 𝟙 Y := by
    first | grind | simp

attribute [simp, grind =] IsIso.hom_inv_id IsIso.inv_hom_id
abbrev inv [f.IsIso] : Y ⟶ X := IsIso.inv f
notation:max f:max "⁻¹" => inv f

end Category.hom
namespace IsIso
variable (f : X ⟶ Y) (g : Y ⟶ Z)

instance id : (𝟙 X).IsIso where
  inv := 𝟙 X

instance trans [f.IsIso] [g.IsIso] : (g ∘ f).IsIso where
  inv := f⁻¹ ∘ g⁻¹

@[simp, grind =]
theorem inv_id : (𝟙 X)⁻¹ = 𝟙 X := rfl

instance inv_isIso [f.IsIso] : f⁻¹.IsIso where
  inv := f

@[simp, grind =, grind _=_]
theorem inv_comp [f.IsIso] [g.IsIso] :
  (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹ := rfl

instance IsSplitMono [p : f.IsIso] : f.IsSplitMono where
  left_inv := f⁻¹
  inv_hom_id := p.inv_hom_id

instance IsSplitEpi [p : f.IsIso] : f.IsSplitEpi where
  right_inv := f⁻¹
  hom_inv_id := p.hom_inv_id

instance IsMono [f.IsIso] : f.IsMono :=
  (IsIso.IsSplitMono f).IsMono

instance IsEpi [f.IsIso] : f.IsEpi :=
  (IsIso.IsSplitEpi f).IsEpi

@[simp, grind =]
theorem id_assoc_left [f.IsIso] :
  f⁻¹ ∘ f ∘ h = h := by simp [←Category.assoc]

@[simp, grind =]
theorem id_assoc_right [f.IsIso] :
  f ∘ f⁻¹ ∘ h = h := by simp [←Category.assoc]

end IsIso

instance Iso.IsIso (i : X ≅ Y) : i.hom.IsIso where
  inv := i.inv

instance Iso.invIsIso (i : X ≅ Y) : i.inv.IsIso where
  inv := i.hom

instance SplitMono_Epi_IsIso (f : X ⟶ Y)
  [p : f.IsSplitMono] [q : f.IsEpi] : f.IsIso where
  inv := f.left_inv
  inv_hom_id := p.inv_hom_id
  hom_inv_id := by
    have h : f ∘ 𝟙 X = 𝟙 Y ∘ f := by simp
    rw [←p.inv_hom_id, ←Category.assoc] at h
    apply q.left_uni at h
    simp_all

instance SplitEpi_Mono_IsIso (f : X ⟶ Y)
  [p : f.IsSplitEpi] [q : f.IsMono] : f.IsIso where
  inv := f.right_inv
  hom_inv_id := p.hom_inv_id
  inv_hom_id := by
    have h : 𝟙 Y ∘ f = f ∘ 𝟙 X := by simp
    rw [←p.hom_inv_id, Category.assoc] at h
    apply q.right_uni at h
    simp_all


namespace Functor
variable {X Y} (f : X ⟶[C] Y) (F : C ⥤ D)

instance mapIsIso [f.IsIso] : F[f].IsIso where
  inv := F[f.inv]

@[simp, grind =, grind _=_]
theorem mapIso.map_inv [f.IsIso] :
  F[f.inv] = F[f].inv := rfl

def mapIso (i : X ≅ Y) : F[X] ≅ F[Y] where
  hom := F[i.hom]
  inv := F[i.inv]

notation:max F "[" i "]" => mapIso F i

@[simp, grind =]
lemma mapIso.hom (i : X ≅ Y) :
  F[i].hom = F[i.hom] := rfl

@[simp, grind =]
lemma mapIso.inv (i : X ≅ Y) :
  F[i].inv = F[i.inv] := rfl

@[simp, grind =]
lemma mapIso.map_hom_inv_id (i : X ≅ Y) :
  F[i.hom] ∘ F[i.inv] = 𝟙 F[Y] := by grind

@[simp, grind =]
lemma mapIso.map_inv_hom_id (i : X ≅ Y) :
  F[i.inv] ∘ F[i.hom] = 𝟙 F[X] := by grind

end Functor

abbrev NatIso (F G : C ⥤ D) := F ≅[⟦C, D⟧] G

notation F "≅" G => NatIso F G

namespace NatIso

abbrev ofComponents
  (α : F ⇒[C, D] G) (eq : ∀ X, (α·X).IsIso) : F ≅ G where
  hom := α
  inv := {
    app X := (eq X).inv,
    naturality {X Y} f := calc
      _ = (α·Y)⁻¹ ∘ (α·Y ∘ F[f]) ∘ (α·X)⁻¹ := by simp
      _ = F[f] ∘ (α·X)⁻¹ := by grind}

variable {F G : C ⥤ D} (α : F ≅ G)

abbrev app (X : C.obj) := (α.hom·X)
notation α "·" X:101 => app α X

@[simp, grind =]
theorem inv_hom_id_app (X : C.obj) :
  α.inv·X ∘ α·X = 𝟙 F[X] := by
  let h := α.inv_hom_id
  simp at h
  exact congrFun h X

@[simp, grind =]
theorem hom_inv_id_app (X : C.obj) :
  α·X ∘ α.inv·X = 𝟙 G[X] := by
  let h := α.hom_inv_id
  simp at h
  exact congrFun h X

instance IsIso (X : C.obj) : (α.hom·X).IsIso where
  inv := α.inv·X

instance inv_IsIso (X : C.obj) : (α.inv·X).IsIso where
  inv := α.hom·X

end NatIso
