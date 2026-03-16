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
@[simp]
instance : Coe (X ≅ Y) (X ⟶ Y) where
  coe i := i.hom

namespace Iso

@[ext, grind ext]
theorem ext {f g : X ≅ Y}
  (p : f.hom = g.hom) : f = g := by
  suffices f.inv = g.inv by grind [Iso]
  have : f.inv = f.inv ∘ f ∘ g.inv := by simp_all
  rw [←Category.assoc, f.inv_hom_id, Category.comp_id] at *
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

variable (f : X ≅ Y)


@[simp, grind =]
theorem hom_inv_id_assoc : f.inv ∘ f ∘ h = h :=
  by simp [←Category.assoc]

abbrev SplitMono : SplitMono X Y where
  hom := f.hom
  left_inv := f.inv
  inv_hom_id := f.inv_hom_id

abbrev SplitEpi : SplitEpi X Y where
  hom := f.hom
  right_inv := f.inv
  hom_inv_id := f.hom_inv_id

abbrev Mono : Mono X Y := f.SplitMono.Mono
abbrev Epi : Epi X Y := f.SplitEpi.Epi

end Iso

abbrev SplitMono_Epi_toIso
  (f : SplitMono X Y) (g : X ↠ Y) (h : f.hom = g.hom) : X ≅ Y where
  hom := f.hom
  inv := f.left_inv
  inv_hom_id := f.inv_hom_id
  hom_inv_id := by
    have p : f ∘ 𝟙 X = 𝟙 Y ∘ f := by simp
    rw [←f.inv_hom_id, ←Category.assoc, h] at p
    apply g.left_uni at p
    simp_all

abbrev SplitEpi_Mono_toIso
  (f : SplitEpi X Y) (g : X ↣ Y) (h : f.hom = g.hom) : X ≅ Y where
  hom := f.hom
  inv := f.right_inv
  hom_inv_id := f.hom_inv_id
  inv_hom_id := by
    have p : 𝟙 Y ∘ f = f ∘ 𝟙 X := by simp
    rw [←f.hom_inv_id, Category.assoc, h] at p
    apply g.right_uni at p
    simp_all


namespace Functor
variable (F : C ⥤ D) (f : X ≅[C] Y)

@[simp, grind =]
lemma map_hom_inv_id :
  F[f.hom] ∘ F[f.inv] = 𝟙 F[Y] := by grind

@[simp, grind =]
lemma map_inv_hom_id :
  F[f.inv] ∘ F[f.hom] = 𝟙 F[X] := by grind

def mapIso (i : X ≅ Y) : F[X] ≅ F[Y] where
  hom := F[i.hom]
  inv := F[i.inv]

@[simp, grind =]
lemma mapIso_hom :
  (F.mapIso f).hom = F[f] := rfl

@[simp, grind =]
lemma mapIso_inv (i : X ≅ Y) :
  (F.mapIso i).inv = F[i.inv] := rfl

end Functor

abbrev NatIso (F G : C ⥤ D) := F ≅[⟦C, D⟧] G

notation F "≅" G => NatIso F G

namespace NatIso
variable (F G : C ⥤ D)

abbrev ofComponents
  (app : ∀ X, F[X] ≅ G[X])
  (naturality : ∀ {X Y} (f : X ⟶ Y), app Y ∘ F[f] = G[f] ∘ app X) : F ≅ G where
  hom := {app X := (app X).hom}
  inv := by
    constructor
    case app
    . exact fun X => (app X).inv
    . intro X Y f
      let h := (app Y).symm.Mono.cancel.mpr (naturality f)
      simp at h
      simp [h]

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

abbrev IsIso (X : C.obj) : F[X] ≅ G[X] where
  hom := α·X
  inv := α.inv·X

@[simp, grind =]
theorem hom_eq : α.hom·X = (IsIso α X).hom := by simp

theorem naturality (g g' : G[X] ⟶ Z) :
    g ∘ α·X = g' ∘ α·X ↔ g = g' := by simp_all

end NatIso
