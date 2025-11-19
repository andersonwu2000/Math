import MATH.Category.Hom.Basic
import MATH.Category.Hom.FullyFaithful

-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category


@[simps]
def yoneda : C ⥤ ⟦Cᵒᵖ, Types⟧ where
  obj X := Hom[—, X]
  map f := post_comp f

namespace yoneda
variable {C : Category}

@[simp, grind =]
theorem Unit
  (α : yoneda[X] ⇒[Cᵒᵖ, Types] F) (f : A ⟶ X) :
  F[f] ((α·X) (𝟙 X)) = (α·A) f := by
  have := (Types.naturality_apply α f) (𝟙 X)
  simp_all

@[simp]
def Equiv (X : C.obj) (F : Cᵒᵖ ⥤ Types) :
  (yoneda[X] ⇒ F) ≅[Types] F.obj X where
  hom α := (α·X) (𝟙 X)
  inv a := {app _ f := F[f] a}
  inv_hom_id := by simp; ext; simp

abbrev Evaluation : Cᵒᵖ × ⟦Cᵒᵖ, Types⟧ ⥤ Types where
  obj := fun (X, F) => F[X]
  map := fun {X Y} (f, α) => Y.2[f] ∘[Types] α·X.1

@[simp]
def Lemma :
  Hom[yonedaᵒᵖ—, —] ≅[⟦Cᵒᵖ × ⟦Cᵒᵖ, Types⟧, Types⟧] Evaluation := by
  apply NatIso.ofComponents
  case α : Hom[yonedaᵒᵖ—,—] ⇒ Evaluation
  . constructor
    case app
    . intro ((X, F) : (Cᵒᵖ × ⟦Cᵒᵖ, Types⟧).obj)
      exact (Equiv X.op F).hom
    case naturality
    . intro (X, F) (Y, G) (f, γ)
      ext α
      let h := Types.naturality_apply γ f ((α·X) (𝟙 X))
      simp at h
      simpa
  . exact (fun (X, F) => (Equiv X.op F).IsIso)

@[simp]
theorem Equiv.inv_eq (X Y : C.obj) :
  (Equiv X yoneda[Y]).inv = yoneda.map := by aesop

def Equiv.yoneda_iso (X Y : C.obj) :
  (yoneda[X] ⇒ yoneda[Y]) ≅[Types] Hom[X, Y] where
  hom := (Equiv X yoneda[Y]).hom
  inv := yoneda.map
  inv_hom_id := by
    let p := (Equiv X yoneda[Y]).inv_hom_id
    simp at p
    exact p

instance FullyFaithful :
  (yoneda : C ⥤ ⟦Cᵒᵖ, Types⟧).FullyFaithful where
  map_bijective X Y := (Equiv.yoneda_iso X Y).symm.IsIso

end yoneda

@[simp]
def coyoneda : Cᵒᵖ ⥤ ⟦C, Types⟧ where
  obj X := Hom[X, —]
  map f := pre_comp f

namespace coyoneda
variable {C : Category}

@[simp, grind =]
theorem Unit
  (α : Hom[X, —] ⇒[C, Types] F) (f : A ⟶ X) :
  F[f] ((α·X) (𝟙[C] X)) = (α·A) f := by
  have := (Types.naturality_apply α f) (𝟙 X)
  simp_all

@[simp]
def Equiv (X : C.obj) (F : C ⥤ Types) :
  (Hom[X, —] ⇒ F) ≅[Types] F.obj X where
  hom α := (α·X) (𝟙 X)
  inv a := {app _ f := F[f] a}
  inv_hom_id := by simp; ext; simp

abbrev Evaluation : C × ⟦C, Types⟧ ⥤ Types where
  obj := fun (X, F) => F[X]
  map := fun {X Y} (f, α) => Y.2[f] ∘[Types] α·X.1

@[simp]
def Lemma :
  Hom[coyonedaᵒᵖ—, —] ≅[⟦C × ⟦C, Types⟧, Types⟧] Evaluation :=
  NatIso.ofComponents {
    app := fun (X, F) => (Equiv X F).hom,
    naturality := by
      intro (X, F) (Y, G) (f, γ)
      ext α
      let h := Types.naturality_apply γ f ((α·X) (𝟙 X))
      simp at h
      simpa}
    (fun (X, F) => (Equiv X F).IsIso)

@[simp]
theorem Equiv.inv_eq (X Y : C.obj) :
  (Equiv X coyoneda[Y]).inv = coyoneda.map := by aesop

def Equiv.coyoneda_iso (X Y : C.obj) :
  Hom[Y, X] ≅[Types] (coyoneda[X] ⇒ coyoneda[Y]) where
  hom := coyoneda.map
  inv := (Equiv X coyoneda[Y]).hom
  inv_hom_id := by
    let p := (Equiv X coyoneda[Y]).inv_hom_id
    simp at p
    aesop
  hom_inv_id := by
    let p := (Equiv X coyoneda[Y]).inv_hom_id
    simp at p
    aesop

instance FullyFaithful :
  (coyoneda : Cᵒᵖ ⥤ ⟦C, Types⟧).FullyFaithful where
  map_bijective Y X := by
    simp at X Y
    exact (Equiv.coyoneda_iso Y X).IsIso


end coyoneda
