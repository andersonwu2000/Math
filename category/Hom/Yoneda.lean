import MATH.Category.Hom.Basic

namespace category


@[simp]
def yoneda : C ⥤ ⟦Cᵒᵖ, Types⟧ where
  obj X := Hom[—, X]
  map f := post_comp f

namespace yoneda

@[simp, grind =]
theorem Unit
  (α : Hom[—, X] ⇒[Cᵒᵖ, Types] F) (f : A ⟶ X) :
  F[f] ((α·X) (𝟙 X)) = (α·A) f := by
  have := (Types.naturality α f) (𝟙 X)
  simp_all

@[simp]
def Equiv (X : C.obj) (F : Cᵒᵖ ⥤ Types) :
  (Hom[—, X] ⇒ F) ≅[Types] F.obj X where
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
      let h := Types.naturality γ f ((α·X) (𝟙 X))
      simp at h
      simpa
  case eq
  . exact (fun (X, F) => (Equiv X.op F).IsIso)

-- theorem FullyFaithful :
--   yoneda.FullyFaithful (D := ⟦Cᵒᵖ, Types⟧) := by
--     intro X Y
--     let sdf := yoneda.map
--     sorry

end yoneda

@[simp]
def coyoneda : Cᵒᵖ ⥤ ⟦C, Types⟧ where
  obj X := Hom[X, —]
  map f := pre_comp f

namespace coyoneda

@[simp, grind =]
theorem Unit
  (α : Hom[X, —] ⇒[C, Types] F) (f : A ⟶ X) :
  F[f] ((α·X) (𝟙[C] X)) = (α·A) f := by
  have := (Types.naturality α f) (𝟙 X)
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
      let h := Types.naturality γ f ((α·X) (𝟙 X))
      simp at h
      simpa}
    (fun (X, F) => (Equiv X F).IsIso)


end coyoneda
