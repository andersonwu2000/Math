import MATH.category.Hom

namespace category


@[simp]
def yoneda : C ⥤ ⟦Cᵒᵖ, Types⟧ where
  obj X := Hom[—, X]
  map f := {app _ h := f ∘ h}

namespace yoneda

@[simp, grind =]
theorem Unit
  (α : Hom[—, X] ⇒[Cᵒᵖ, Types] F) (f : X ⟶[Cᵒᵖ] A) :
  F[f] ((α·X) (𝟙[C] X)) = (α·A) f := by
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
  Hom[yonedaᵒᵖ—, —] ≅[⟦Cᵒᵖ × ⟦Cᵒᵖ, Types⟧, Types⟧] Evaluation :=
  NatIso.ofComponents {
    app := fun (X, F) => (Equiv X.op F).hom,
    naturality := by
      intro (X, F) (Y, G) (f, γ)
      ext α
      let h := Types.naturality γ f ((α·X) (𝟙 X))
      simp at h
      simpa}
    (fun (X, F) => (Equiv X.op F).IsIso)

theorem Unit_comp {G : D ⥤ C}
  (α : Hom[Gᵒᵖ—, G[X]] ⇒[Dᵒᵖ, Types] F) (f : X ⟶[Dᵒᵖ] A) :
  F[f] ((α·X) (𝟙[C] G[X])) = (α·A) G[f] := by
  have := (Types.naturality α f) (𝟙 G[X])
  simp_all

theorem Unit_comp' {G : D ⥤ C}
  (α : Hom[—, G—][—, X] ⇒[Cᵒᵖ, Types] F) (f : A ⟶[C] G[X]) :
  F[f] ((α·Gᵒᵖ[X]) (𝟙 G[X])) = (α·A) f := by
  have := (Types.naturality α f) (𝟙 G[X])
  simp_all

end yoneda

@[simp]
def coyoneda : Cᵒᵖ ⥤ ⟦C, Types⟧ where
  obj X := Hom[X, —]
  map f := {app _ h := h ∘ f}

namespace coyoneda

@[simp, grind =]
theorem Unit
  (α : Hom[X, —] ⇒[C, Types] F) (f : X ⟶[C] A) :
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

theorem Unit_comp {G : D ⥤ C}
  (α : Hom[Gᵒᵖ[X], G—] ⇒[D, Types] F) (f : X ⟶[D] A) :
  F[f] ((α·X) (𝟙[C] G[X])) = (α·A) G[f] := by
  have := (Types.naturality α f) (𝟙 G[X])
  simp_all

theorem Unit_comp' {G : D ⥤ C}
  (α : Hom[Gᵒᵖ—, —][X, —] ⇒[C, Types] F) (f : G[X] ⟶[C] A) :
  F[f] ((α·G[X]) (𝟙 G[X])) = (α·A) f := by
  have := (Types.naturality α f) (𝟙 G[X])
  simp_all

end coyoneda
