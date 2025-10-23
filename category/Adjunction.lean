import MATH.category.Hom

namespace category

@[simp]
abbrev Adjunction (F : C ⥤ D) (G : D ⥤ C) :=
  Hom[Fᵒᵖ ·, ·] ≅[⟦Cᵒᵖ × D, Types⟧] Hom[·, G·]

notation F "⊣[" C "," D "]" G => @Adjunction C D F G
notation F "⊣" G => Adjunction F G


section HomEquiv


abbrev HomEquiv (F : C ⥤ D) (G : D ⥤ C) :=
  ∀ X Y, (F[X] ⟶ Y) ≅[Types] (X ⟶ G[Y])

notation F "≃[" C "," D "]" G => @HomEquiv C D F G
notation F "≃" G => HomEquiv F G

abbrev HomEquiv.Sharp
  {φ : F ≃ G} (f : X ⟶ G[A]) : F[X] ⟶ A :=
  (φ X A).inv f

abbrev HomEquiv.Flat
  {φ : F ≃ G} (f : F[X] ⟶ A) : X ⟶ G[A] :=
  (φ X A).hom f

instance Adjunction.HomEquiv
  (φ : F ⊣[C, D] G) : F ≃ G := fun X Y =>
  ⟨φ.hom|(X, Y), φ.inv|(X, Y),
    by
      let h := φ.inv_hom_id
      simp at h
      exact (congrFun h) (X, Y),
    by
      let h := φ.hom_inv_id
      simp at h
      exact (congrFun h) (X, Y)⟩

end HomEquiv

section Units

structure Units (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟙[Cat] C ⇒ G ∘[Cat] F
  ε : F ∘[Cat] G ⇒ 𝟙[Cat] D

instance Adjunction.Units
  (φ : F ⊣[C, D] G) : Units F G where
  η := ⟨fun X => (φ.hom|(X, F[X])) (𝟙[D] F[X]), by
      intros X Y h
      let sdf : (Y, F[Y]) ⟶[Cᵒᵖ× D] (X, F[Y]) :=
        (h.op, 𝟙 F[Y])
      -- let sd := φ.hom.naturality sdf
      -- simp at sd
      -- let s := (congrFun sd) (𝟙 F[Y])
      -- simp [sdf] at s
      let ssdf := φ.hom(·, F[Y])
      simp [-Hom] at ssdf
      let sdf := coyoneda.counit_comp ssdf h
      simp at sdf
      simp?⟩
  ε := sorry

end Units
