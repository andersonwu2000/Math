import MATH.category.Yoneda
-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category

@[simp]
def Adjunction (F : C ⥤ D) (G : D ⥤ C) :=
  Hom[Fᵒᵖ—, —] ≅ Hom[—, G—]

notation F "⊣[" C "," D "]" G => @Adjunction C D F G
notation F "⊣" G => Adjunction F G


section HomEquiv

structure HomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  equiv X A : (F[X] ⟶ A) ≅[Types] (X ⟶ G[A])
  naturality_left {X Y A} (f : Y ⟶ X) (g : F[X] ⟶ A) :
    (equiv Y A).hom (g ∘ Fᵒᵖ[f]) = f.op ∘ (equiv X A).hom g
  naturality_right {X A B} (f : F[X] ⟶ A) (g : A ⟶ B) :
    (equiv X B).hom (g ∘ f) = G[g] ∘ (equiv X A).hom f

attribute [simp, grind =] HomEquiv.naturality_left HomEquiv.naturality_right

@[simp]
theorem HomEquiv.naturality_right_symm
  (φ : HomEquiv F G) (f : X ⟶ G[A]) (g : A ⟶ B) :
  (φ.equiv X B).inv (G[g] ∘ f) = g ∘ (φ.equiv X A).inv f := by simp

@[simp]
theorem HomEquiv.naturality_left_symm
  (φ : HomEquiv F G) (f : Y ⟶ X) (g : X ⟶ G[A]) :
  (φ.equiv Y A).inv (g ∘ f) = Fᵒᵖ[f] ∘ (φ.equiv X A).inv g := by
  rw [Types.symm_eq_apply]
  grind

abbrev HomEquiv.hom
  (φ : HomEquiv F G) (f : F[X] ⟶ A) : X ⟶ G[A] :=
  (φ.equiv X A).hom f

abbrev HomEquiv.inv
  (φ : HomEquiv F G) (f : X ⟶ G[A]) : F[X] ⟶ A :=
  (φ.equiv X A).inv f

abbrev HomEquiv.Adjunction
  (φ : HomEquiv F G) : F ⊣ G := NatIso.ofComponents
    ⟨fun (X, Y) => (φ.equiv X.op Y).hom, by
      simp
      intro X A Y B f g
      ext h
      rw [←φ.naturality_left f h]
      simp⟩
    fun (X, Y) => (φ.equiv X.op Y).IsIso

abbrev Adjunction.HomEquiv
  (φ : F ⊣ G) : HomEquiv F G where
    equiv X Y := {hom := φ.hom·(X, Y), inv := φ.inv·(X, Y)}
    naturality_left {X Y A} f g := by
      let h := φ.hom(—, A).naturality f
      simp at h
      exact (congrFun h) g
    naturality_right {X A B} f g := by
      let h := φ.hom(X, —).naturality g
      simp at h
      exact (congrFun h) f

end HomEquiv

section Units

structure Units (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟙[Cat] C ⇒ G ∘[Cat] F
  ε : F ∘[Cat] G ⇒ 𝟙[Cat] D
  left_triangle  : 𝟙[⟦C, D⟧] F = (ε ◫ F) ∘ (F ◫ η)
  right_triangle : 𝟙[⟦D, C⟧] G = (G ◫ ε) ∘ (η ◫ G)

attribute [simp] Units.left_triangle Units.right_triangle

@[simp]
theorem Units.left_triangle_hom
  (u : Units F G) {f : F[X] ⟶ Y} :
  f ∘ (u.ε·F[X] ∘ F[u.η·X]) = f := by
    let p := congrArg NatTrans.app u.left_triangle
    let q := congrFun p X
    simp at q
    simp [←q]

@[simp]
theorem Units.right_triangle_hom
  (u : Units F G) {f : X ⟶ G[Y]} :
  G[u.ε·Y] ∘ (u.η·G[Y] ∘ f) = f := by
    let p := congrArg NatTrans.app u.right_triangle
    let q := congrFun p Y
    simp at q
    simp [←Category.assoc, ←q]

abbrev Units.Adjunction
  (u : Units F G) : F ⊣ G where
  hom := ⟨fun (X, Y) f => G[f] ∘ u.η·X, by
    simp; intro X A Y B f g; ext h
    repeat apply Whisker.left_cancel
    exact (u.η.naturality f).symm⟩
  inv := {app := fun (A, B) =>
      fun (f : A.op ⟶ G[B]) => u.ε·B ∘ F[f]}
  hom_inv_id := by
    simp; ext X f
    let h := (u.η.naturality f).symm
    simp at h
    simp [h]
  inv_hom_id := by simp; ext; simp

variable (φ : F ⊣[C, D] G)

abbrev Adjunction.η : 𝟙[Cat] C ⇒ G ∘[Cat] F where
  app X := (φ.hom·(X, F[X])) (𝟙 F[X])
  naturality {X Y} h := by
    simp
    rw [←φ.HomEquiv.naturality_left, ←φ.HomEquiv.naturality_right]
    simp

abbrev Adjunction.ε : F ∘[Cat] G ⇒ 𝟙[Cat] D where
  app A := (φ.inv·(Gᵒᵖ[A], A)) (𝟙 G[A])
  naturality {A B} h := by
    simp
    rw [←φ.HomEquiv.naturality_left_symm, ←φ.HomEquiv.naturality_right_symm]
    simp

theorem Adjunction.hom_right_η (f : F[X] ⟶ A) :
  φ.HomEquiv.hom f = G[f] ∘ φ.η·X := by
    simp
    rw [←φ.HomEquiv.naturality_right]
    simp

theorem Adjunction.inv_left_ε (f : X ⟶ G[A]) :
  φ.HomEquiv.inv f = φ.ε·A ∘ F[f] := by
    simp
    rw [←φ.HomEquiv.naturality_left_symm]
    simp

abbrev Adjunction.Units : Units F G where
    η := φ.η
    ε := φ.ε
    left_triangle  := by
      simp; ext X
      let q := φ.inv_left_ε (φ.HomEquiv.hom (𝟙 F[X]))
      simp at q
      exact q
    right_triangle := by
      simp; ext A
      let q := φ.hom_right_η (φ.HomEquiv.inv (𝟙 G[A]))
      simp at q
      exact q

end Units
