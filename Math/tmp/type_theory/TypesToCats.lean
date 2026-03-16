import MATH.type_theory.CatsOnTypes

open CategoryTheory

instance prod_to_cartesian (T : ProdTheory φ) :
  CartesianMonoidalCategory ↑φ :=
  let 𝒯 : Limits.LimitCone (Functor.empty ↑φ) :=
    let cone : Limits.Cone (Functor.empty ↑φ) :=
      let terminal : ↑φ := ⟨Unit, T.unit⟩
      let π := fun X _ => nomatch X.as
      ⟨terminal, π, by simp_all⟩
    let isLimit : Limits.IsLimit cone :=
      let lift s := fun _ => Unit.unit
      let uniq s m j := rfl
      ⟨lift, by simp_all, uniq⟩
    ⟨cone, isLimit⟩
  let ℬ (X Y : ↑φ) : Limits.LimitCone (Limits.pair X Y) :=
    let cone : Limits.Cone (Limits.pair X Y) :=
      let prod : ↑φ := ⟨X.1 × Y.1, T.prod X.2 Y.2⟩
      let π := fun ⟨i⟩ => match i with
        | .left => fun p => p.1
        | .right => fun p => p.2
      let h := fun ⟨x⟩ ⟨y⟩ f => match x, y with
        | .left, .left => by simp
        | .left, .right => nomatch f
        | .right, .left => nomatch f
        | .right, .right => by simp
      ⟨prod, π, h⟩
    let isLimit : Limits.IsLimit cone :=
      let lift s := fun x =>
        ⟨s.2.1 {as := .left} x, s.2.1 {as := .right} x⟩
      let fac s := fun ⟨j⟩ => match j with
        | .left => rfl
        | .right => rfl
      let uniq s m f := by
        let f₀ := f ⟨.left⟩
        let f₁ := f ⟨.right⟩
        simp [cone, CategoryStruct.comp] at f₀ f₁
        ext x
        simp [lift, ←f₀]
        simp [lift, ←f₁]
      ⟨lift, fac, uniq⟩
    ⟨cone, isLimit⟩
  CartesianMonoidalCategory.ofChosenFiniteProducts 𝒯 ℬ

instance simp_to_cartesian_closed (T : SimpTheory φ) :
  @CartesianClosed ↑φ _ (prod_to_cartesian ⟨T.1, T.2⟩) :=
  let C := prod_to_cartesian ⟨T.1, T.2⟩
  let closed (X : ↑φ) : Closed X :=
    let rightAdj :=
      let obj : ↑φ → ↑φ := fun A =>
        ⟨X.1 → A.1, T.func X.2 A.2⟩
      let map {A B} (f : A⟶B) := fun g => f ∘ g
      let F := ⟨obj, map⟩
      let map_id (A : ↑φ) := rfl
      let map_comp {A B C} (f : A⟶B) (g : B⟶C) := rfl
      ⟨F, map_id, map_comp⟩
    let adj :=
      let homEquiv (A B : ↑φ) :=
        have h : ⟨X.1 × A.1, T.prod X.2 A.2⟩ =
          MonoidalCategoryStruct.tensorObj X A := rfl
        let toFun f := by
          simp at f
          rw [←h] at f
          exact fun a x => f (x, a)
        let invFun f := by
          simp [←h]
          exact fun ⟨x, a⟩ => f a x
        let left_inv : Function.LeftInverse invFun toFun := by
          simp [Function.LeftInverse]
          intro x
          rfl
        let right_inv : Function.RightInverse invFun toFun := by
          simp [Function.RightInverse]
          intro x
          rfl
        ⟨toFun, invFun, left_inv, right_inv⟩
      Adjunction.mkOfHomEquiv ⟨
        homEquiv,
        fun f g => rfl,
        fun f g => rfl⟩
    ⟨rightAdj, adj⟩
  let exp (X : ↑φ) : Exponentiable X := closed X
  CartesianClosed.mk ↑φ exp

def pi_to_self_prod (T : PiTheory φ) :
  Types.SelfProd φ := fun A f =>
  let f' : A.1 → Type := fun a => (f a).1
  let P : ↑φ :=
    ⟨∀ a, f' a, T.1 f' A.2 (fun a => (f a).2)⟩
  let π := fun ⟨a⟩ g => g a
  let cone := ⟨P, π, fun X Y ⟨⟨g⟩⟩ => by
      have h : X = Y := Discrete.ext_iff.mpr g
      subst h
      simp_all⟩
  let isLimit :=
    let lift s x := fun a => s.2.1 ⟨a⟩ x
    ⟨lift, fun s j => rfl, fun s m f => by
      ext x a
      let f' := f ⟨a⟩
      simp [cone] at f'
      simp [lift, ←f', CategoryStruct.comp, π]⟩
  ⟨cone, isLimit⟩


abbrev F_img {C : Type 1} [Category C] (F : C ⥤ Type) : Type → Prop :=
  fun A => ∃ x : C, A = F.obj x

def F_hom {C : Type 1} [Category C] (F : C ⥤ Type) :
  C ⥤ ↑(F_img F) :=
  let obj x := ⟨F.obj x, by simp⟩
  let map {X Y} (f : X ⟶ Y) := F.map f
  let map_id X : map (𝟙 X) = 𝟙 (obj X) := F.map_id X
  let map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) := F.map_comp f g
  ⟨⟨obj, map⟩, map_id, map_comp⟩

instance F_equi {C : Type 1} [Category C]
  (F : C ⥤ Type) (h : Functor.FullyFaithful F) :
  Functor.IsEquivalence (F_hom F) where
  faithful := ⟨fun p => h.map_injective p⟩
  full := ⟨fun p => h.map_surjective p⟩
  essSurj :=
    let essSurj A :=
      let ⟨_, x, h⟩ := A
      let hom := eqToHom h.symm
      let inv := eqToHom h
      let hom_inv_id := eqToHom_trans h.symm h
      let inv_hom_id := eqToHom_trans h h.symm
      ⟨x, hom, inv, hom_inv_id, inv_hom_id⟩
    ⟨essSurj⟩

noncomputable
def F_inv {C : Type 1} [Category C]
  (F : C ⥤ Type) (h : Functor.FullyFaithful F) :
  ↑(F_img F) ⥤ C :=
  let obj x : C := Exists.choose x.2
  let map {X Y : ↑(F_img F)} (f : X ⟶ Y) : obj X ⟶ obj Y := by
    let h₀ := Exists.choose_spec X.2
    let h₁ := Exists.choose_spec Y.2
    exact h.preimage ((eqToHom h₀.symm) ≫ f ≫ eqToHom h₁)
  let map_id X : map (𝟙 X) = 𝟙 (obj X) := by
    let h₀ := Exists.choose_spec X.2
    have h₁ : 𝟙 X = 𝟙 X.1 := rfl
    have h₂ : eqToHom h₀.symm ≫ 𝟙 X ≫ eqToHom h₀ = F.map (𝟙 (obj X)) := by
      rw [h₁]
      simp [obj]
    simp [map]
    rw [h₂]
    exact h.preimage_map (𝟙 (obj X))
  let map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) := by
    simp_all [map, obj]
    let x := eqToHom (Exists.choose_spec X.2).symm
    let y  := eqToHom (Exists.choose_spec Y.2)
    let y' := eqToHom (Exists.choose_spec Y.2).symm
    let z := eqToHom (Exists.choose_spec Z.2)
    have h₀ : (x ≫ f ≫ y) ≫ (y' ≫ g ≫ z) = x ≫ (f ≫ g) ≫ z := by
      simp [x, y, y', z]
    let h₁ := h.preimage_comp (x ≫ f ≫ y) (y' ≫ g ≫ z)
    rw [←h₁, h₀]
    rfl
  ⟨⟨obj, map⟩, map_id, map_comp⟩


def C_cong_Fimg {C : Type 1} [c : Category C] (F : C ⥤ Type) :
  Functor.FullyFaithful F → Function.Injective F.obj →
  IsIsomorphic (C := Cat) ⟨C, c⟩
    ⟨↑(F_img F), Types.FullSub (F_img F)⟩ := by
  intros h h'
  let C' : Cat := ⟨C, c⟩
  let D' : Cat := ⟨↑(F_img F), Types.FullSub (F_img F)⟩
  let hom_inv_id : F_hom F ⋙ F_inv F h = 𝟙 C' := by
    let h₀ (X : C) :=
      Exists.choose_spec (F_inv._proof_1 F ⟨F.obj X, F_hom._proof_1 F X⟩)
    let h₁ (X : C) := h' (h₀ X).symm
    apply Functor.hext
    . exact h₁
    . intros X Y f
      have h₂ : h.preimage (eqToHom (h₀ X).symm) = eqToHom (h₁ X) := by
        conv =>
          rhs
          rw [←h.preimage_map (eqToHom (h₁ X))]
        simp [eqToHom_map]
      have h₃ : h.preimage (eqToHom (h₀ Y)) = eqToHom (h₁ Y).symm := by
        conv =>
          rhs
          rw [←h.preimage_map (eqToHom (h₁ Y).symm)]
        simp [eqToHom_map]
      simp_all [F_hom, F_inv]
  let inv_hom_id : F_inv F h ⋙ F_hom F = 𝟙 D' := by
    apply Functor.hext
    . intro ⟨X, hX⟩
      simp_all [F_hom, F_inv, CategoryStruct.comp]
      rw [←Exists.choose_spec hX]
    . intro ⟨X, hX⟩ ⟨Y, hY⟩ f
      simp_all [F_hom, F_inv]
  exact ⟨F_hom F, F_inv F h, hom_inv_id, inv_hom_id⟩
