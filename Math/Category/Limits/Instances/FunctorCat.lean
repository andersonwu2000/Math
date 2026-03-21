import MATH.Category.Limits.Shapes.InitialTerminal
import MATH.Category.Limits.Shapes.BinaryProduct
import MATH.Category.Limits.Shapes.Equalizer
import MATH.Category.Structure.FunctorCat

/-!
# Limits/Instances/FunctorCat.lean

`FunctorCat`（函子範疇）的 limit shape 實例——逐點構造。

## 定理
### `FunctorCat`
- `Initial ⟦C, D⟧` — initial object = `Δ[init]`（D 有 initial 時）
- `Terminal ⟦C, D⟧` — terminal object = `Δ[term]`（D 有 terminal 時）
- `BinaryProduct F G` — binary product，逐點（D 有 binary product 時）
- `BinaryCoproduct F G` — binary coproduct，逐點（D 有 binary coproduct 時）
- `Equalizer α β` — equalizer，逐點（D 有 equalizer 時）
-/

namespace CategoryTheory

variable {C D : Category}

-- ─── Initial / Terminal ───────────────────────────────────────────────────────

/-- Functor category `⟦C, D⟧` 的 initial object `Δ[init]`（D 有 initial 時） -/
noncomputable instance FunctorCat_Initial [h : Initial D] : Initial ⟦C, D⟧ :=
  let id := Initial.data D
  InitialData.toInitial (C := ⟦C, D⟧) {
    obj := Δ[id.obj]
    map F := {
      app X := id.map F[X]
      naturality f := by
        simp only [Diagonal, Category.id_comp]
        exact (id.map_unique (F[f] ○ id.map F[_])).symm }
    map_unique α := by
      ext X
      exact id.map_unique (α·X) }

/-- Functor category `⟦C, D⟧` 的 terminal object `Δ[term]`（D 有 terminal 時） -/
noncomputable instance FunctorCat_Terminal [h : Terminal D] : Terminal ⟦C, D⟧ :=
  let td := Terminal.data D
  TerminalData.toTerminal (C := ⟦C, D⟧) {
    obj := Δ[td.obj]
    map F := {
      app X := td.map F[X]
      naturality f := by
        simp only [Diagonal, Category.comp_id]
        exact td.map_unique (td.map F[_] ○ F[f]) }
    map_unique α := by
      ext X
      exact td.map_unique (α·X) }

-- ─── BinaryProduct / BinaryCoproduct ─────────────────────────────────────────

section BinaryProduct

variable [bp : ∀ (A B : D.obj), BinaryProduct (C := D) A B]

private noncomputable def bpData (A B : D.obj) := BinaryProduct.data (C := D) A B

/-- 逐點 binary product functor：`(F ×_⟦C,D⟧ G)[X] = F[X] ×_D G[X]` -/
private noncomputable def pointwiseProdFunctor (F G : C ⥤ D) : C ⥤ D where
  obj X := (bpData F[X] G[X]).obj
  map {X Y} f :=
    (bpData F[Y] G[Y]).lift
      (F[f] ○ (bpData F[X] G[X]).π₁)
      (G[f] ○ (bpData F[X] G[X]).π₂)
  map_id X :=
    ((bpData F[X] G[X]).lift_unique _ _ (𝟙 _)
      (by simp [Functor.map_id]) (by simp [Functor.map_id])).symm
  map_comp f g := by
    -- map_comp (f : Y ⟶ Z) (g : X ⟶ Y) 在 Functor 中
    -- 目標：lift(F[f○g] ○ π₁, G[f○g] ○ π₂) = lift(F[f] ○ π₁, G[f] ○ π₂) ○ lift(F[g] ○ π₁, G[g] ○ π₂)
    exact ((bpData F[_] G[_]).lift_unique _ _
      ((bpData F[_] G[_]).lift (F[f] ○ (bpData F[_] G[_]).π₁)
          (G[f] ○ (bpData F[_] G[_]).π₂) ○
        (bpData F[_] G[_]).lift (F[g] ○ (bpData F[_] G[_]).π₁)
          (G[g] ○ (bpData F[_] G[_]).π₂))
      (by rw [←Category.assoc, BinaryProductData.lift_π₁,
              Category.assoc, BinaryProductData.lift_π₁,
              ←Category.assoc, ←F.map_comp])
      (by rw [←Category.assoc, BinaryProductData.lift_π₂,
              Category.assoc, BinaryProductData.lift_π₂,
              ←Category.assoc, ←G.map_comp])).symm

/-- Functor category `⟦C, D⟧` 的 binary product（逐點） -/
noncomputable instance FunctorCat_BinaryProduct (F G : ⟦C, D⟧.obj) :
    BinaryProduct (C := ⟦C, D⟧) F G :=
  BinaryProductData.toBinaryProduct (A := F) (B := G) {
    obj := pointwiseProdFunctor F G
    π₁ := {
      app X := (bpData F[X] G[X]).π₁
      naturality f := (bpData F[_] G[_]).lift_π₁ _ _ }
    π₂ := {
      app X := (bpData F[X] G[X]).π₂
      naturality f := (bpData F[_] G[_]).lift_π₂ _ _ }
    lift α β := {
      app X := (bpData F[X] G[X]).lift (α·X) (β·X)
      naturality {X Y} f := by
        let dX := bpData F[X] G[X]
        let dY := bpData F[Y] G[Y]
        have lhs : dY.lift (α·Y) (β·Y) ○ _ =
            dY.lift (F[f] ○ (α·X)) (G[f] ○ (β·X)) :=
          BinaryProductData.lift_unique dY _ _ _
            (by rw [←Category.assoc, dY.lift_π₁]; exact α.naturality f)
            (by rw [←Category.assoc, dY.lift_π₂]; exact β.naturality f)
        have rhs : (pointwiseProdFunctor F G).map f ○ dX.lift (α·X) (β·X) =
            dY.lift (F[f] ○ (α·X)) (G[f] ○ (β·X)) :=
          BinaryProductData.lift_unique dY _ _ _
            (by dsimp only [pointwiseProdFunctor]
                rw [←Category.assoc, dY.lift_π₁, Category.assoc, dX.lift_π₁])
            (by dsimp only [pointwiseProdFunctor]
                rw [←Category.assoc, dY.lift_π₂, Category.assoc, dX.lift_π₂])
        exact lhs.trans rhs.symm }
    lift_π₁ α β := by
      ext X
      exact (bpData F[X] G[X]).lift_π₁ (α·X) (β·X)
    lift_π₂ α β := by
      ext X
      exact (bpData F[X] G[X]).lift_π₂ (α·X) (β·X)
    lift_unique α β γ hk₁ hk₂ := by
      ext X
      exact (bpData F[X] G[X]).lift_unique (α·X) (β·X) (γ·X)
        (congrFun (congrArg NatTrans.app hk₁) X)
        (congrFun (congrArg NatTrans.app hk₂) X) }

end BinaryProduct

section BinaryCoproduct

variable [bc : ∀ (A B : D.obj), BinaryCoproduct (C := D) A B]

private noncomputable def bcData (A B : D.obj) := BinaryCoproduct.data (C := D) A B

/-- 逐點 binary coproduct functor -/
private noncomputable def pointwiseCoprodFunctor (F G : C ⥤ D) : C ⥤ D where
  obj X := (bcData F[X] G[X]).obj
  map {X Y} f :=
    (bcData F[X] G[X]).desc
      ((bcData F[Y] G[Y]).ι₁ ○ F[f])
      ((bcData F[Y] G[Y]).ι₂ ○ G[f])
  map_id X :=
    ((bcData F[X] G[X]).desc_unique _ _ (𝟙 _)
      (by simp [Functor.map_id]) (by simp [Functor.map_id])).symm
  map_comp f g := by
    -- map_comp (f : Y ⟶ Z) (g : X ⟶ Y) 在 Functor 中
    exact ((bcData F[_] G[_]).desc_unique _ _
      ((bcData F[_] G[_]).desc ((bcData F[_] G[_]).ι₁ ○ F[f])
          ((bcData F[_] G[_]).ι₂ ○ G[f]) ○
        (bcData F[_] G[_]).desc ((bcData F[_] G[_]).ι₁ ○ F[g])
          ((bcData F[_] G[_]).ι₂ ○ G[g]))
      (by rw [Category.assoc, BinaryCoproductData.desc_ι₁,
              ←Category.assoc, BinaryCoproductData.desc_ι₁,
              Category.assoc, ←F.map_comp])
      (by rw [Category.assoc, BinaryCoproductData.desc_ι₂,
              ←Category.assoc, BinaryCoproductData.desc_ι₂,
              Category.assoc, ←G.map_comp])).symm

/-- Functor category `⟦C, D⟧` 的 binary coproduct（逐點） -/
noncomputable instance FunctorCat_BinaryCoproduct (F G : ⟦C, D⟧.obj) :
    BinaryCoproduct (C := ⟦C, D⟧) F G :=
  BinaryCoproductData.toBinaryCoproduct (A := F) (B := G) {
    obj := pointwiseCoprodFunctor F G
    ι₁ := {
      app X := (bcData F[X] G[X]).ι₁
      naturality f := by
        exact ((bcData F[_] G[_]).desc_ι₁ _ _).symm }
    ι₂ := {
      app X := (bcData F[X] G[X]).ι₂
      naturality f := by
        exact ((bcData F[_] G[_]).desc_ι₂ _ _).symm }
    desc α β := {
      app X := (bcData F[X] G[X]).desc (α·X) (β·X)
      naturality {X Y} f := by
        let dX := bcData F[X] G[X]
        let dY := bcData F[Y] G[Y]
        have lhs : dY.desc (α·Y) (β·Y) ○ (pointwiseCoprodFunctor F G).map f =
            dX.desc ((α·Y) ○ F[f]) ((β·Y) ○ G[f]) :=
          BinaryCoproductData.desc_unique dX _ _ _
            (by dsimp only [pointwiseCoprodFunctor]
                rw [Category.assoc, dX.desc_ι₁, ←Category.assoc, dY.desc_ι₁])
            (by dsimp only [pointwiseCoprodFunctor]
                rw [Category.assoc, dX.desc_ι₂, ←Category.assoc, dY.desc_ι₂])
        have rhs : _ ○ dX.desc (α·X) (β·X) =
            dX.desc ((α·Y) ○ F[f]) ((β·Y) ○ G[f]) :=
          BinaryCoproductData.desc_unique dX _ _ _
            (by rw [Category.assoc, dX.desc_ι₁]; exact (α.naturality f).symm)
            (by rw [Category.assoc, dX.desc_ι₂]; exact (β.naturality f).symm)
        exact lhs.trans rhs.symm }
    desc_ι₁ α β := by
      ext X
      exact (bcData F[X] G[X]).desc_ι₁ (α·X) (β·X)
    desc_ι₂ α β := by
      ext X
      exact (bcData F[X] G[X]).desc_ι₂ (α·X) (β·X)
    desc_unique α β γ hk₁ hk₂ := by
      ext X
      exact (bcData F[X] G[X]).desc_unique (α·X) (β·X) (γ·X)
        (congrFun (congrArg NatTrans.app hk₁) X)
        (congrFun (congrArg NatTrans.app hk₂) X) }

end BinaryCoproduct

-- ─── Equalizer ──────────────────────────────────────────────────────────────────

section Equalizer

variable {F G : C ⥤ D} (α β : F ⇒ G) [ep : ∀ {A B : D.obj} (f g : A ⟶[D] B), Equalizer f g]

private noncomputable def eqData {A B : D.obj} (f g : A ⟶[D] B) : EqualizerData f g :=
  Equalizer.data f g

private lemma eqData_ext {A B : D.obj} {f g : A ⟶[D] B} {Z : D.obj}
    {k₁ k₂ : Z ⟶ (eqData f g).obj}
    (h : (eqData f g).π ○ k₁ = (eqData f g).π ○ k₂) : k₁ = k₂ := by
  have hc : f ○ ((eqData f g).π ○ k₂) = g ○ ((eqData f g).π ○ k₂) := by
    grind [(eqData f g).cond]
  have e₁ := (eqData f g).lift_unique ((eqData f g).π ○ k₂) hc k₁ h
  have e₂ := (eqData f g).lift_unique ((eqData f g).π ○ k₂) hc k₂ rfl
  exact e₁.trans e₂.symm

private lemma eqData_map_cond {X Y : C.obj} (f : X ⟶[C] Y) :
    (α·Y) ○ (F.map f ○ (eqData (α·X) (β·X)).π) =
    (β·Y) ○ (F.map f ○ (eqData (α·X) (β·X)).π) := by
  have nat_α := α.naturality f
  have nat_β := β.naturality f
  have c := (eqData (α·X) (β·X)).cond
  grind

/-- 逐點 equalizer functor：`E[X] = eq(α·X, β·X)` -/
private noncomputable def pointwiseEqualizerFunctor : C ⥤ D where
  obj X := (eqData (α·X) (β·X)).obj
  map f :=
    (eqData (α·_) (β·_)).lift
      (F.map f ○ (eqData (α·_) (β·_)).π) (eqData_map_cond α β f)
  map_id X := by
    symm
    exact (eqData (α·X) (β·X)).lift_unique _ _ (𝟙 _) (by simp)
  map_comp g f := by
    simp only [Functor.map_comp]
    symm
    apply (eqData (α·_) (β·_)).lift_unique
    have l₁ := (eqData (α·_) (β·_)).lift_π
      (F.map g ○ (eqData (α·_) (β·_)).π) (eqData_map_cond α β g)
    have l₂ := (eqData (α·_) (β·_)).lift_π
      (F.map f ○ (eqData (α·_) (β·_)).π) (eqData_map_cond α β f)
    grind

private noncomputable def mkEQπ : pointwiseEqualizerFunctor α β ⇒ F where
  app X := (eqData (α·X) (β·X)).π
  naturality m := by
    change (eqData (α·_) (β·_)).π ○ (pointwiseEqualizerFunctor α β).map m =
         F.map m ○ (eqData (α·_) (β·_)).π
    simp only [pointwiseEqualizerFunctor, (eqData _ _).lift_π]

private noncomputable def mkEQLift {H : C ⥤ D} (γ : H ⇒ F)
    (cond : ∀ X, (α·X) ○ (γ·X) = (β·X) ○ (γ·X)) :
    H ⇒ pointwiseEqualizerFunctor α β where
  app X := (eqData (α·X) (β·X)).lift (γ·X) (cond X)
  naturality {X Y} m := by
    apply eqData_ext (f := α·Y) (g := β·Y)
    have l₁ := (eqData (α·Y) (β·Y)).lift_π (γ·Y) (cond Y)
    have l₂ := (eqData (α·X) (β·X)).lift_π (γ·X) (cond X)
    have l₃ := (eqData (α·Y) (β·Y)).lift_π
      (F.map m ○ (eqData (α·X) (β·X)).π) (eqData_map_cond α β m)
    have nat := γ.naturality m
    change (eqData (α·Y) (β·Y)).π ○
          ((eqData (α·Y) (β·Y)).lift (γ·Y) (cond Y) ○ H[m]) =
         (eqData (α·Y) (β·Y)).π ○
          ((pointwiseEqualizerFunctor α β).map m ○
           (eqData (α·X) (β·X)).lift (γ·X) (cond X))
    change _ = (eqData (α·Y) (β·Y)).π ○
      ((eqData (α·Y) (β·Y)).lift (F.map m ○ (eqData (α·X) (β·X)).π)
        (eqData_map_cond α β m) ○
       (eqData (α·X) (β·X)).lift (γ·X) (cond X))
    grind

/-- Functor category `⟦C, D⟧` 的 equalizer（逐點） -/
noncomputable instance FunctorCat_Equalizer (F G : C ⥤ D) (α β : F ⇒ G)
    [ep : ∀ {A B : D.obj} (f g : A ⟶[D] B), Equalizer f g] :
    @Equalizer ⟦C, D⟧ F G α β :=
  (@EqualizerData.toEqualizer ⟦C, D⟧ F G α β {
    obj := pointwiseEqualizerFunctor α β
    π := mkEQπ α β
    cond := by ext X; exact (eqData (α·X) (β·X)).cond
    lift γ cond := mkEQLift α β γ (fun X => NatTrans.congr_app cond X)
    lift_π γ cond := by ext X; exact (eqData (α·X) (β·X)).lift_π _ _
    lift_unique γ cond k hk := by
      ext X
      exact (eqData (α·X) (β·X)).lift_unique _ _ (k·X) (NatTrans.congr_app hk X)
  })

end Equalizer

end CategoryTheory
