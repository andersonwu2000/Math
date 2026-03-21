import MATH.Category.Morphism.PreserveReflect

/-!
# Functor/Essentially.lean

Essentially surjective / essentially injective functor 及相關性質。

## 定義
- `Functor.EssentiallySurjective` — ∀ A, ∃ X, F[X] ≅ A
- `Functor.EssentiallyInjective` — F[X] ≅ F[Y] → X ≅ Y

## 定理
- `fullyFaithful_essentiallyInjective` — fully faithful ⟹ essentially injective
### `Functor.EssentiallySurjective`
- `.id` — identity functor 是 essentially surjective
- `.comp` — essentially surjective 在合成下封閉
- `.of_comp` — G ○ F essentially surjective ⟹ G essentially surjective
-/

namespace CategoryTheory

variable {C D : Category}

/-- Essentially surjective：∀ A, ∃ X, F[X] ≅ A -/
class Functor.EssentiallySurjective (F : C ⥤ D) : Prop where
  obj_surj : ∀ A : D.obj, ∃ X : C.obj, Nonempty (F[X] ≅[D] A)

/-- Essentially injective：F[X] ≅ F[Y] → X ≅ Y -/
class Functor.EssentiallyInjective (F : C ⥤ D) where
  obj_inj {X Y : C.obj} : (F[X] ≅[D] F[Y]) → Nonempty (X ≅[C] Y)

/-- Identity functor 是 essentially surjective -/
instance Functor.EssentiallySurjective.id :
    (𝟙[Cat] C).EssentiallySurjective where
  obj_surj A := ⟨A, ⟨Iso.refl⟩⟩

/-- Essentially surjective 在合成下封閉 -/
instance Functor.EssentiallySurjective.comp
    {E : Category} (F : C ⥤ D) (G : D ⥤ E)
    [F.EssentiallySurjective] [G.EssentiallySurjective] :
    (G ○[Cat] F).EssentiallySurjective where
  obj_surj A := by
    obtain ⟨B, ⟨iB⟩⟩ := EssentiallySurjective.obj_surj (F := G) A
    obtain ⟨X, ⟨iX⟩⟩ := EssentiallySurjective.obj_surj (F := F) B
    exact ⟨X, ⟨(Preserve.Iso G iX).trans iB⟩⟩

/-- G ○ F essentially surjective ⟹ G essentially surjective -/
lemma Functor.EssentiallySurjective.of_comp
    {E : Category} (F : C ⥤ D) (G : D ⥤ E)
    [h : (G ○[Cat] F).EssentiallySurjective] :
    G.EssentiallySurjective where
  obj_surj A := by
    obtain ⟨X, ⟨i⟩⟩ := h.obj_surj A
    exact ⟨F[X], ⟨i⟩⟩

/-- Fully faithful functor 是 essentially injective -/
noncomputable
instance fullyFaithful_essentiallyInjective
    (F : C ⥤ D) [F.FullyFaithful] : F.EssentiallyInjective where
  obj_inj i := ⟨Reflect.Iso F i⟩

/-- `G ○ F ≅ H ○ F → G ≅ H`（fully faithful + essentially surjective） -/
noncomputable
def Reflect.NatIso' {G H : D ⥤ E} (F : C ⥤ D)
    [F.FullyFaithful] [F.EssentiallySurjective]
    (α : G ○[Cat] F ≅ H ○[Cat] F) : G ≅ H := by
  -- 對每個 d : D.obj，選擇 c_d 與 iso i_d : F[c_d] ≅ d
  have surj := Functor.EssentiallySurjective.obj_surj (F := F)
  let c (d : D.obj) : C.obj := (surj d).choose
  let i (d : D.obj) : F[c d] ≅ d := ((surj d).choose_spec).some
  -- 定義逐點的態射
  let β (d : D.obj) : G[d] ⟶[E] H[d] :=
    H[(i d).hom] ○ α.hom·(c d) ○ G[(i d).inv]
  let γ (d : D.obj) : H[d] ⟶[E] G[d] :=
    G[(i d).hom] ○ α.inv·(c d) ○ H[(i d).inv]
  -- 輔助引理：NatIso 分量的逆
  have α_inv_hom (x : C.obj) : α.inv·x ○ α.hom·x = 𝟙 :=
    congrFun (congrArg NatTrans.app α.inv_hom_id) x
  have α_hom_inv (x : C.obj) : α.hom·x ○ α.inv·x = 𝟙 :=
    congrFun (congrArg NatTrans.app α.hom_inv_id) x
  -- 正規化 α_inv_hom / α_hom_inv 的 RHS
  simp only [Cat, Function.comp] at α_inv_hom α_hom_inv
  -- β 與 γ 互逆
  have inv_βγ (d : D.obj) : γ d ○ β d = 𝟙 := by
    simp only [β, γ, Category.assoc, Cat, Function.comp]
    -- 用 ← E.assoc 配對後消去
    erw [← E.assoc (H.map (i d).inv) (H.map (i d).hom),
         ← Functor.map_comp H (i d).inv (i d).hom, Iso.inv_hom_id, Functor.map_id,
         Category.comp_id]
    erw [← E.assoc (α.inv·(c d)) (α.hom·(c d)), α_inv_hom, Category.comp_id]
    rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  have inv_γβ (d : D.obj) : β d ○ γ d = 𝟙 := by
    simp only [β, γ, Category.assoc, Cat, Function.comp]
    erw [← E.assoc (G.map (i d).inv) (G.map (i d).hom),
         ← Functor.map_comp G (i d).inv (i d).hom, Iso.inv_hom_id, Functor.map_id,
         Category.comp_id]
    erw [← E.assoc (α.hom·(c d)) (α.inv·(c d)), α_hom_inv, Category.comp_id]
    rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  -- naturality of β
  have nat_β {d₁ d₂ : D.obj} (f : d₁ ⟶ d₂) :
      β d₂ ○ G[f] = H[f] ○ β d₁ := by
    simp only [β]
    let h := F.preimage ((i d₂).inv ○ f ○ (i d₁).hom)
    have hF : F[h] = (i d₂).inv ○ f ○ (i d₁).hom := F.map_preimage_id _
    have nat_h := α.hom.naturality h
    simp only [Cat, Function.comp] at nat_h
    simp only [Category.assoc, Cat, Function.comp]
    rw [← Functor.map_comp G (i d₂).inv f]
    have eq1 : (i d₂).inv ○ f = F[h] ○ (i d₁).inv := by rw [hF]; grind
    rw [eq1, Functor.map_comp]
    -- 目標：H[i₂.hom] ○ (α.hom·c₂ ○ (G[F[h]] ○ G[i₁.inv]))
    --     = H[f] ○ (H[i₁.hom] ○ (α.hom·c₁ ○ G[i₁.inv]))
    -- 配對 α.hom·c₂ 與 G[F[h]] 用 nat_h
    erw [← E.assoc (α.hom·(c d₂)) (G.map (F.map h)), nat_h, Category.assoc]
    -- 配對 H[i₂.hom] 與 H[F[h]] 用 erw + ← E.assoc + map_comp
    erw [← E.assoc (H.map (i d₂).hom) (H.map (F.map h)),
         ← Functor.map_comp H (i d₂).hom (F.map h)]
    have eq2 : (i d₂).hom ○ F[h] = f ○ (i d₁).hom := by rw [hF]; grind
    rw [eq2, Functor.map_comp, Category.assoc]
  -- naturality of γ：利用 β 的 naturality 和逆對消去推導
  have nat_γ {d₁ d₂ : D.obj} (f : d₁ ⟶ d₂) :
      γ d₂ ○ H[f] = G[f] ○ γ d₁ := by
    have h1 : γ d₂ ○ (H[f] ○ β d₁) = G[f] := by
      rw [← nat_β f]
      grind
    calc γ d₂ ○ H[f]
        _ = γ d₂ ○ H[f] ○ (β d₁ ○ γ d₁) := by rw [inv_γβ]; simp
        _ = (γ d₂ ○ (H[f] ○ β d₁)) ○ γ d₁ := by simp
        _ = G[f] ○ γ d₁ := by rw [h1]
  exact {
    hom := { app := β, naturality := nat_β }
    inv := { app := γ, naturality := nat_γ }
    hom_inv_id := by ext d; exact inv_γβ d
    inv_hom_id := by ext d; exact inv_βγ d }

end CategoryTheory
