import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Essentially

/-!
# Adjunction/Equivalence.lean

Category equivalence、adjoint equivalence
與 fully faithful + essentially surjective 的等價。

## 定義
- `CatEquiv C D` — category equivalence（F、G、η : 𝟙 ≅ GF、ρ : FG ≅ 𝟙）
- `AdjointEquivalence F G` — adjoint equivalence（η、ε 為 nat iso + triangle identity）

## 定理
### `AdjointEquivalence`
- `.toUnits` / `.toCatEquiv` — 轉換為 `Units` / `CatEquiv`
- `.essentiallySurjective` — adj equiv ⟹ essentially surjective
- `.fullyFaithful` — adj equiv ⟹ fully faithful
- `.ofCatEquiv` — cat equiv ⟹ adj equiv
- `.ofFullyFaithful` — fully faithful + ess surj ⟹ adj equiv
-/

namespace CategoryTheory

-- ─── CatEquiv ────────────────────────────────────────────────────────────────

/-- Category equivalence：`F`、`G`、`η : 1_C ≅ GF`、`ρ : FG ≅ 1_D` -/
structure CatEquiv (C D : Category) where
  F : C ⥤ D
  G : D ⥤ C
  η : 𝟙[Cat] C ≅ G ○[Cat] F
  ρ : F ○[Cat] G ≅ 𝟙[Cat] D

namespace CatEquiv

/-- Reflexivity -/
@[refl]
def refl : CatEquiv C C where
  F := 𝟙[Cat] C
  G := 𝟙[Cat] C
  η := Iso.refl
  ρ := Iso.refl

/-- Symmetry -/
@[symm]
def symm (e : CatEquiv C D) : CatEquiv D C where
  F := e.G
  G := e.F
  η := e.ρ.symm
  ρ := e.η.symm

end CatEquiv

-- ─── AdjointEquivalence ──────────────────────────────────────────────────────

/-- Adjoint equivalence：`η`、`ε` 為 natural isomorphism，滿足 triangle identity -/
structure AdjointEquivalence (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟙[Cat] C ≅ G ○[Cat] F
  ε : F ○[Cat] G ≅ 𝟙[Cat] D
  left_triangle  : 𝟙[⟦C, D⟧] F = (ε.hom ◫ F) ○[⟦C, D⟧] (F ◫ η.hom)
  right_triangle : 𝟙[⟦D, C⟧] G = (G ◫ ε.hom) ○[⟦D, C⟧] (η.hom ◫ G)

namespace AdjointEquivalence

variable {C D : Category} {F : C ⥤ D} {G : D ⥤ C}

def toUnits (e : AdjointEquivalence F G) : Units F G where
  η := e.η.hom
  ε := e.ε.hom
  left_triangle  := e.left_triangle
  right_triangle := e.right_triangle

/-- Adjoint equivalence 給出 category equivalence -/
def toCatEquiv (e : AdjointEquivalence F G) : CatEquiv C D where
  F := F
  G := G
  η := e.η
  ρ := e.ε

/-- ε·F[X] ○ F[η·X] = 𝟙（左 triangle identity 消去） -/
lemma ε_triangle (e : AdjointEquivalence F G) (X : C.obj) :
    e.ε.hom·F[X] ○ F[e.η.hom·X] = 𝟙 := by
  simpa using e.toUnits.left_tri_id (f := 𝟙 F[X])

/-- G[ε·A] ○ η·G[A] = 𝟙（右 triangle identity 消去） -/
lemma η_triangle (e : AdjointEquivalence F G) (A : D.obj) :
    G[e.ε.hom·A] ○ e.η.hom·G[A] = 𝟙 := by
  simpa using e.toUnits.right_tri_id (f := 𝟙 G[A])

-- ─── 方向 (2) → (3) ─────────────────────────────────────────────────────────

/-- Adjoint equivalence 蘊含 essentially surjective -/
instance essentiallySurjective (e : AdjointEquivalence F G) :
    F.EssentiallySurjective where
  obj_surj A := ⟨G[A], ⟨{
    hom := e.ε.hom·A
    inv := e.ε.inv·A
    hom_inv_id := NatIso.hom_inv_id_app e.ε A
    inv_hom_id := NatIso.inv_hom_id_app e.ε A}⟩⟩

/-- 輔助 lemma：F[η.inv·Y] = ε.hom·F[Y] -/
private lemma map_η_inv_eq_ε (e : AdjointEquivalence F G) (Y : C.obj) :
    F[e.η.inv·Y] = e.ε.hom·F[Y] := by
  have hFηY_epi : (F[e.η.hom·Y]).IsEpi := inferInstance
  -- 兩者都是左逆：
  have h1 : F[e.η.inv·Y] ○ F[e.η.hom·Y] = 𝟙 := by
    simp only [← F.map_comp, NatIso.inv_hom_id_app e.η Y, Functor.map_id]
  have h2 : e.ε.hom·F[Y] ○ F[e.η.hom·Y] = 𝟙 := e.ε_triangle Y
  exact hFηY_epi.left_uni (h1.trans h2.symm)

/-- 輔助 lemma：G[ε.inv·A] = η.hom·G[A]（map_η_inv_eq_ε 的對偶） -/
private lemma map_ε_inv_eq_η (e : AdjointEquivalence F G) (A : D.obj) :
    G[e.ε.inv·A] = e.η.hom·G[A] := by
  have hGεA_mono : (G[e.ε.hom·A]).IsMono := inferInstance
  -- 兩者都是右逆：
  have h1 : G[e.ε.hom·A] ○ G[e.ε.inv·A] = 𝟙 := by
    simp only [← G.map_comp, NatIso.hom_inv_id_app e.ε A, Functor.map_id]
  have h2 : G[e.ε.hom·A] ○ e.η.hom·G[A] = 𝟙 := e.η_triangle A
  exact hGεA_mono.right_uni (h1.trans h2.symm)

/-- Adjoint equivalence 蘊含 fully faithful -/
instance fullyFaithful (e : AdjointEquivalence F G) :
    F.FullyFaithful where
  map_bijective {X Y} := ⟨
    -- Faithful：η·Y 是 monomorphism
    fun {f g} heq => by
      have hηY_mono : (e.η.hom·Y).IsMono := inferInstance
      apply hηY_mono.right_uni
      have hf := e.η.hom.naturality f
      have hg := e.η.hom.naturality g
      simp_all,
    -- Full：逆映射為 η.inv·Y ○ G[h] ○ η.hom·X
    fun h => ⟨e.η.inv·Y ○ G[h] ○ e.η.hom·X, by
      change F[e.η.inv·Y ○ G[h] ○ e.η.hom·X] = h
      rw [F.map_comp, F.map_comp, map_η_inv_eq_ε e Y]
      exact (toUnits e).flat_sharp_id⟩⟩

-- ─── 方向 (1) → (2) ─────────────────────────────────────────────────────────

/-- 修正的餘單位自然變換：ε'·A = ρ·A ○ F[η⁻¹·G[A]] ○ ρ⁻¹·F[G[A]] -/
private def ofCatEquiv_ε'_nat (e : CatEquiv C D) : e.F ○[Cat] e.G ⇒ 𝟙[Cat] D where
  app A := e.ρ.hom·A ○ e.F[e.η.inv·(e.G[A])] ○ e.ρ.inv·(e.F[e.G[A]])
  naturality {A B} f := by
    have h1 := e.ρ.inv.naturality (e.F[e.G[f]])
    have h2 := e.η.inv.naturality (e.G[f])
    have h3 := e.ρ.hom.naturality f
    simp only [Cat.eq_1, Function.comp_apply, id_eq] at *
    grind

@[reducible]
private def ofCatEquiv_ε'_iso (e : CatEquiv C D) (A : D.obj) :
    ((ofCatEquiv_ε'_nat e)·A).IsIso where
  inv := e.ρ.hom·(e.F[e.G[A]]) ○ e.F[e.η.hom·(e.G[A])] ○ e.ρ.inv·A
  hom_inv_id :=
    Whisker.triple_cancel (NatIso.inv_hom_id_app e.ρ _)
      ((e.F.map_comp _ _).symm.trans
        ((congrArg e.F.map (NatIso.inv_hom_id_app e.η _)).trans (e.F.map_id _)))
      (NatIso.hom_inv_id_app e.ρ _)
  inv_hom_id :=
    Whisker.triple_cancel (NatIso.inv_hom_id_app e.ρ _)
      ((e.F.map_comp _ _).symm.trans
        ((congrArg e.F.map (NatIso.hom_inv_id_app e.η _)).trans (e.F.map_id _)))
      (NatIso.hom_inv_id_app e.ρ _)

/-- 左 triangle identity 的分量版本：ε'·F[X] ○ F[η·X] = 𝟙 -/
private lemma ofCatEquiv_left_tri (e : CatEquiv C D) (X : C.obj) :
    (ofCatEquiv_ε'_nat e)·(e.F[X]) ○ e.F[e.η.hom·X] = 𝟙 := by
  simp only [ofCatEquiv_ε'_nat]
  have h1 : e.ρ.inv·(e.F[e.G[e.F[X]]]) ○ e.F[e.η.hom·X] =
            e.F[e.G[e.F[e.η.hom·X]]] ○ e.ρ.inv·(e.F[X]) := by
    simpa using e.ρ.inv.naturality (e.F[e.η.hom·X])
  have h2 : e.η.inv·(e.G[e.F[X]]) ○ e.G[e.F[e.η.hom·X]] = 𝟙 := by
    have := e.η.inv.naturality (e.η.hom·X)
    simpa using this.trans (NatIso.hom_inv_id_app e.η X)
  simp only [Category.assoc]
  have h3 : e.F[e.η.inv·(e.G[e.F[X]])] ○ e.F[e.G[e.F[e.η.hom·X]]] =
            e.F[𝟙] :=
    (e.F.map_comp _ _).symm.trans (congrArg e.F.map h2)
  have h_h1 := congrArg (e.ρ.hom·(e.F[X]) ○ ·)
                 (congrArg (e.F[e.η.inv·(e.G[e.F[X]])] ○ ·) h1)
  have h4 : e.F[e.η.inv·(e.G[e.F[X]])] ○ (e.F[e.G[e.F[e.η.hom·X]]] ○ e.ρ.inv·(e.F[X])) =
            e.ρ.inv·(e.F[X]) :=
    (D.assoc _ _ _).symm.trans
      ((congrArg (· ○ _) (h3.trans (e.F.map_id _))).trans (D.comp_id _))
  exact h_h1.trans ((congrArg (e.ρ.hom·(e.F[X]) ○ ·) h4).trans (NatIso.hom_inv_id_app e.ρ _))

/-- 右 triangle identity 的分量版本：G[ε'·A] ○ η·G[A] = 𝟙 -/
private lemma ofCatEquiv_right_tri (e : CatEquiv C D) (A : D.obj) :
    e.G[(ofCatEquiv_ε'_nat e)·A] ○ e.η.hom·(e.G[A]) = 𝟙 := by
  have hFr : e.F[e.G[(ofCatEquiv_ε'_nat e)·A] ○ e.η.hom·(e.G[A])] = 𝟙 := by
    rw [e.F.map_comp]
    have hnat : (ofCatEquiv_ε'_nat e)·A ○ e.F[e.G[(ofCatEquiv_ε'_nat e)·A]] =
                (ofCatEquiv_ε'_nat e)·A ○ (ofCatEquiv_ε'_nat e)·(e.F[e.G[A]]) := by
      simpa using (ofCatEquiv_ε'_nat e).naturality ((ofCatEquiv_ε'_nat e)·A)
    have hmono : ((ofCatEquiv_ε'_nat e)·A).IsMono :=
      haveI := ofCatEquiv_ε'_iso e A; inferInstance
    have hFGε : e.F[e.G[(ofCatEquiv_ε'_nat e)·A]] =
                (ofCatEquiv_ε'_nat e)·(e.F[e.G[A]]) := hmono.right_uni hnat
    rw [hFGε]; exact ofCatEquiv_left_tri e (e.G[A])
  have hηGA_mono : (e.η.hom·(e.G[A])).IsMono := inferInstance
  apply hηGA_mono.right_uni
  have hnat2 := e.η.hom.naturality (e.G[(ofCatEquiv_ε'_nat e)·A] ○ e.η.hom·(e.G[A]))
  simp only [Cat.eq_1, Function.comp_apply, id_eq] at hnat2
  aesop_cat

/-- 從 category equivalence 構造 adjoint equivalence -/
def ofCatEquiv (e : CatEquiv C D) :
    AdjointEquivalence e.F e.G := by
  let ε'_nat := ofCatEquiv_ε'_nat e
  let ε' : e.F ○[Cat] e.G ≅ 𝟙[Cat] D :=
    NatIso.ofComponents ε'_nat (ofCatEquiv_ε'_iso e)
  exact {
    η := e.η
    ε := ε'
    left_triangle := by
      ext X
      simpa using (ofCatEquiv_left_tri e X).symm
    right_triangle := by
      ext A
      simpa using (ofCatEquiv_right_tri e A).symm}

-- ─── 方向 (3) → (2) ─────────────────────────────────────────────────────────

section OfFullyFaithful

variable (F : C ⥤ D) [hFF : F.FullyFaithful] [hES : F.EssentiallySurjective]

/-- 選取右伴隨函子的物件 -/
noncomputable def right_adj_obj (A : D.obj) : C.obj :=
  (hES.obj_surj A).choose

/-- 選取同構 `F[right_adj_obj F A] ≅ A` -/
noncomputable def right_adj_iso (A : D.obj) : F[right_adj_obj F A] ≅ A :=
  (hES.obj_surj A).choose_spec.some

/-- 構造右伴隨函子 G : D ⥤ C，其中 G[A] 為選定的原像物件 -/
noncomputable def make_right_adj : D ⥤ C where
  obj := right_adj_obj F
  map {A B} f :=
    F.preimage ((right_adj_iso F B).inv ○ f ○ (right_adj_iso F A).hom)
  map_id A := by
    apply F.map_injective
    simp only [Functor.map_id, F.map_preimage_id]
    rw [Category.comp_id, (right_adj_iso F A).inv_hom_id]
  map_comp {A B C_} g f := by
    apply F.map_injective
    have hA : (right_adj_iso F A).hom ○[D]
        ((right_adj_iso F A).inv ○[D] (f ○[D] (right_adj_iso F C_).hom)) =
        f ○[D] (right_adj_iso F C_).hom := by grind
    simp only [Functor.map_comp, F.map_preimage_id, Category.assoc, hA]

/-- 從全忠實 + 本質滿射構造伴隨等價 -/
noncomputable def ofFullyFaithful :
    AdjointEquivalence F (make_right_adj F) := by
  let G := make_right_adj F
  let εi (A : D.obj) := right_adj_iso F A
  -- HomEquiv：(F[X] ⟶ A) ≅ (X ⟶ G[A])，透過 f ↦ F.preimage(εi_A⁻¹ ∘ f)
  let hEquiv : HomEquiv F G := {
    equiv X A := {
      hom f := F.preimage ((εi A).inv ○ f)
      inv g := (εi A).hom ○ F[g]
      hom_inv_id := by
        ext g
        simp only [Function.comp_apply, id_eq]
        change F.preimage ((right_adj_iso F A).inv ○ (right_adj_iso F A).hom ○ F[g]) = g
        simp only [← Category.assoc, (right_adj_iso F A).inv_hom_id, Category.comp_id,
                   F.preimage_map_id]
      inv_hom_id := by
        ext f
        simp only [Function.comp_apply, id_eq]
        change (right_adj_iso F A).hom ○ F[F.preimage ((right_adj_iso F A).inv ○ f)] = f
        rw [F.map_preimage_id, ← Category.assoc, (right_adj_iso F A).hom_inv_id,
            Category.comp_id]}
    naturality_left {X Y A} f g := by
      apply F.map_injective
      simp only [Functor.map_comp, F.map_preimage_id, G, make_right_adj,
                 right_adj_obj, right_adj_iso, ← Category.assoc]
    naturality_right {X A B} f k := by
      apply F.map_injective
      simp only [Functor.map_comp, F.map_preimage_id, G, make_right_adj,
                 right_adj_obj, Category.assoc]
      grind}
  let φ := Adjunction.ofHomEquiv hEquiv
  -- φ.η·X = F.preimage(εi(FX)⁻¹) 是同構
  have η_comp_iso (X : C.obj) : (φ.η·X).IsIso := by
    have hval : F[φ.η·X] = (εi (F[X])).inv := by
      change F[F.preimage ((εi (F[X])).inv ○ 𝟙 F[X])] = (εi (F[X])).inv
      rw [Category.id_comp, F.map_preimage_id]
    have hFη : (F[φ.η·X]).IsIso := {
      inv := (εi (F[X])).hom
      inv_hom_id := by rw [hval]; simp
      hom_inv_id := by rw [hval]; simp}
    exact Reflect.IsIso F (φ.η·X)
  -- φ.ε·A = (εi A).hom 是同構
  have ε_comp_iso (A : D.obj) : (φ.ε·A).IsIso := by
    have hε : φ.ε·A = (εi A).hom := by
      change (εi A).hom ○ F[𝟙 G[A]] = (εi A).hom
      exact (congrArg ((εi A).hom ○ ·) (F.map_id _)).trans (D.id_comp (εi A).hom)
    rw [hε]
    exact { inv := (εi A).inv }
  exact {
    η := NatIso.ofComponents φ.η η_comp_iso
    ε := NatIso.ofComponents φ.ε ε_comp_iso
    left_triangle := φ.Units.left_triangle
    right_triangle := φ.Units.right_triangle}

end OfFullyFaithful

end AdjointEquivalence
end CategoryTheory
