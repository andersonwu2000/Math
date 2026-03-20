import MATH.Category.Yoneda
import MATH.Category.UniversalProperty
import MATH.Category.NatTrans.Horizontal

/-!
# Adjunction/Basic.lean

Adjunction 及其等價形式。

## 定義
- `Adjunction` — adjunction `F ⊣ G := Hom[Fᵒᵖ–, –] ≅ Hom[–, G–]`
- `HomEquiv` — 逐 hom-set isomorphism + naturality
- `HomMate` — mate condition
- `Units` — unit η、counit ε + triangle identity

## 定理
### `HomEquiv`
- `.naturality_right_symm` — naturality（逆方向，右變量）
- `.naturality_left_symm` — naturality（逆方向，左變量）

### `HomMate`
- `.HomEquiv` — `HomMate` ⟹ `HomEquiv`
### `HomEquiv`
- `.HomMate` — `HomEquiv` ⟹ `HomMate`

### `Universal`
- `.leftAdjoint` — 從 universal property 族構造左 adjoint
### `CoUniversal`
- `.rightAdjoint` — 從 couniversal property 族構造右 adjoint

### `Adjunction`
- `.ofHomEquiv` — 從 `HomEquiv` 構造
- `.ofHomMate` — 從 `HomMate` 構造
- `.ofUnits` — 從 `Units` 構造
- `.ofUniversal` — 從 universal property 構造
- `.ofCoUniversal` — 從 couniversal property 構造
- `.Universal` — 伴隨給出 universal property
- `.CoUniversal` — 伴隨給出 couniversal property
- `.mate_sharp` / `.mate_flat` — mate 條件
- `.hom_right_η` — `φ♯f = G[f] ○ φ.η·X`
- `.inv_left_ε` — `φ♭f = φ.ε·A ○ F[f]`
-/

namespace CategoryTheory

/-- Adjunction `F ⊣ G := Hom[Fᵒᵖ–, –] ≅ Hom[–, G–]` -/
@[simp]
def Adjunction (F : C ⥤ D) (G : D ⥤ C) :=
  Hom[Fᵒᵖ–, –] ≅ Hom[–, G–]

notation F " ⊣[" C ", " D "] " G => @Adjunction C D F G
notation F " ⊣ " G => Adjunction F G

section
variable (φ : F ⊣ G)

/-- Sharp transposition `φ♯f : X ⟶ G[A]` -/
abbrev Adjunction.sharp (f : F[X] ⟶ A) : X ⟶ G[A] :=
  (φ·(X, A) : _ → _) f

/-- Flat transposition `φ♭f : F[X] ⟶ A` -/
abbrev Adjunction.flat (f : X ⟶ G[A]) : F[X] ⟶ A :=
  (φ⁻¹·(X, A) : _ → _) f

notation φ "♯" f:80 => Adjunction.sharp φ f
notation φ "♭" f:80 => Adjunction.flat φ f

end

section HomEquiv

/-- `HomEquiv`：逐 hom-set isomorphism `(F[X] ⟶ A) ≅ (X ⟶ G[A])` 加 naturality -/
structure HomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  equiv X A : (F[X] ⟶ A) ≅[Types] (X ⟶ G[A])
  naturality_left {X Y A} (f : Y ⟶ X) (g : F[X] ⟶ A) :
    (equiv Y A).hom (g ○ Fᵒᵖ[f]) = f.op ○ (equiv X A).hom g
  naturality_right {X A B} (f : F[X] ⟶ A) (g : A ⟶ B) :
    (equiv X B).hom (g ○ f) = G[g] ○ (equiv X A).hom f

attribute [simp, grind =, grind _=_] HomEquiv.naturality_left HomEquiv.naturality_right

@[simp]
lemma HomEquiv.naturality_right_symm
  (φ : HomEquiv F G) (f : X ⟶ G[A]) (g : A ⟶ B) :
  (φ.equiv X B).inv (G[g] ○ f) = g ○ (φ.equiv X A).inv f := by simp

@[simp]
lemma HomEquiv.naturality_left_symm
  (φ : HomEquiv F G) (f : Y ⟶ X) (g : X ⟶ G[A]) :
  (φ.equiv Y A).inv (g ○ f) = Fᵒᵖ[f] ○ (φ.equiv X A).inv g := by
  have h := φ.naturality_left f ((φ.equiv X A).inv g)
  simp at h
  simpa using h.symm

def Adjunction.ofHomEquiv
  (φ : HomEquiv F G) : F ⊣ G := NatIso.ofComponents
    ⟨fun (X, Y) => (φ.equiv X.op Y).hom, by
      simp only [ProductCat_obj, ProductCat_hom, Hom.eq_1,
        Function.comp_def, Prod.forall]
      intro X A Y B f g
      ext h
      rw [←φ.naturality_left f h]
      simp⟩
    fun (X, Y) => (φ.equiv X.op Y).IsIso

variable (φ : F ⊣ G)

abbrev Adjunction.HomEquiv : HomEquiv F G where
    equiv X Y := {hom := φ·(X, Y), inv := φ⁻¹·(X, Y)}
    naturality_left {X Y A} f g := by
      let h := φ.hom·(–, A).naturality f
      simpa using (congrFun h) g
    naturality_right {X A B} f g := by
      let h := φ.hom·(X, –).naturality g
      simpa using (congrFun h) f

end HomEquiv

section HomMate

/-- `HomMate`：mate condition `k ○ f = g ○ F[h] ↔ G[k] ○ φ(f) = φ(g) ○ h` -/
structure HomMate (F : C ⥤ D) (G : D ⥤ C) where
  equiv X A : (F[X] ⟶ A) ≅[Types] (X ⟶ G[A])
  mate (f g) (h : X ⟶ Y) (k : A ⟶ B) :
    k ○ f = g ○ F[h] ↔
    G[k] ○ (equiv X A).hom f = (equiv Y B).hom g ○ h

variable {F : C ⥤ D} {G : D ⥤ C}

def HomMate.HomEquiv (φ : HomMate F G) : HomEquiv F G where
  equiv := φ.equiv
  naturality_left := by
    intro X A B h f
    have := φ.mate (f ○ F[h]) f h (𝟙 B)
    simp_all
  naturality_right := by
    intro X A B f k
    have := φ.mate f (k ○ f) (𝟙 X) k
    simp_all

def Adjunction.ofHomMate (φ : HomMate F G) : F ⊣ G :=
  Adjunction.ofHomEquiv φ.HomEquiv

def HomEquiv.HomMate (φ : HomEquiv F G) : HomMate F G where
  equiv := φ.equiv
  mate {X Y A B} f g h k := ⟨
    fun p => by
      rw [← φ.naturality_right, p];
      simpa using φ.naturality_left h g,
    fun p => by
    let p' := congrArg (φ.equiv X _).inv p
    let q := congrArg (φ.equiv X _).inv (φ.naturality_right f k)
    simp [-naturality_right] at p' q
    simp_all⟩

variable (φ : F ⊣ G)

abbrev Adjunction.HomMate : HomMate F G :=
  φ.HomEquiv.HomMate

/-- `k ○ f = g ○ F[h] ↔ G[k] ○ (φ♯f) = (φ♯g) ○ h` -/
lemma Adjunction.mate_sharp
  (f g) (h : X ⟶ Y) (k : A ⟶ B) :
  k ○ f = g ○ F[h]  ↔  G[k] ○ (φ ♯ f) = (φ ♯ g) ○ h :=
    φ.HomMate.mate _ _ _ _

/-- `k ○ (φ♭f) = (φ♭g) ○ F[h] ↔ G[k] ○ f = g ○ h` -/
lemma Adjunction.mate_flat
  (f g) (h : X ⟶ Y) (k : A ⟶ B) :
  k ○ (φ ♭ f) = (φ ♭ g) ○ F[h]  ↔  G[k] ○ f = g ○ h := by
    have := φ.mate_sharp (φ ♭ f) (φ ♭ g)
    simp_all

end HomMate

section Units

/-- `Units`：unit `η`、counit `ε`、triangle identity -/
structure Units (F : C ⥤ D) (G : D ⥤ C) where
  η : 𝟙[Cat] C ⇒ G ○[Cat] F
  ε : F ○[Cat] G ⇒ 𝟙[Cat] D
  left_triangle  : 𝟙[⟦C, D⟧] F = (ε ◫ F) ○ (F ◫ η)
  right_triangle : 𝟙[⟦D, C⟧] G = (G ◫ ε) ○ (η ◫ G)

attribute [simp] Units.left_triangle Units.right_triangle

/-- `f ○ ε·F[X] ○ F[η·X] = f` -/
@[simp]
lemma Units.left_tri_id
  (u : Units F G) {f : F[X] ⟶ Y} :
  f ○ u.ε·F[X] ○ F[u.η·X] = f := by
    have q := congrFun (congrArg NatTrans.app u.left_triangle) X
    simp at q; simp [←q]

/-- `G[ε·Y] ○ η·G[Y] ○ f = f` -/
@[simp]
lemma Units.right_tri_id
  (u : Units F G) {f : X ⟶ G[Y]} :
  G[u.ε·Y] ○ u.η·G[Y] ○ f = f := by
    have q := congrFun (congrArg NatTrans.app u.right_triangle) Y
    simp at q; simp [←Category.assoc, ←q]

/-- `ε·Y ○ F[G[f]] ○ F[η·X] = f` -/
@[simp]
lemma Units.flat_sharp_id
  (u : Units F G) {f : F[X] ⟶ Y} :
  u.ε·Y ○ F[G[f]] ○ F[u.η·X] = f := by
    rw [← Category.assoc]
    have h := u.ε.naturality f
    simp at h
    simp [h]
    simpa using Units.left_tri_id u

/-- `G[ε·A] ○ G[F[g]] ○ η·X = g` -/
@[simp]
lemma Units.sharp_flat_id
  (u : Units F G) {g : X ⟶ G[A]} :
  G[u.ε·A] ○ G[F[g]] ○ u.η·X = g := by
    erw [← u.η.naturality g]
    simpa using Units.right_tri_id u

/-- 從 `Units` 構造 adjunction -/
def Adjunction.ofUnits
  (u : Units F G) : F ⊣ G where
  hom := ⟨fun (X, Y) f => G[f] ○ u.η·X, by
    simp only [ProductCat_obj, ProductCat_hom, Hom.eq_1, Cat.eq_1,
      Function.comp_def, Prod.forall]
    intro _ _ _ _ f g; ext
    simp only [Functor.map_comp, Category.assoc]
    repeat apply Whisker.left_cancel
    exact (u.η.naturality f).symm⟩
  inv := ⟨fun (A, B) => fun (f : A.op ⟶ G[B]) => u.ε·B ○ F[f], by
    simp only [ProductCat_obj, ProductCat_hom, Hom.eq_1, Cat.eq_1,
      Function.comp_def, Functor.map_comp, Category.assoc, Prod.forall]
    intro _ _ _ _ f g; ext
    repeat rw [←Category.assoc]
    repeat apply Whisker.right_cancel
    exact u.ε.naturality g⟩
  hom_inv_id := by
    ext ⟨X, A⟩ f
    simp only [Function.comp_def, Functor.map_comp, Category.assoc, id_eq]
    exact Units.sharp_flat_id u
  inv_hom_id := by
    ext ⟨X, A⟩ f
    simp only [Function.comp_def, Functor.map_comp, id_eq]
    exact Units.flat_sharp_id u

variable (φ : F ⊣[C, D] G)

/-- Unit：`φ.η·X = φ♯𝟙[F[X]]` -/
abbrev Adjunction.η : 𝟙[Cat] C ⇒ G ○[Cat] F where
  app X : X ⟶ G[F[X]] := φ ♯ 𝟙 F[X]
  naturality {X Y} h := by
    dsimp
    rw [←φ.HomEquiv.naturality_left, ←φ.HomEquiv.naturality_right]
    simp

/-- Counit：`φ.ε·A = φ♭𝟙[G[A]]` -/
abbrev Adjunction.ε : F ○[Cat] G ⇒ 𝟙[Cat] D where
  app A : F[G[A]] ⟶ A := φ ♭ 𝟙 G[A]
  naturality {A B} h := by
    dsimp
    rw [←φ.HomEquiv.naturality_left_symm, ←φ.HomEquiv.naturality_right_symm]
    simp

/-- `φ♯f = G[f] ○ φ.η·X` -/
lemma Adjunction.hom_right_η (f : F[X] ⟶ A) :
  φ ♯ f = G[f] ○ φ.η·X := by
    simpa using φ.HomEquiv.naturality_right (𝟙 F[X]) f

/-- `φ♭f = φ.ε·A ○ F[f]` -/
lemma Adjunction.inv_left_ε (f : X ⟶ G[A]) :
  φ ♭ f = φ.ε·A ○ F[f] := by
    simpa using φ.HomEquiv.naturality_left_symm f (𝟙 G[A])

abbrev Adjunction.Units : Units F G where
    η := φ.η
    ε := φ.ε
    left_triangle  := by
      ext X
      simpa using φ.inv_left_ε (φ ♯ 𝟙F[X])
    right_triangle := by
      ext A
      simpa using φ.hom_right_η (φ ♭ 𝟙G[A])

end Units

section UniversalProperty

/-- 從 universal property 族構造左 adjoint -/
abbrev Universal.leftAdjoint {G : D ⥤ C}
    (p : ∀ X, Universal G X) : C ⥤ D where
  obj X := (p X).obj
  map {X Y} f := (CoYoneda.Equiv ((p Y).obj) Hom[(p X).obj, –]).hom
    ((p X).rep.inv ○ Hom[f, G–] ○ (p Y).rep.hom)
  map_comp {Y Z X} g f := by
    have q := congrFun
      (CoYoneda.Equiv ((p Y).obj) Hom[(p X).obj, –]).inv_hom_id
      ((p X).rep.inv ○ Hom[f, G–] ○ (p Y).rep.hom)
    simp only [Hom.eq_1, ProductCat_obj, ProductCat_hom, CoYoneda.Equiv,
      Category.id_comp, Functor.map_id, Category.comp_id, Function.comp_def,
      id_eq, NatTrans.mk.injEq] at q
    have := congr_fun₂ q
    simp_all

/-- 從 couniversal property 族構造右 adjoint -/
abbrev CoUniversal.rightAdjoint {F : C ⥤ D}
    (p : ∀ A, CoUniversal F A) : D ⥤ C where
  obj A := (p A).obj
  map {X Y} f := (Yoneda.Equiv ((p X).obj) Hom[–, (p Y).obj]).hom
    ((p Y).rep.hom ○ Hom[Fᵒᵖ–, f] ○ (p X).rep.inv)
  map_comp {Y Z X} g f := by
    have q := congrFun
      (Yoneda.Equiv ((p Y).obj) Hom[–, (p Z).obj]).inv_hom_id
      ((p Z).rep.hom ○ Hom[Fᵒᵖ–, g] ○ (p Y).rep.inv)
    simp only [Hom.eq_1, ProductCat_obj, ProductCat_hom, Yoneda.Equiv,
      Category.comp_id, Functor.map_id, Category.id_comp, Function.comp_def,
      id_eq, NatTrans.mk.injEq] at q
    have := congr_fun₂ q
    simp_all

/-- `leftAdjoint p ⊣ G` -/
def Adjunction.ofUniversal (G : D ⥤ C)
  (p : ∀ X, Universal G X) : Universal.leftAdjoint p ⊣ G :=
  NatIso.ofComponents
    ⟨fun (X, A) => (p X).rep.hom·A, by
      intro (X, A) (Y, B) (f, g)
      ext h
      have q₀ := Universal.data.factorization (Universal.rep.hom·A h)
      have q₁ := congrFun (Universal.rep.hom.naturality (g ○ h)) (Universal.leftAdjoint p)[f]
      simp [Universal.data] at q₀ q₁
      simp [q₁]
      grind⟩
    fun (X, A) => (p X).rep.IsIso A

/-- `F ⊣ rightAdjoint p` -/
def Adjunction.ofCoUniversal (F : C ⥤ D)
    (p : ∀ A, CoUniversal F A) : F ⊣ CoUniversal.rightAdjoint p :=
  NatIso.ofComponents
    ⟨fun (X, A) => (p A).rep.hom·X, by
      intro (X, A) (Y, B) (f, g)
      ext h
      have q₀ := CoUniversal.data.factorization h
      have q₁ := congrFun (CoUniversal.rep.hom.naturality
        (CoUniversal.data.factor h ○[C] f)) (g ○ CoUniversal.data.morphism)
      conv_lhs => rw [q₀]
      simpa using q₁⟩
    fun (X, A) => (p A).rep.IsIso X

variable (φ : F ⊣[C, D] G)

/-- 伴隨給出 universal property -/
abbrev Adjunction.Universal (X : C.obj) : CategoryTheory.Universal G X where
  obj := F[X]
  rep := {
    hom := {
      app Y := φ·(X, Y),
      naturality f := by simpa using φ.hom·(X, –).naturality f}
    inv := {
      app Y := φ⁻¹·(X, Y),
      naturality f := by simpa using φ.inv·(X, –).naturality f} }

/-- 伴隨給出 couniversal property -/
abbrev Adjunction.CoUniversal (A : D.obj) : CategoryTheory.CoUniversal F A where
  obj := G[A]
  rep := {
    hom := {
      app B := φ·(B, A),
      naturality f := by simpa using φ.hom·(–, A).naturality f}
    inv := {
      app B := φ⁻¹·(B, A),
      naturality f := by simpa using φ.inv·(–, A).naturality f} }

end UniversalProperty
end CategoryTheory
