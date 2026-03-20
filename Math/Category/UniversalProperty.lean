import MATH.Category.Functor.Representable

/-!
# UniversalProperty.lean

Universal / couniversal property。

## 定義
- `Universal G X` — 存在 `obj` 使 `Hom[obj, –] ≅ Hom[X, G–]`
- `UniversalData G X` — 具體 universal arrow 資料
- `CoUniversal F A` — 存在 `obj` 使 `Hom[Fᵒᵖ–, A] ≅ Hom[–, obj]`
- `CoUniversalData F A` — 具體 couniversal arrow 資料

## 定理
### `Universal`
- `.representable` — instance：`Universal G X` ⟹ `Representable Hom[X, G–]`
- `.data` — `Universal` ⟹ `UniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — universal object 在 iso 下唯一
- `.ofIso` / `.ofNatIso` — 沿 iso 轉移
### `UniversalData`
- `.toUniversal` — `UniversalData` ⟹ `Universal`
### `CoUniversal`
- `.representable` — instance：`CoUniversal F A` ⟹ `CoRepresentable Hom[Fᵒᵖ–, A]`
- `.data` — `CoUniversal` ⟹ `CoUniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — couniversal object 在 iso 下唯一
- `.ofIso` / `.ofNatIso` — 沿 iso 轉移
### `CoUniversalData`
- `.toCoUniversal` — `CoUniversalData` ⟹ `CoUniversal`
-/

namespace CategoryTheory

/-- `Universal G X`：存在 `obj : D.obj` 使得 `Hom[obj, –] ≅ Hom[X, G–]` -/
class Universal (G : D ⥤ C) (X : C.obj) where
  obj : D.obj
  rep : Hom[obj, –] ≅ Hom[X, G–]

/-- `CoUniversal F A`：存在 `obj : C.obj` 使得 `Hom[Fᵒᵖ–, A] ≅ Hom[–, obj]` -/
class CoUniversal (F : C ⥤ D) (A : D.obj) where
  obj : C.obj
  rep : Hom[Fᵒᵖ–, A] ≅ Hom[–, obj]

-- ─── UniversalData / CoUniversalData ──────────────────────────────────────────

/-- `UniversalData G X`：具體 universal arrow 資料 -/
structure UniversalData (G : D ⥤ C) (X : C.obj) where
  obj : D.obj
  morphism : X ⟶ G[obj]
  factor (f : X ⟶ G[B]) : obj ⟶ B
  factorization (f : X ⟶ G[B]) : f = G[factor f] ○ morphism
  factor_unique (f : X ⟶ G[B]) (k : obj ⟶ B)
      (hk : f = G[k] ○ morphism) : k = factor f

attribute [simp] UniversalData.factorization

/-- `CoUniversalData F A`：具體 couniversal arrow 資料 -/
structure CoUniversalData (F : C ⥤ D) (A : D.obj) where
  obj : C.obj
  morphism : F[obj] ⟶ A
  factor (f : F[Y] ⟶ A) : Y ⟶ obj
  factorization (f : F[Y] ⟶ A) : f = morphism ○ F[factor f]
  factor_unique (f : F[Y] ⟶ A) (k : Y ⟶ obj)
      (hk : f = morphism ○ F[k]) : k = factor f

attribute [simp] CoUniversalData.factorization


-- ─── Universal ────────────────────────────────────────────────────────────────

/-- `Universal G X` ⟹ `Representable Hom[X, G–]` -/
instance Universal.representable {G : D ⥤ C} {X : C.obj}
    [h : Universal G X] : Representable Hom[X, G–] where
  obj := h.obj
  rep := h.rep

/-- `Universal` ⟹ `UniversalData` -/
def Universal.data [Universal G X] : UniversalData G X where
  obj := Universal.representable.data.obj
  morphism := Universal.representable.data.element
  factor f := Universal.representable.data.factor f
  factorization f := by simpa using (Universal.representable.data.factorization f).symm
  factor_unique f k hk := by
    apply Universal.representable.data.factor_unique; simpa using hk.symm

/-- `UniversalData` ⟹ `Universal` -/
@[reducible]
def UniversalData.toUniversal (h : UniversalData G X) : Universal G X :=
  let r := RepresentableData.toRepresentable (F := Hom[X, G–]) {
    obj := h.obj
    element := h.morphism
    factor f := h.factor f
    factorization f := by simpa using (h.factorization f).symm
    factor_unique f k hk := by apply h.factor_unique; simpa using hk.symm
  }
  { obj := r.obj, rep := r.rep }

/-- 對任意 `f : X ⟶ G[B]`，存在唯一的分解 `k : obj ⟶ B` 使 `f = G[k] ○ morphism` -/
lemma Universal.property [h : Universal G X] :
    ∀ f : X ⟶ G[B], ∃! k : h.obj ⟶ B, f = G[k] ○ h.data.morphism := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Universal object 在 isomorphism 下唯一 -/
noncomputable def Universal.unique (u v : Universal G X) : u.obj ≅ v.obj :=
  Representable.unique (Universal.representable (h := u)) (Universal.representable (h := v))

/-- 沿 isomorphism 轉移 universal property -/
@[reducible]
def Universal.ofIso
  (u : Universal G X) (iso : u.obj ≅ B) : Universal G X where
  obj := B
  rep := Iso.trans (Hom.preserve_iso_left iso).symm u.rep

/-- 沿 natural isomorphism 轉移 universal property -/
@[reducible]
def Universal.ofNatIso
  (u : Universal G X) (iso : F ≅ G) : Universal F X where
  obj := u.obj
  rep := Iso.trans u.rep ((Hom.preserve_natiso_right iso)(X, –).symm)

-- ─── CoUniversal ──────────────────────────────────────────────────────────────

/-- `CoUniversal F A` ⟹ `CoRepresentable Hom[Fᵒᵖ–, A]` -/
instance CoUniversal.representable {F : C ⥤ D} {A : D.obj}
    [h : CoUniversal F A] : CoRepresentable Hom[Fᵒᵖ–, A] where
  obj := h.obj
  rep := h.rep

/-- `CoUniversal` ⟹ `CoUniversalData` -/
def CoUniversal.data [CoUniversal F A] : CoUniversalData F A where
  obj := CoUniversal.representable.data.obj
  morphism := CoUniversal.representable.data.element
  factor f := CoUniversal.representable.data.factor f
  factorization f := by simpa using (CoUniversal.representable.data.factorization f).symm
  factor_unique f k hk := by
    apply CoUniversal.representable.data.factor_unique; simpa using hk.symm

/-- `CoUniversalData` ⟹ `CoUniversal` -/
@[reducible]
def CoUniversalData.toCoUniversal (h : CoUniversalData F A) : CoUniversal F A :=
  let r := CoRepresentableData.toCoRepresentable (F := Hom[Fᵒᵖ–, A]) {
    obj := h.obj
    element := h.morphism
    factor f := h.factor f
    factorization f := by simpa using (h.factorization f).symm
    factor_unique f k hk := by apply h.factor_unique; simpa using hk.symm
  }
  { obj := r.obj, rep := r.rep }

/-- 對任意 `f : F[Y] ⟶ A`，存在唯一的分解 `k : Y ⟶ obj` 使 `f = morphism ○ F[k]` -/
lemma CoUniversal.property [h : CoUniversal F A] :
    ∀ f : F[Y] ⟶ A, ∃! k : Y ⟶ h.obj, f = h.data.morphism ○ F[k] := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Couniversal object 在 isomorphism 下唯一 -/
noncomputable def CoUniversal.unique (u v : CoUniversal F A) : u.obj ≅ v.obj :=
  CoRepresentable.unique (CoUniversal.representable (h := u)) (CoUniversal.representable (h := v))

/-- 沿 isomorphism 轉移 couniversal property -/
@[reducible]
def CoUniversal.ofIso
  (u : CoUniversal F A) (iso : u.obj ≅ B) : CoUniversal F A where
  obj := B
  rep := Iso.trans u.rep (Hom.preserve_iso_right iso)

/-- 沿 natural isomorphism 轉移 couniversal property -/
@[reducible]
def CoUniversal.ofNatIso
  (u : CoUniversal F A) (iso : F ≅ G) : CoUniversal G A where
  obj := u.obj
  rep := Iso.trans ((Hom.preserve_natiso_left iso)(–, A)).symm u.rep

end CategoryTheory
