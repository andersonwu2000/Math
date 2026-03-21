import MATH.Category.Functor.Representable

/-!
# UniversalProperty.lean

Universal / couniversal property。

## 定義
- `Universal G X` — 存在 `obj` 使 `Hom[obj, –] ≅ Hom[X, G–]`（extends `Representable`）
- `UniversalData G X` — 具體 universal arrow 資料
- `CoUniversal F A` — 存在 `obj` 使 `Hom[Fᵒᵖ–, A] ≅ Hom[–, obj]`（extends `CoRepresentable`）
- `CoUniversalData F A` — 具體 couniversal arrow 資料

## 定理
### `Universal`
- `.data` — `Universal` ⟹ `UniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — universal object 在 iso 下唯一
- `.ofIso` — `X ≅ Y → Universal G X → Universal G Y`
- `.ofNatIso` — `F ≅ G → Universal G X → Universal F X`
- `.ofObjIso` — `obj ≅ B → Universal G X → Universal G X`（改 representing object）
### `UniversalData`
- `.toUniversal` — `UniversalData` ⟹ `Universal`
### `CoUniversal`
- `.data` — `CoUniversal` ⟹ `CoUniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — couniversal object 在 iso 下唯一
- `.ofIso` — `A ≅ B → CoUniversal F A → CoUniversal F B`
- `.ofNatIso` — `F ≅ G → CoUniversal F A → CoUniversal G A`
- `.ofObjIso` — `obj ≅ B → CoUniversal F A → CoUniversal F A`（改 representing object）
### `CoUniversalData`
- `.toCoUniversal` — `CoUniversalData` ⟹ `CoUniversal`
-/

namespace CategoryTheory

/-- `Universal G X`：存在 `obj : D.obj` 使得 `Hom[obj, –] ≅ Hom[X, G–]` -/
class Universal (G : D ⥤ C) (X : C.obj) extends Representable Hom[X, G–]

/-- `CoUniversal F A`：存在 `obj : C.obj` 使得 `Hom[Fᵒᵖ–, A] ≅ Hom[–, obj]` -/
class CoUniversal (F : C ⥤ D) (A : D.obj) extends CoRepresentable Hom[Fᵒᵖ–, A]

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

/-- `Universal` ⟹ `UniversalData` -/
def Universal.data [h : Universal G X] : UniversalData G X :=
  let d := h.toRepresentable.data
  { obj := d.obj
    morphism := d.element
    factor f := d.factor f
    factorization f := by simpa using (d.factorization f).symm
    factor_unique f k hk := by apply d.factor_unique; simpa using hk.symm }

/-- `UniversalData` ⟹ `Universal` -/
@[reducible]
def UniversalData.toUniversal (h : UniversalData G X) : Universal G X :=
  { toRepresentable := RepresentableData.toRepresentable (F := Hom[X, G–]) {
      obj := h.obj
      element := h.morphism
      factor f := h.factor f
      factorization f := by simpa using (h.factorization f).symm
      factor_unique f k hk := by apply h.factor_unique; simpa using hk.symm } }

/-- 對任意 `f : X ⟶ G[B]`，存在唯一的分解 `k : obj ⟶ B` 使 `f = G[k] ○ morphism` -/
lemma Universal.property [h : Universal G X] :
    ∀ f : X ⟶ G[B], ∃! k : h.obj ⟶ B, f = G[k] ○ h.data.morphism := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Universal object 在 isomorphism 下唯一 -/
noncomputable def Universal.unique (u v : Universal G X) : u.obj ≅ v.obj :=
  Representable.unique u.toRepresentable v.toRepresentable

/-- 沿 argument 的 isomorphism 轉移 -/
@[reducible]
def Universal.ofIso
  (u : Universal G X) (iso : X ≅ Y) : Universal G Y where
  toRepresentable := Representable.ofNatIso (h := u.toRepresentable) {
    hom := { app B f := f ○ iso.inv }
    inv := { app B f := f ○ iso.hom } }

/-- 沿 functor 的 natural isomorphism 轉移 -/
@[reducible]
def Universal.ofNatIso
  (u : Universal G X) (iso : F ≅ G) : Universal F X where
  toRepresentable := Representable.ofNatIso
    ((Hom.preserve_natiso_right iso)(X, –).symm)

/-- 沿 representing object 的 isomorphism 轉移 -/
@[reducible]
def Universal.ofObjIso
  (u : Universal G X) (iso : u.obj ≅ B) : Universal G X where
  obj := B
  rep := Iso.trans (Hom.preserve_iso_left iso).symm u.rep

-- ─── CoUniversal ──────────────────────────────────────────────────────────────

/-- `CoUniversal` ⟹ `CoUniversalData` -/
def CoUniversal.data [h : CoUniversal F A] : CoUniversalData F A :=
  let d := h.toCoRepresentable.data
  { obj := d.obj
    morphism := d.element
    factor f := d.factor f
    factorization f := by simpa using (d.factorization f).symm
    factor_unique f k hk := by apply d.factor_unique; simpa using hk.symm }

/-- `CoUniversalData` ⟹ `CoUniversal` -/
@[reducible]
def CoUniversalData.toCoUniversal (h : CoUniversalData F A) : CoUniversal F A :=
  { toCoRepresentable := CoRepresentableData.toCoRepresentable (F := Hom[Fᵒᵖ–, A]) {
      obj := h.obj
      element := h.morphism
      factor f := h.factor f
      factorization f := by simpa using (h.factorization f).symm
      factor_unique f k hk := by apply h.factor_unique; simpa using hk.symm } }

/-- 對任意 `f : F[Y] ⟶ A`，存在唯一的分解 `k : Y ⟶ obj` 使 `f = morphism ○ F[k]` -/
lemma CoUniversal.property [h : CoUniversal F A] :
    ∀ f : F[Y] ⟶ A, ∃! k : Y ⟶ h.obj, f = h.data.morphism ○ F[k] := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Couniversal object 在 isomorphism 下唯一 -/
noncomputable def CoUniversal.unique (u v : CoUniversal F A) : u.obj ≅ v.obj :=
  CoRepresentable.unique u.toCoRepresentable v.toCoRepresentable

/-- 沿 argument 的 isomorphism 轉移 -/
@[reducible]
def CoUniversal.ofIso
  (u : CoUniversal F A) (iso : A ≅ B) : CoUniversal F B where
  toCoRepresentable := CoRepresentable.ofNatIso (h := u.toCoRepresentable) {
    hom := { app Y f := iso.hom ○ f }
    inv := { app Y f := iso.inv ○ f }
    hom_inv_id := by ext Y f; simp [Types, ←Category.assoc]
    inv_hom_id := by ext Y f; simp [Types, ←Category.assoc] }

/-- 沿 functor 的 natural isomorphism 轉移 -/
@[reducible]
def CoUniversal.ofNatIso
  (u : CoUniversal F A) (iso : F ≅ G) : CoUniversal G A where
  toCoRepresentable := CoRepresentable.ofNatIso
    ((Hom.preserve_natiso_left iso)(–, A))

/-- 沿 representing object 的 isomorphism 轉移 -/
@[reducible]
def CoUniversal.ofObjIso
  (u : CoUniversal F A) (iso : u.obj ≅ B) : CoUniversal F A where
  obj := B
  rep := Iso.trans u.rep (Hom.preserve_iso_right iso)

end CategoryTheory
