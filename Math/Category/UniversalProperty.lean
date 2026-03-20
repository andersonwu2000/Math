import MATH.Category.Structure.Types
import MATH.Category.Functor.Hom

/-!
# UniversalProperty.lean

Universal / couniversal property。

## 定義
- `Universal G X A` — `Hom[A, –] ≅ Hom[X, G–]`
- `UniversalData G X A` — 具體 universal arrow 資料
- `CoUniversal F A X` — `Hom[Fᵒᵖ–, A] ≅ Hom[–, X]`
- `CoUniversalData F A X` — 具體 couniversal arrow 資料

## 定理
### `Universal`
- `.data` — `Universal` ⟹ `UniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — universal object 在 iso 下唯一
- `.ofIso` / `.ofNatIso` — 沿 iso 轉移
### `UniversalData`
- `.Universal` — `UniversalData` ⟹ `Universal`
### `CoUniversal`
- `.data` — `CoUniversal` ⟹ `CoUniversalData`
- `.property` — 對任意 `f` 存在唯一分解
- `.unique` — couniversal object 在 iso 下唯一
- `.ofIso` / `.ofNatIso` — 沿 iso 轉移
### `CoUniversalData`
- `.CoUniversal` — `CoUniversalData` ⟹ `CoUniversal`
-/

namespace CategoryTheory

/-- `Universal G X A := Hom[A, –] ≅ Hom[X, G–]` -/
@[simp]
def Universal (G : D ⥤ C) (X : C.obj) (A : D.obj) :=
  Hom[A, –] ≅ Hom[X, G–]

/-- `CoUniversal F A X := Hom[Fᵒᵖ–, A] ≅ Hom[–, X]` -/
@[simp]
def CoUniversal (F : C ⥤ D) (A : D.obj) (X : C.obj) :=
  Hom[Fᵒᵖ–, A] ≅ Hom[–, X]

-- ─── UniversalData / CoUniversalData ──────────────────────────────────────────

/-- `UniversalData G X A`：具體 universal arrow 資料 -/
structure UniversalData (G : D ⥤ C) (X : C.obj) (A : D.obj) where
  morphism : X ⟶ G[A]
  factor (f : X ⟶ G[B]) : A ⟶ B
  factorization (f : X ⟶ G[B]) : f = G[factor f] ○ morphism
  factor_unique (f : X ⟶ G[B]) (k : A ⟶ B)
      (hk : f = G[k] ○ morphism) : k = factor f

attribute [simp] UniversalData.factorization

/-- `CoUniversalData F A X`：具體 couniversal arrow 資料 -/
structure CoUniversalData (F : C ⥤ D) (A : D.obj) (X : C.obj) where
  morphism : F[X] ⟶ A
  factor (f : F[Y] ⟶ A) : Y ⟶ X
  factorization (f : F[Y] ⟶ A) : f = morphism ○ F[factor f]
  factor_unique (f : F[Y] ⟶ A) (k : Y ⟶ X)
      (hk : f = morphism ○ F[k]) : k = factor f

attribute [simp] CoUniversalData.factorization

-- ─── Universal ────────────────────────────────────────────────────────────────

/-- `Universal` ⟹ `UniversalData` -/
def Universal.data (iso : Universal G X A) : UniversalData G X A where
  morphism      := (iso·A : Hom[A, A] ⟶ Hom[X, G[A]]) (𝟙 A)
  factor f      := iso⁻¹·_ f
  factorization f := by simpa using congrFun (iso.hom.naturality (iso⁻¹·_ f)) (𝟙 A)
  factor_unique f k hk := by
    have p := congrFun (iso.hom.naturality k) (𝟙 A)
    simpa [← hk, ← NatIso.eq_symm_apply] using p

/-- `UniversalData` ⟹ `Universal` -/
def UniversalData.Universal
    (h : UniversalData G X A) : CategoryTheory.Universal G X A where
  hom : Hom[A, –] ⇒ Hom[X, G–] := { app B f := G[f] ○ h.morphism }
  inv : Hom[X, G–] ⇒ Hom[A, –] := {
    app B f := h.factor f
    naturality {B₁ B₂} k := by
      ext f
      symm; apply h.factor_unique
      aesop_cat
      nth_rw 1 [h.factorization f] }
  hom_inv_id := by ext B f; exact (h.factorization f).symm
  inv_hom_id := by ext B f; exact (h.factor_unique (G[f] ○ h.morphism) f rfl).symm

/-- 對任意 `f : X ⟶ G[B]`，存在唯一的分解 `k : A ⟶ B` 使 `f = G[k] ○ morphism` -/
lemma Universal.property (h : Universal G X A) :
    ∀ f : X ⟶ G[B], ∃! k : A ⟶ B, f = G[k] ○ h.data.morphism := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Universal object 在 isomorphism 下唯一 -/
noncomputable def Universal.unique
  (u : Universal G X A) (v : Universal G X B) : A ≅ B :=
  Hom.reflect_iso_left (Iso.trans u v.symm)

/-- 沿 isomorphism 轉移 universal property -/
def Universal.ofIso
  (u : Universal G X A) (iso : A ≅ B) : Universal G X B :=
  Iso.trans (Hom.preserve_iso_left iso).symm u

/-- 沿 natural isomorphism 轉移 universal property -/
def Universal.ofNatIso
  (u : Universal G X A) (iso : F ≅ G) : Universal F X A :=
  Iso.trans u ((Hom.preserve_natiso_right iso)(X, –).symm)

-- ─── CoUniversal ──────────────────────────────────────────────────────────────

/-- `CoUniversal` ⟹ `CoUniversalData` -/
def CoUniversal.data (iso : CoUniversal F A X) : CoUniversalData F A X where
  morphism      := (iso⁻¹·X : Hom[X, X] ⟶ Hom[Fᵒᵖ[X], A]) (𝟙 X)
  factor f      := iso·_ f
  factorization f := by simpa using congrFun (iso.inv.naturality (iso·_ f)) (𝟙 X)
  factor_unique f k hk := by
    have p := congrFun (iso.inv.naturality k) (𝟙 X)
    simp [← hk] at p
    exact (iso.eq_symm_apply.mp p.symm).symm

/-- `CoUniversalData` ⟹ `CoUniversal` -/
def CoUniversalData.CoUniversal
    (h : CoUniversalData F A X) : CategoryTheory.CoUniversal F A X where
  hom : Hom[Fᵒᵖ–, A] ⇒ Hom[–, X] := {
    app B f := h.factor f
    naturality {B₁ B₂} k := by
      ext f
      symm; apply h.factor_unique
      aesop_cat
      nth_rw 1 [h.factorization f]
      simp [Category.assoc] }
  inv : Hom[–, X] ⇒ Hom[Fᵒᵖ–, A] := { app B f := h.morphism ○ F[f] }
  hom_inv_id := by ext B f; exact (h.factor_unique (h.morphism ○ F[f]) f rfl).symm
  inv_hom_id := by ext B f; exact (h.factorization f).symm

/-- 對任意 `f : F[Y] ⟶ A`，存在唯一的分解 `k : Y ⟶ X` 使 `f = morphism ○ F[k]` -/
lemma CoUniversal.property (h : CoUniversal F A X) :
    ∀ f : F[Y] ⟶ A, ∃! k : Y ⟶ X, f = h.data.morphism ○ F[k] := fun f =>
  ⟨h.data.factor f, h.data.factorization f, fun k hk => h.data.factor_unique f k hk⟩

/-- Couniversal object 在 isomorphism 下唯一 -/
noncomputable def CoUniversal.unique
  (u : CoUniversal G X A) (v : CoUniversal G X B) : A ≅ B :=
  Hom.reflect_iso_right (Iso.trans u.symm v)

/-- 沿 isomorphism 轉移 couniversal property -/
def CoUniversal.ofIso
  (u : CoUniversal G X A) (iso : A ≅ B) : CoUniversal G X B :=
  Iso.trans u (Hom.preserve_iso_right iso)

/-- 沿 natural isomorphism 轉移 couniversal property -/
def CoUniversal.ofNatIso
  (u : CoUniversal G X A) (iso : F ≅ G) : CoUniversal F X A :=
  Iso.trans ((Hom.preserve_natiso_left iso)(–, X)) u

end CategoryTheory
