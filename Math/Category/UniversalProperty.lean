import MATH.Category.Structure.Types
import MATH.Category.Functor.Hom

/-!
# UniversalProperty.lean

Universal / couniversal property。

## 定義
- `Universal G X A` — `Hom[A, –] ≅ Hom[X, G–]`
- `coUniversal F A X` — `Hom[Fᵒᵖ–, A] ≅ Hom[–, X]`
- `IsUniversal` / `IscoUniversal` — ∃! factorization 版本

## 定理
### `Universal` / `coUniversal`
- `.factorization` — `f = G[u⁻¹·B f] ○ u.morphism`
- `.Property` — `Universal` ⟹ `IsUniversal`
- `.uniqueUpToIso` — universal object 在 iso 下唯一
- `.ofUniversalIso` / `.ofUniversalNatIso` — 沿 iso 轉移
### `IsUniversal` / `IscoUniversal`
- `.Universal` / `.coUniversal` — `IsUniversal` ⟹ `Universal`
-/

namespace CategoryTheory

/-- `Universal G X A := Hom[A, –] ≅ Hom[X, G–]` -/
@[simp]
def Universal (G : D ⥤ C) (X : C.obj) (A : D.obj) :=
  Hom[A, –] ≅ Hom[X, G–]

/-- Universal arrow `u.morphism = u·A (𝟙 A) : X ⟶ G[A]` -/
abbrev Universal.morphism
  (u : Universal G X A) : X ⟶ G[A] :=
  (u·A : Hom[A, A] ⟶ Hom[X, G[A]]) (𝟙 A)

/-- `f = G[u⁻¹·B f] ○ u.morphism` -/
lemma Universal.factorization (u : Universal G X A) :
  ∀ B (f : X ⟶ G[B]), f = G[u⁻¹·B f] ○ u.morphism := by
    intro B f
    simpa using congrFun (u.hom.naturality (u⁻¹·B f)) (𝟙 A)


/-- `coUniversal F A X := Hom[Fᵒᵖ–, A] ≅ Hom[–, X]` -/
@[simp]
def coUniversal (F : C ⥤ D) (A : D.obj) (X : C.obj) :=
  Hom[Fᵒᵖ–, A] ≅ Hom[–, X]

/-- Couniversal arrow `u.morphism = u⁻¹·X (𝟙 X) : F[X] ⟶ A` -/
abbrev coUniversal.morphism
  (u : coUniversal F A X) : F[X] ⟶ A :=
  (u⁻¹·X : Hom[X, X] ⟶ Hom[Fᵒᵖ[X], A]) (𝟙 X)

/-- `f = u.morphism ○ F[u·Y f]` -/
lemma coUniversal.factorization (u : coUniversal F A X) :
  ∀ Y (f : F[Y] ⟶ A), f = u.morphism ○ F[u·Y f] :=  by
    intro Y f
    simpa using congrFun (u.inv.naturality (u·Y f)) (𝟙 X)


/-- `IsUniversal u`：對任意 `f : X ⟶ G[B]`，∃! `f' : A ⟶ B` 使得 `f = G[f'] ○ u` -/
def IsUniversal {G : D ⥤ C} (u : X ⟶ G[A]) : Prop :=
  ∀ B (f : X ⟶ G[B]), ∃! f' : A ⟶ B, f = G[f'] ○ u

@[simp]
lemma Universal.Property
  (u : Universal G X A) : IsUniversal u.morphism :=
    fun B f => ⟨u⁻¹·B f, factorization u B f, fun f' q => by
      let p := congrFun (u.hom.naturality f') (𝟙 A)
      simpa [←q, ←NatIso.eq_symm_apply] using p⟩

noncomputable
def IsUniversal.Universal
  (u : X ⟶ G[A]) (prop : IsUniversal u) : Universal G X A where
  hom : Hom[A, –] ⇒ Hom[X, G–] := {app B f := G[f] ○ u}
  inv : Hom[X, G–] ⇒ Hom[A, –]  := {
    app B f := (prop B f).choose,
    naturality {A' B'} h := by
      ext f
      let p := (prop B' (G[h] ○ f)).choose_spec.2 (h ○ (prop A' f).choose)
      let q := Whisker.left_cancel G[h] (prop A' f).choose_spec.1
      simp at p q
      simpa using (p q).symm }
  hom_inv_id := by
    ext B f
    simpa using ((prop B f).choose_spec.1).symm
  inv_hom_id := by
    ext B h
    let p := (prop B (G[h] ○ u)).choose_spec.2 h
    simp at p
    exact p.symm

@[simp]
lemma IsUniversal.IsMorphism
  (u : X ⟶ G[A]) (prop : IsUniversal u) :
  (IsUniversal.Universal u prop).morphism = u := by
    simp [IsUniversal.Universal]
    grind

/-- `IscoUniversal u`：對任意 `f : F[Y] ⟶ A`，∃! `f' : Y ⟶ X` 使得 `f = u ○ F[f']` -/
def IscoUniversal {F : C ⥤ D} (u : F[X] ⟶ A) : Prop :=
  ∀ Y (f : F[Y] ⟶ A), ∃! f' : Y ⟶ X, f = u ○ F[f']

@[simp]
lemma coUniversal.Property
  (u : coUniversal F A X) : IscoUniversal u.morphism :=
    fun Y f => ⟨u·Y f, factorization u Y f, fun f' q => by
      let p := congrFun (u.inv.naturality f') (𝟙 X)
      simp [←q] at p
      exact (u.eq_symm_apply.mp p.symm).symm⟩

noncomputable
def IscoUniversal.coUniversal
  (u : F[X] ⟶ A) (prop : IscoUniversal u) : coUniversal F A X where
  hom : Hom[Fᵒᵖ–, A] ⇒ Hom[–, X] := {
    app B f := (prop B f).choose,
    naturality {A' B'} h := by
      ext f
      let p := (prop B' (f ○ F[h])).choose_spec.2 ((prop A' f).choose ○ h)
      let q := Whisker.right_cancel F[h] (prop A' f).choose_spec.1
      simp at p q
      simpa using (p q).symm }
  inv : Hom[–, X] ⇒ Hom[Fᵒᵖ–, A] := {app B f := u ○ F[f]}
  hom_inv_id := by
    ext B h
    let p := (prop B (u ○ F[h])).choose_spec.2 h
    simp at p
    exact p.symm
  inv_hom_id := by
    ext B f
    simpa using ((prop B f).choose_spec.1).symm

@[simp]
lemma coUniversal.IsMorphism
  (u : F[X] ⟶ A) (prop : IscoUniversal u) :
  (IscoUniversal.coUniversal u prop).morphism = u := by
    simp [IscoUniversal.coUniversal]
    grind


/-- Universal object 在 isomorphism 下唯一 -/
def Universal.uniqueUpToIso
  (u : Universal G X A) (v : Universal G X B) : A ≅ B :=
  Hom.reflect_iso_left (Iso.trans u v.symm)

/-- Couniversal object 在 isomorphism 下唯一 -/
def coUniversal.uniqueUpToIso
  (u : coUniversal G X A) (v : coUniversal G X B) : A ≅ B :=
  Hom.reflect_iso_right (Iso.trans u.symm v)

/-- 沿 isomorphism 轉移 universal property -/
def Universal.ofUniversalIso
  (u : Universal G X A) (iso : A ≅ B) : Universal G X B :=
  Iso.trans (Hom.preserve_iso_left iso).symm u

/-- 沿 isomorphism 轉移 couniversal property -/
def coUniversal.ofcoUniversalIso
  (u : coUniversal G X A) (iso : A ≅ B) : coUniversal G X B :=
  Iso.trans u (Hom.preserve_iso_right iso)

/-- 沿 natural isomorphism 轉移 universal property -/
def Universal.ofUniversalNatIso
  (u : Universal G X A) (iso : F ≅ G) : Universal F X A :=
  Iso.trans u ((Hom.preserve_natiso_right iso)(X, –).symm)

/-- 沿 natural isomorphism 轉移 couniversal property -/
def coUniversal.ofcoUniversalNatIso
  (u : coUniversal G X A) (iso : F ≅ G) : coUniversal F X A :=
  Iso.trans ((Hom.preserve_natiso_left iso)(–, X)) u

end CategoryTheory
