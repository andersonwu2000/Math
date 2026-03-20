import MATH.Category.Adjunction.Basic

/-!
# Functor/Representable.lean

Representable / corepresentable functor。

## 定義
- `Representable F` — presheaf `F : Cᵒᵖ ⥤ Types` 可由 `Hom[–, X]` 表示
- `CoRepresentable F` — functor `F : C ⥤ Types` 可由 `Hom[X, –]` 表示
- `RepresentableData F` — 具體 universal element 資料
- `CoRepresentableData F` — 具體 universal element 資料

## 定理
### `Representable`
- `.data` — `Representable` ⟹ `RepresentableData`
- `.unique` — representing object 在 iso 下唯一
### `RepresentableData`
- `.toRepresentable` — `RepresentableData` ⟹ `Representable`
### `CoRepresentable`
- `.data` — `CoRepresentable` ⟹ `CoRepresentableData`
- `.unique` — representing object 在 iso 下唯一
### `CoRepresentableData`
- `.toCoRepresentable` — `CoRepresentableData` ⟹ `CoRepresentable`
-/

namespace CategoryTheory

/-- Representable presheaf：`F : Cᵒᵖ ⥤ Types` 可由 `Hom[–, X]` 表示 -/
class Representable (F : Cᵒᵖ ⥤ Types) where
  rep : C.obj
  iso : Hom[–, rep] ≅ F

/-- CoRepresentable functor：`F : C ⥤ Types` 可由 `Hom[X, –]` 表示 -/
class CoRepresentable (F : C ⥤ Types) where
  rep : C.obj
  iso : Hom[rep, –] ≅ F

/-- Representable 的具體 universal element 資料 -/
structure RepresentableData (F : Cᵒᵖ ⥤ Types) where
  rep : C.obj
  element : F[rep]
  factor {A : C.obj} (a : F[A]) : A ⟶ rep
  factorization {A : C.obj} (a : F[A]) : F[factor a] element = a
  factor_unique {A : C.obj} (a : F[A]) (f : A ⟶ rep)
      (hf : F[f] element = a) : f = factor a

/-- CoRepresentable 的具體 universal element 資料 -/
structure CoRepresentableData (F : C ⥤ Types) where
  rep : C.obj
  element : F[rep]
  factor {A : C.obj} (a : F[A]) : rep ⟶ A
  factorization {A : C.obj} (a : F[A]) : F[factor a] element = a
  factor_unique {A : C.obj} (a : F[A]) (f : rep ⟶ A)
      (hf : F[f] element = a) : f = factor a

-- ─── Representable ───────────────────────────────────────────────────────────

namespace Representable

/-- `Representable` ⟹ `RepresentableData` -/
noncomputable def data (h : Representable F) : RepresentableData F where
  rep       := h.rep
  element   := h.iso.hom·h.rep (𝟙 h.rep)
  factor a  := h.iso.inv·_ a
  factorization a := by
    have p := Yoneda.principal h.iso.hom (h.iso.inv·_ a)
    rw [p]; exact congrFun (NatIso.hom_inv_id_app h.iso _) a
  factor_unique a f hf := by
    have p := Yoneda.principal h.iso.hom f
    rw [hf] at p
    exact Eq.trans
      (Types.hom_inv_id_apply f (NatIso.Iso h.iso _)).symm
      (congrArg (h.iso.inv·_) p.symm)

/-- Representing object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Representable F) :
    h₁.rep ≅ h₂.rep :=
  Hom.reflect_iso_right (Iso.trans h₁.iso h₂.iso.symm)

end Representable

/-- `RepresentableData` ⟹ `Representable` -/
@[reducible]
noncomputable def RepresentableData.toRepresentable
    (rd : RepresentableData F) : Representable F where
  rep := rd.rep
  iso := {
    hom := { app A f := F[f] rd.element }
    inv := { app A a := rd.factor a
             naturality g := by
               ext a; simp only [Types]; symm
               apply rd.factor_unique
               simp [Hom, rd.factorization] }
    hom_inv_id := by
      ext A a; simp only [Types]
      exact rd.factorization a
    inv_hom_id := by
      ext A f; simp only [Types]
      exact (rd.factor_unique _ f rfl).symm }

-- ─── CoRepresentable ─────────────────────────────────────────────────────────

namespace CoRepresentable

/-- `CoRepresentable` ⟹ `CoRepresentableData` -/
noncomputable def data (h : CoRepresentable F) : CoRepresentableData F where
  rep       := h.rep
  element   := h.iso.hom·h.rep (𝟙 h.rep)
  factor a  := h.iso.inv·_ a
  factorization a := by
    have p := CoYoneda.principal h.iso.hom (h.iso.inv·_ a)
    rw [p]; exact congrFun (NatIso.hom_inv_id_app h.iso _) a
  factor_unique a f hf := by
    have p := CoYoneda.principal h.iso.hom f
    rw [hf] at p
    exact Eq.trans
      (Types.hom_inv_id_apply f (NatIso.Iso h.iso _)).symm
      (congrArg (h.iso.inv·_) p.symm)

/-- Representing object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : CoRepresentable F) :
    h₁.rep ≅ h₂.rep :=
  Hom.reflect_iso_left (Iso.trans h₁.iso h₂.iso.symm)

end CoRepresentable

/-- `CoRepresentableData` ⟹ `CoRepresentable` -/
@[reducible]
noncomputable def CoRepresentableData.toCoRepresentable
    (rd : CoRepresentableData F) : CoRepresentable F where
  rep := rd.rep
  iso := {
    hom := { app A f := F[f] rd.element }
    inv := { app A a := rd.factor a
             naturality g := by
               ext a; simp only [Types]; symm
               apply rd.factor_unique
               simp [Hom, rd.factorization] }
    hom_inv_id := by
      ext A a; simp only [Types]
      exact rd.factorization a
    inv_hom_id := by
      ext A f; simp only [Types]
      exact (rd.factor_unique _ f rfl).symm }

end CategoryTheory
