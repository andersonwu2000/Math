import MATH.Category.Structure.Types
import MATH.Category.Functor.Hom

/-!
# Functor/Representable.lean

Representable / corepresentable functor。

## 定義
- `Representable F` — functor `F : C ⥤ Types` 可由 `Hom[X, –]` 表示
- `CoRepresentable F` — presheaf `F : Cᵒᵖ ⥤ Types` 可由 `Hom[–, X]` 表示
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
### `Types`
- `Representable (𝟙[Cat] Types)` — `Hom[Types.Terminal, –] ≅ 𝟙 Types`
-/

namespace CategoryTheory

/-- Representable functor：`F : C ⥤ Types` 可由 `Hom[X, –]` 表示 -/
class Representable (F : C ⥤ Types) where
  obj : C.obj
  rep : Hom[obj, –] ≅ F

/-- CoRepresentable presheaf：`F : Cᵒᵖ ⥤ Types` 可由 `Hom[–, X]` 表示 -/
class CoRepresentable (F : Cᵒᵖ ⥤ Types) where
  obj : C.obj
  rep : F ≅ Hom[–, obj]

/-- Representable 的具體 universal element 資料 -/
structure RepresentableData (F : C ⥤ Types) where
  obj : C.obj
  element : F[obj]
  factor {A : C.obj} (a : F[A]) : obj ⟶ A
  factorization {A : C.obj} (a : F[A]) : F[factor a] element = a
  factor_unique {A : C.obj} (a : F[A]) (f : obj ⟶ A)
      (hf : F[f] element = a) : f = factor a

/-- CoRepresentable 的具體 universal element 資料 -/
structure CoRepresentableData (F : Cᵒᵖ ⥤ Types) where
  obj : C.obj
  element : F[obj]
  factor {A : C.obj} (a : F[A]) : A ⟶ obj
  factorization {A : C.obj} (a : F[A]) : F[factor a] element = a
  factor_unique {A : C.obj} (a : F[A]) (f : A ⟶ obj)
      (hf : F[f] element = a) : f = factor a

-- ─── Representable ───────────────────────────────────────────────────────────

namespace Representable

/-- `Representable` ⟹ `RepresentableData` -/
def data [h : Representable F] : RepresentableData F where
  obj       := h.obj
  element   := h.rep.hom·h.obj (𝟙 h.obj)
  factor a  := h.rep.inv·_ a
  factorization a := by
    have p := CoYoneda.principal h.rep.hom (h.rep.inv·_ a)
    rw [p]; exact congrFun (NatIso.hom_inv_id_app h.rep _) a
  factor_unique a f hf := by
    have p := CoYoneda.principal h.rep.hom f
    rw [hf] at p
    exact Eq.trans
      (Types.hom_inv_id_apply f (NatIso.Iso h.rep _)).symm
      (congrArg (h.rep.inv·_) p.symm)

/-- Representing object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Representable F) :
    h₁.obj ≅ h₂.obj :=
  Hom.reflect_iso_left (Iso.trans h₁.rep h₂.rep.symm)

end Representable

/-- `RepresentableData` ⟹ `Representable` -/
@[reducible]
def RepresentableData.toRepresentable
    (rd : RepresentableData F) : Representable F where
  obj := rd.obj
  rep := {
    hom := { app A f := F[f] rd.element }
    inv := { app A a := rd.factor a
             naturality g := by
               ext a; symm
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
def data [h : CoRepresentable F] : CoRepresentableData F where
  obj       := h.obj
  element   := h.rep.inv·h.obj (𝟙 h.obj)
  factor a  := h.rep.hom·_ a
  factorization a := by
    have p := Yoneda.principal h.rep.inv (h.rep.hom·_ a)
    rw [p]; exact congrFun (NatIso.inv_hom_id_app h.rep _) a
  factor_unique a f hf := by
    have p := Yoneda.principal h.rep.inv f
    rw [hf] at p
    exact Eq.trans
      (Types.inv_hom_id_apply f (NatIso.Iso h.rep _)).symm
      (congrArg (h.rep.hom·_) p.symm)

/-- Representing object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : CoRepresentable F) :
    h₁.obj ≅ h₂.obj :=
  Hom.reflect_iso_right (Iso.trans h₁.rep.symm h₂.rep)

end CoRepresentable

/-- `CoRepresentableData` ⟹ `CoRepresentable` -/
@[reducible]
def CoRepresentableData.toCoRepresentable
    (rd : CoRepresentableData F) : CoRepresentable F where
  obj := rd.obj
  rep := {
    hom := { app A a := rd.factor a
             naturality g := by
               ext a; symm
               apply rd.factor_unique
               simp [Hom, rd.factorization] }
    inv := { app A f := F[f] rd.element }
    hom_inv_id := by
      ext A f; simp only [Types]
      exact (rd.factor_unique _ f rfl).symm
    inv_hom_id := by
      ext A a; simp only [Types]
      exact rd.factorization a }

/-- `Hom[Types.Terminal, –] ≅ 𝟙 Types`：PUnit represents the identity functor -/
instance : Representable (𝟙[Cat] Types) :=
  RepresentableData.toRepresentable {
    obj := Types.Terminal
    element := PUnit.unit
    factor a := fun _ => a
    factorization _ := rfl
    factor_unique _ f hf := by funext ⟨⟩; exact hf
  }

end CategoryTheory
