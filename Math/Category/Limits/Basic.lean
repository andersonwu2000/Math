import MATH.Category.UniversalProperty
import MATH.Category.Functor.Const

/-!
# Limits/Basic.lean

Limit / colimit。

## 定義
- `Limit F` — `F` 有 limit，即 `Hom[Δᵒᵖ–, F] ≅ Hom[–, obj]`
- `CoLimit F` — `F` 有 colimit，即 `Hom[obj, –] ≅ Hom[F, Δ–]`
- `LimitData F` — limit cone `cone`、universal `lift`
- `CoLimitData F` — colimit cocone `cocone`、universal `desc`

## 定理
### `Limit`
- `.universal` — instance：`Limit F` ⟹ `CoUniversal Δ F`
- `.data` — `Limit` ⟹ `LimitData`
- `.unique` — limit 在 iso 下唯一
### `CoLimit`
- `.universal` — instance：`CoLimit F` ⟹ `Universal Δ F`
- `.data` — `CoLimit` ⟹ `CoLimitData`
- `.unique` — colimit 在 iso 下唯一
### `LimitData`
- `.toLimit` — `LimitData` ⟹ `Limit`
### `CoLimitData`
- `.toCoLimit` — `CoLimitData` ⟹ `CoLimit`
-/

namespace CategoryTheory

/-- `Limit F`：`F` 有 limit，即 `Hom[Δᵒᵖ–, F] ≅ Hom[–, obj]` -/
class Limit (F : J ⥤ C) where
  obj : C.obj
  rep : Hom[Δᵒᵖ–, F] ≅ Hom[–, obj]

/-- `CoLimit F`：`F` 有 colimit，即 `Hom[obj, –] ≅ Hom[F, Δ–]` -/
class CoLimit (F : J ⥤ C) where
  obj : C.obj
  rep : Hom[obj, –] ≅ Hom[F, Δ–]

-- ─── LimitData / CoLimitData ──────────────────────────────────────────────────

/-- `LimitData F`：limit cone `cone`、universal `lift` -/
structure LimitData (F : J ⥤ C) where
  obj : C.obj
  cone : Δ[obj] ⇒ F
  lift (φ : Δ[X] ⇒ F) : X ⟶ obj
  lift_π (φ : Δ[X] ⇒ F) (j : J.obj) : cone·j ○ lift φ = φ·j
  lift_unique (φ : Δ[X] ⇒ F) (k : X ⟶ obj)
      (hk : ∀ j : J.obj, cone·j ○ k = φ·j) : k = lift φ

/-- `CoLimitData F`：colimit cocone `cocone`、universal `desc` -/
structure CoLimitData (F : J ⥤ C) where
  obj : C.obj
  cocone : F ⇒ Δ[obj]
  desc (φ : F ⇒ Δ[X]) : obj ⟶ X
  desc_ι (φ : F ⇒ Δ[X]) (j : J.obj) : desc φ ○ cocone·j = φ·j
  desc_unique (φ : F ⇒ Δ[X]) (k : obj ⟶ X)
      (hk : ∀ j : J.obj, k ○ cocone·j = φ·j) : k = desc φ

-- ─── Limit ────────────────────────────────────────────────────────────────────

/-- `Limit F` ⟹ `CoUniversal Δ F` -/
instance Limit.universal [h : Limit F] : CoUniversal Δ F where
  obj := h.obj
  rep := h.rep

/-- `Limit` ⟹ `LimitData` -/
@[reducible]
noncomputable def Limit.data [Limit F] : LimitData F where
  obj      := Limit.universal.data.obj
  cone     := Limit.universal.data.morphism
  lift φ   := Limit.universal.data.factor φ
  lift_π φ j := by simpa using (NatTrans.congr_app (Limit.universal.data.factorization φ) j).symm
  lift_unique φ k hk :=
    Limit.universal.data.factor_unique φ k (by ext j; simpa using (hk j).symm)

/-- `LimitData` ⟹ `Limit` -/
instance LimitData.toLimit {F : J ⥤ C} (l : LimitData F) : Limit F :=
  let u := CoUniversalData.toCoUniversal {
    obj             := l.obj
    morphism        := l.cone
    factor          := l.lift
    factorization φ := by ext j; simpa using (l.lift_π φ j).symm
    factor_unique φ k hk := l.lift_unique φ k fun j => by
      simpa using (NatTrans.congr_app hk j).symm
  }
  { obj := u.obj, rep := u.rep }

/-- Limit 在 iso 下唯一 -/
noncomputable def Limit.unique
    {F : J ⥤ C} (h₁ h₂ : Limit F) : h₁.obj ≅ h₂.obj :=
  let u₁ : CoUniversal Δ F := Limit.universal (h := h₁)
  let u₂ : CoUniversal Δ F := Limit.universal (h := h₂)
  CoUniversal.unique u₁ u₂

-- ─── CoLimit ──────────────────────────────────────────────────────────────────

/-- `CoLimit F` ⟹ `Universal Δ F` -/
instance CoLimit.universal [h : CoLimit F] : Universal Δ F where
  obj := h.obj
  rep := h.rep

/-- `CoLimit` ⟹ `CoLimitData` -/
@[reducible]
noncomputable def CoLimit.data [CoLimit F] : CoLimitData F where
  obj    := CoLimit.universal.data.obj
  cocone := CoLimit.universal.data.morphism
  desc φ := CoLimit.universal.data.factor φ
  desc_ι φ j := by simpa using (NatTrans.congr_app (CoLimit.universal.data.factorization φ) j).symm
  desc_unique φ k hk :=
    CoLimit.universal.data.factor_unique φ k (by ext j; simpa using (hk j).symm)

/-- `CoLimitData` ⟹ `CoLimit` -/
instance CoLimitData.toCoLimit {F : J ⥤ C} (l : CoLimitData F) : CoLimit F :=
  let u := UniversalData.toUniversal {
    obj             := l.obj
    morphism        := l.cocone
    factor          := l.desc
    factorization φ := by ext j; simpa using (l.desc_ι φ j).symm
    factor_unique φ k hk := l.desc_unique φ k fun j => by
      simpa using (NatTrans.congr_app hk j).symm
  }
  { obj := u.obj, rep := u.rep }

/-- CoLimit 在 iso 下唯一 -/
noncomputable def CoLimit.unique
    {F : J ⥤ C} (h₁ h₂ : CoLimit F) : h₁.obj ≅ h₂.obj :=
  let u₁ : Universal Δ F := CoLimit.universal (h := h₁)
  let u₂ : Universal Δ F := CoLimit.universal (h := h₂)
  Universal.unique u₁ u₂

end CategoryTheory
