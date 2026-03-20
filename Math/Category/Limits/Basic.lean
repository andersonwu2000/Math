import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const

/-!
# Limits/Basic.lean

Limit / colimit。

## 定義
- `Limit F` — `F` 有 limit，即 `CoUniversal Δ F lim`
- `CoLimit F` — `F` 有 colimit，即 `Universal Δ F colim`
- `LimitData F` — limit cone `cone`、universal `lift`
- `CoLimitData F` — colimit cocone `cocone`、universal `desc`

## 定理
### `Limit`
- `.data` — `Limit` ⟹ `LimitData`
- `.unique` — limit 在 iso 下唯一
### `CoLimit`
- `.data` — `CoLimit` ⟹ `CoLimitData`
- `.unique` — colimit 在 iso 下唯一
### `LimitData`
- `.toLimit` — `LimitData` ⟹ `Limit`
### `CoLimitData`
- `.toCoLimit` — `CoLimitData` ⟹ `CoLimit`
-/

namespace CategoryTheory

/-- `Limit F`：`F` 有 limit，即 `CoUniversal Δ F lim` -/
class Limit (F : J ⥤ C) where
  lim : C.obj
  universal : CoUniversal Δ F lim

/-- `CoLimit F`：`F` 有 colimit，即 `Universal Δ F colim` -/
class CoLimit (F : J ⥤ C) where
  colim : C.obj
  universal : Universal Δ F colim

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

/-- `Limit` ⟹ `LimitData` -/
@[reducible]
noncomputable def Limit.data {F : J ⥤ C} (h : Limit F) : LimitData F where
  obj      := h.lim
  cone     := h.universal.data.morphism
  lift φ   := h.universal.data.factor φ
  lift_π φ j := by
    have := NatTrans.congr_app (h.universal.data.factorization φ) j
    simp at this; exact this.symm
  lift_unique φ k hk :=
    h.universal.data.factor_unique φ k (by ext j; simpa using (hk j).symm)

/-- `LimitData` ⟹ `Limit` -/
@[reducible]
noncomputable def LimitData.toLimit {F : J ⥤ C} (l : LimitData F) : Limit F where
  lim := l.obj
  universal := ({
    morphism    := l.cone
    factor      := l.lift
    factorization φ := by ext j; simpa using (l.lift_π φ j).symm
    factor_unique φ k hk := l.lift_unique φ k fun j => by
      have := NatTrans.congr_app hk j; simp at this; exact this.symm
  } : CoUniversalData Δ F l.obj).CoUniversal

/-- Limit 在 iso 下唯一 -/
noncomputable def Limit.unique {F : J ⥤ C} (h₁ h₂ : Limit F) : h₁.lim ≅ h₂.lim :=
  CoUniversal.unique h₁.universal h₂.universal

-- ─── CoLimit ──────────────────────────────────────────────────────────────────

/-- `CoLimit` ⟹ `CoLimitData` -/
@[reducible]
noncomputable def CoLimit.data {F : J ⥤ C} (h : CoLimit F) : CoLimitData F where
  obj    := h.colim
  cocone := h.universal.data.morphism
  desc φ := h.universal.data.factor φ
  desc_ι φ j := by
    have := NatTrans.congr_app (h.universal.data.factorization φ) j
    simp at this; exact this.symm
  desc_unique φ k hk :=
    h.universal.data.factor_unique φ k (by ext j; simpa using (hk j).symm)

/-- `CoLimitData` ⟹ `CoLimit` -/
@[reducible]
noncomputable def CoLimitData.toCoLimit {F : J ⥤ C} (l : CoLimitData F) : CoLimit F where
  colim := l.obj
  universal := ({
    morphism    := l.cocone
    factor      := l.desc
    factorization φ := by ext j; simpa using (l.desc_ι φ j).symm
    factor_unique φ k hk := l.desc_unique φ k fun j => by
      have := NatTrans.congr_app hk j; simp at this; exact this.symm
  } : UniversalData Δ F l.obj).Universal

/-- CoLimit 在 iso 下唯一 -/
noncomputable def CoLimit.unique {F : J ⥤ C} (h₁ h₂ : CoLimit F) : h₁.colim ≅ h₂.colim :=
  Universal.unique h₁.universal h₂.universal

end CategoryTheory
