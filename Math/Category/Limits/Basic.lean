import MATH.Category.UniversalProperty
import MATH.Category.Functor.Const

/-!
# Limits/Basic.lean

Limit / colimit。

## 定義
- `Limit F` — `F` 有 limit（extends `CoUniversal Δ F`）
- `CoLimit F` — `F` 有 colimit（extends `Universal Δ F`）
- `LimitData F` — limit cone `cone`、universal `lift`
- `CoLimitData F` — colimit cocone `cocone`、universal `desc`

## 定理
### `Limit`
- `.data` — `Limit` ⟹ `LimitData`
- `.unique` — limit 在 iso 下唯一
- `.ofNatIso` — `F ≅ G → Limit F → Limit G`
- `.ofObjIso` — `obj ≅ B → Limit F → Limit F`（改 limit object）
### `CoLimit`
- `.data` — `CoLimit` ⟹ `CoLimitData`
- `.unique` — colimit 在 iso 下唯一
- `.ofNatIso` — `F ≅ G → CoLimit F → CoLimit G`
- `.ofObjIso` — `obj ≅ B → CoLimit F → CoLimit F`（改 colimit object）
### `LimitData`
- `.toLimit` — `LimitData` ⟹ `Limit`
### `CoLimitData`
- `.toCoLimit` — `CoLimitData` ⟹ `CoLimit`
-/

namespace CategoryTheory

/-- `Limit F`：`F` 有 limit -/
class Limit (F : J ⥤ C) extends CoUniversal Δ F

/-- `CoLimit F`：`F` 有 colimit -/
class CoLimit (F : J ⥤ C) extends Universal Δ F

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
noncomputable def Limit.data [h : Limit F] : LimitData F :=
  let d := h.toCoUniversal.data
  { obj      := d.obj
    cone     := d.morphism
    lift φ   := d.factor φ
    lift_π φ j := by simpa using (NatTrans.congr_app (d.factorization φ) j).symm
    lift_unique φ k hk :=
      d.factor_unique φ k (by ext j; simpa using (hk j).symm) }

/-- `LimitData` ⟹ `Limit` -/
instance LimitData.toLimit {F : J ⥤ C} (l : LimitData F) : Limit F :=
  { toCoUniversal := CoUniversalData.toCoUniversal {
      obj             := l.obj
      morphism        := l.cone
      factor          := l.lift
      factorization φ := by ext j; simpa using (l.lift_π φ j).symm
      factor_unique φ k hk := l.lift_unique φ k fun j => by
        simpa using (NatTrans.congr_app hk j).symm } }

/-- Limit 在 iso 下唯一 -/
noncomputable def Limit.unique
    {F : J ⥤ C} (h₁ h₂ : Limit F) : h₁.obj ≅ h₂.obj :=
  CoUniversal.unique h₁.toCoUniversal h₂.toCoUniversal

/-- 沿 functor 的 natural isomorphism 轉移 -/
@[reducible]
def Limit.ofNatIso (h : Limit F) (iso : F ≅ G) : Limit G :=
  { toCoUniversal := h.toCoUniversal.ofIso iso }

/-- 沿 limit object 的 isomorphism 轉移 -/
@[reducible]
def Limit.ofObjIso (h : Limit F) (iso : h.obj ≅ B) : Limit F :=
  { toCoUniversal := h.toCoUniversal.ofObjIso iso }

-- ─── CoLimit ──────────────────────────────────────────────────────────────────

/-- `CoLimit` ⟹ `CoLimitData` -/
@[reducible]
noncomputable def CoLimit.data [h : CoLimit F] : CoLimitData F :=
  let d := h.toUniversal.data
  { obj    := d.obj
    cocone := d.morphism
    desc φ := d.factor φ
    desc_ι φ j := by simpa using (NatTrans.congr_app (d.factorization φ) j).symm
    desc_unique φ k hk :=
      d.factor_unique φ k (by ext j; simpa using (hk j).symm) }

/-- `CoLimitData` ⟹ `CoLimit` -/
instance CoLimitData.toCoLimit {F : J ⥤ C} (l : CoLimitData F) : CoLimit F :=
  { toUniversal := UniversalData.toUniversal {
      obj             := l.obj
      morphism        := l.cocone
      factor          := l.desc
      factorization φ := by ext j; simpa using (l.desc_ι φ j).symm
      factor_unique φ k hk := l.desc_unique φ k fun j => by
        simpa using (NatTrans.congr_app hk j).symm } }

/-- CoLimit 在 iso 下唯一 -/
noncomputable def CoLimit.unique
    {F : J ⥤ C} (h₁ h₂ : CoLimit F) : h₁.obj ≅ h₂.obj :=
  Universal.unique h₁.toUniversal h₂.toUniversal

/-- 沿 functor 的 natural isomorphism 轉移 -/
@[reducible]
def CoLimit.ofNatIso (h : CoLimit F) (iso : F ≅ G) : CoLimit G :=
  { toUniversal := h.toUniversal.ofIso iso }

/-- 沿 colimit object 的 isomorphism 轉移 -/
@[reducible]
def CoLimit.ofObjIso (h : CoLimit F) (iso : h.obj ≅ B) : CoLimit F :=
  { toUniversal := h.toUniversal.ofObjIso iso }

end CategoryTheory
