import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const

/-!
# Limits/Basic.lean

Limit / colimit。

## 定義
- `HasLimit` — `F` 有 limit（couniversal cone）
- `HascoLimit` — `F` 有 colimit（universal cocone）

## 定理
### `HasLimit`
- `.ofUniversal` — 從 cone + IscoUniversal 構造
- `.Cone` — limit cone
- `.factor` — 從任意 cone 取得唯一態射到 limit
- `.factor_cone` — factoring property
- `.factor_unique` — 唯一性
### `HascoLimit`
- `.ofUniversal` — 從 cocone + IsUniversal 構造
- `.coCone` — colimit cocone
- `.factor` — 從任意 cocone 取得唯一態射從 colimit
- `.factor_cone` — factoring property
- `.factor_unique` — 唯一性
-/

namespace CategoryTheory

/-- `HasLimit F`：`F` 有 limit。

In other words, `Hom[Δᵒᵖ–, F] ≅ Hom[–, lim F]`. -/
class HasLimit (F : J ⥤ C) where
  lim : C.obj
  universal : coUniversal Δ F lim

/-- 從 cone + IscoUniversal 構造 HasLimit -/
@[reducible]
noncomputable def HasLimit.ofCone {J C : Category} {F : J ⥤ C}
    (lim : C.obj) (cone : Δ[lim] ⟶[⟦J, C⟧] F)
    (h : IscoUniversal (D := ⟦J, C⟧) (F := Δ) cone) : HasLimit F where
  lim := lim
  universal := IscoUniversal.coUniversal cone h

namespace HasLimit

variable {J C : Category} {F : J ⥤ C} (h : HasLimit F)

/-- Limit cone：`Δ[lim] ⇒ F` -/
abbrev Cone : Δ[h.lim] ⇒ F := h.universal.morphism

/-- Limit 在 iso 下唯一 -/
noncomputable def unique (h₁ h₂ : HasLimit F) : h₁.lim ≅ h₂.lim :=
  coUniversal.uniqueUpToIso h₁.universal h₂.universal

/-- 從任意 cone `φ : Δ[Y] ⇒ F` 取得唯一態射 `Y ⟶ lim F` -/
abbrev factor {Y : C.obj} (φ : Δ[Y] ⇒ F) : Y ⟶ h.lim :=
  h.universal·Y φ

/-- factoring property：`φ = h.Cone ○ Δ[factor φ]` -/
lemma factor_cone {Y : C.obj} (φ : Δ[Y] ⇒ F) :
    φ = h.Cone ○[⟦J, C⟧] Δ[h.factor φ] :=
  h.universal.factorization Y φ

/-- 唯一性：若 `φ = h.Cone ○ Δ[f]`，則 `f = factor φ` -/
lemma factor_unique {Y : C.obj} (φ : Δ[Y] ⇒ F) (f : Y ⟶ h.lim)
    (hf : φ = h.Cone ○[⟦J, C⟧] Δ[f]) : f = h.factor φ := by
  -- u⁻¹·Y f = Cone ○ Δ[f]（由 naturality）
  have key : h.universal⁻¹·Y f = h.Cone ○[⟦J, C⟧] Δ[f] := by
    simpa using congrFun (h.universal.inv.naturality f) (𝟙 h.lim)
  -- u⁻¹·Y f = φ
  have eq : h.universal⁻¹·Y f = φ := key.trans hf.symm
  -- f = u·Y (u⁻¹·Y f) = u·Y φ = factor φ
  have cancel : h.universal·Y (h.universal⁻¹·Y f) = f :=
    congrFun (NatIso.hom_inv_id_app h.universal Y) f
  rw [eq] at cancel
  exact cancel.symm

end HasLimit

/-- `HascoLimit F`：`F` 有 colimit。

In other words, `Hom[colim F, –] ≅ Hom[F, Δ–]`. -/
class HascoLimit (F : J ⥤ C) where
  colim : C.obj
  universal : Universal Δ F colim

/-- 從 cocone + IsUniversal 構造 HascoLimit -/
@[reducible]
noncomputable def HascoLimit.ofcoCone (colim : C.obj)
    (cocone : (F : ⟦J, C⟧.obj) ⟶ Δ[colim])
    (h : IsUniversal (C := ⟦J, C⟧) (G := Δ) cocone) : HascoLimit F where
  colim := colim
  universal := IsUniversal.Universal cocone h

namespace HascoLimit

variable {J C : Category} {F : J ⥤ C} (h : HascoLimit F)

/-- Colimit cocone：`F ⇒ Δ[colim]` -/
abbrev coCone : F ⇒ Δ[h.colim] := h.universal.morphism

/-- Colimit 在 iso 下唯一 -/
noncomputable def unique (h₁ h₂ : HascoLimit F) : h₁.colim ≅ h₂.colim :=
  Universal.uniqueUpToIso h₁.universal h₂.universal

/-- 從任意 cocone `φ : F ⇒ Δ[Y]` 取得唯一態射 `colim F ⟶ Y` -/
abbrev factor {Y : C.obj} (φ : F ⇒ Δ[Y]) : h.colim ⟶ Y :=
  h.universal⁻¹·Y φ

/-- factoring property：`φ = Δ[factor φ] ○ h.coCone` -/
lemma factor_cone {Y : C.obj} (φ : F ⇒ Δ[Y]) :
    φ = Δ[h.factor φ] ○[⟦J, C⟧] h.coCone :=
  h.universal.factorization Y φ

/-- 唯一性：若 `φ = Δ[f] ○ h.coCone`，則 `f = factor φ` -/
lemma factor_unique {Y : C.obj} (φ : F ⇒ Δ[Y]) (f : h.colim ⟶ Y)
    (hf : φ = Δ[f] ○[⟦J, C⟧] h.coCone) : f = h.factor φ := by
  -- u·Y f = Δ[f] ○ coCone（由 naturality）
  have key : h.universal·Y f = Δ[f] ○[⟦J, C⟧] h.coCone := by
    simpa using congrFun (h.universal.hom.naturality f) (𝟙 h.colim)
  -- u·Y f = φ
  have eq : h.universal·Y f = φ := key.trans hf.symm
  -- f = u⁻¹·Y (u·Y f) = u⁻¹·Y φ = factor φ
  have cancel : h.universal⁻¹·Y (h.universal·Y f) = f :=
    congrFun (NatIso.inv_hom_id_app h.universal Y) f
  rw [eq] at cancel
  exact cancel.symm

end HascoLimit

end CategoryTheory
