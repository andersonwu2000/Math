import MATH.Category.Limits.Complete
import MATH.Category.Structure.Shapes

/-!
# Limits/Shapes/BinaryProduct.lean

Binary product / coproduct：兩個 object 的 product / coproduct。

## 定義
- `BinaryFamily A B` — binary product / coproduct 的 index family
- `BinaryProduct A B` — `Limit (discreteFunctor (BinaryFamily A B))`
- `BinaryCoproduct A B` — `CoLimit (discreteFunctor (BinaryFamily A B))`
- `BinaryProductData A B` — binary product object `obj`、projections `π₁` `π₂`、universal `lift`
- `BinaryCoproductData A B` — binary coproduct object `obj`、injections `ι₁` `ι₂`、universal `desc`
- `Prod.BinaryProduct` — `A` 和 `B` 的 binary product object
- `Prod.BinaryCoproduct` — `A` 和 `B` 的 binary coproduct object

## 定理
### `BinaryProduct`
- `.data` — `BinaryProduct` ⟹ `BinaryProductData`
- `.unique` — binary product 在 iso 下唯一
- `ShapeComplete.BinaryProduct` — `ShapeComplete` ⟹ `BinaryProduct`
### `BinaryProductData`
- `.toBinaryProduct` — `BinaryProductData` ⟹ `BinaryProduct`
### `BinaryCoproduct`
- `.data` — `BinaryCoproduct` ⟹ `BinaryCoproductData`
- `.unique` — binary coproduct 在 iso 下唯一
- `ShapeCoComplete.BinaryCoproduct` — `ShapeCoComplete` ⟹ `BinaryCoproduct`
### `BinaryCoproductData`
- `.toBinaryCoproduct` — `BinaryCoproductData` ⟹ `BinaryCoproduct`
-/

namespace CategoryTheory

variable {C : Category} (A B : C.obj)

/-- Binary product / coproduct 的 index family -/
def BinaryFamily : Bool → C.obj
  | false => A
  | true  => B

/-- Binary product：`Limit (discreteFunctor (BinaryFamily A B))` -/
class BinaryProduct extends Limit (discreteFunctor (BinaryFamily A B))

/-- Binary coproduct：`CoLimit (discreteFunctor (BinaryFamily A B))` -/
class BinaryCoproduct extends CoLimit (discreteFunctor (BinaryFamily A B))

/-- Binary product：binary product object `obj`、projections `π₁` `π₂`、universal `lift` -/
structure BinaryProductData where
  obj : C.obj
  π₁ : obj ⟶ A
  π₂ : obj ⟶ B
  lift (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) : Z ⟶ obj
  lift_π₁ (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) : π₁ ○ lift h₁ h₂ = h₁
  lift_π₂ (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) : π₂ ○ lift h₁ h₂ = h₂
  lift_unique (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) (k : Z ⟶ obj)
      (hk₁ : π₁ ○ k = h₁) (hk₂ : π₂ ○ k = h₂) : k = lift h₁ h₂

/-- Binary coproduct：binary coproduct object `obj`、injections `ι₁` `ι₂`、universal `desc` -/
structure BinaryCoproductData where
  obj : C.obj
  ι₁ : A ⟶ obj
  ι₂ : B ⟶ obj
  desc (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) : obj ⟶ Z
  desc_ι₁ (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) : desc h₁ h₂ ○ ι₁ = h₁
  desc_ι₂ (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) : desc h₁ h₂ ○ ι₂ = h₂
  desc_unique (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) (k : obj ⟶ Z)
      (hk₁ : k ○ ι₁ = h₁) (hk₂ : k ○ ι₂ = h₂) : k = desc h₁ h₂

-- ─── BinaryProduct ───────────────────────────────────────────────────────────

namespace BinaryProduct

/-- `BinaryProduct` ⟹ `BinaryProductData` -/
noncomputable def data [h : BinaryProduct A B] : BinaryProductData A B :=
  let ld := Limit.data
  { obj           := h.obj
    π₁            := ld.cone·false
    π₂            := ld.cone·true
    lift h₁ h₂    := ld.lift {
      app := fun | false => h₁ | true => h₂
      naturality h := by rcases h with ⟨rfl⟩; simp }
    lift_π₁ h₁ h₂ := ld.lift_π _ false
    lift_π₂ h₁ h₂ := ld.lift_π _ true
    lift_unique h₁ h₂ k hk₁ hk₂ :=
      ld.lift_unique _ k (fun | false => hk₁ | true => hk₂) }

/-- Binary product 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : BinaryProduct A B) : h₁.obj ≅ h₂.obj :=
  Limit.unique h₁.toLimit h₂.toLimit

instance (priority := 100) ShapeComplete.BinaryProduct
    [h : ShapeComplete (DiscreteCat Bool) C] : BinaryProduct A B where
  obj := (h.hasLimit (discreteFunctor (BinaryFamily A B))).obj
  rep := (h.hasLimit (discreteFunctor (BinaryFamily A B))).rep

end BinaryProduct

/-- `A` 和 `B` 的 binary product object -/
def Prod.BinaryProduct [h : BinaryProduct A B] := h.obj

/-- `BinaryProductData` ⟹ `BinaryProduct` -/
@[reducible]
noncomputable def BinaryProductData.toBinaryProduct (pd : BinaryProductData A B) :
    BinaryProduct A B where
  obj := pd.obj
  rep := (LimitData.toLimit {
    obj  := pd.obj
    cone := show Δ[pd.obj] ⇒ discreteFunctor (BinaryFamily A B) from {
      app := fun | false => pd.π₁ | true => pd.π₂
      naturality h := by rcases h with ⟨rfl⟩; simp }
    lift φ := pd.lift (φ.app false) (φ.app true)
    lift_π φ a := by
      match a with | false => exact pd.lift_π₁ _ _ | true => exact pd.lift_π₂ _ _
    lift_unique φ k hk :=
      pd.lift_unique _ _ k (hk false) (hk true)
  }).rep

-- ─── BinaryCoproduct ─────────────────────────────────────────────────────────

namespace BinaryCoproduct

/-- `BinaryCoproduct` ⟹ `BinaryCoproductData` -/
noncomputable def data [h : BinaryCoproduct A B] : BinaryCoproductData A B :=
  let cd := CoLimit.data
  { obj            := h.obj
    ι₁             := cd.cocone·false
    ι₂             := cd.cocone·true
    desc h₁ h₂     := cd.desc {
      app := fun | false => h₁ | true => h₂
      naturality h := by rcases h with ⟨rfl⟩; simp }
    desc_ι₁ h₁ h₂  := cd.desc_ι _ false
    desc_ι₂ h₁ h₂  := cd.desc_ι _ true
    desc_unique h₁ h₂ k hk₁ hk₂ :=
      cd.desc_unique _ k (fun | false => hk₁ | true => hk₂) }

/-- Binary coproduct 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : BinaryCoproduct A B) : h₁.obj ≅ h₂.obj :=
  CoLimit.unique h₁.toCoLimit h₂.toCoLimit

instance (priority := 100) ShapeCoComplete.BinaryCoproduct
    [h : ShapeCoComplete (DiscreteCat Bool) C] : BinaryCoproduct A B where
  obj := (h.hasCoLimit (discreteFunctor (BinaryFamily A B))).obj
  rep := (h.hasCoLimit (discreteFunctor (BinaryFamily A B))).rep

end BinaryCoproduct

/-- `A` 和 `B` 的 binary coproduct object -/
def Prod.BinaryCoproduct [h : BinaryCoproduct A B] := h.obj

/-- `BinaryCoproductData` ⟹ `BinaryCoproduct` -/
@[reducible]
noncomputable def BinaryCoproductData.toBinaryCoproduct (cpd : BinaryCoproductData A B) :
    BinaryCoproduct A B where
  obj := cpd.obj
  rep := (CoLimitData.toCoLimit {
    obj    := cpd.obj
    cocone := show discreteFunctor (BinaryFamily A B) ⇒ Δ[cpd.obj] from {
      app := fun | false => cpd.ι₁ | true => cpd.ι₂
      naturality h := by rcases h with ⟨rfl⟩; simp }
    desc φ := cpd.desc (φ.app false) (φ.app true)
    desc_ι φ a := by
      match a with | false => exact cpd.desc_ι₁ _ _ | true => exact cpd.desc_ι₂ _ _
    desc_unique φ k hk :=
      cpd.desc_unique _ _ k (hk false) (hk true)
  }).rep

end CategoryTheory
