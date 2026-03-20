import MATH.Category.Limits.Complete
import MATH.Category.Structure.Shapes

/-!
# Limits/Shapes/Product.lean

Indexed product / coproduct：discrete 圖的 limit / colimit。

## 定義
- `Product f` — `Limit (discreteFunctor f)`
- `CoProduct f` — `CoLimit (discreteFunctor f)`
- `ProductData f` — product object `obj`、projections `π`、universal `lift`
- `CoProductData f` — coproduct object `obj`、injections `ι`、universal `desc`

## 定理
### `Product`
- `.data` — `Product` ⟹ `ProductData`
- `.unique` — product 在 iso 下唯一
- `ShapeComplete.Product` — `ShapeComplete` ⟹ `Product`
### `ProductData`
- `.toProduct` — `ProductData` ⟹ `Product`
### `CoProduct`
- `.data` — `CoProduct` ⟹ `CoProductData`
- `.unique` — coproduct 在 iso 下唯一
- `ShapeCoComplete.CoProduct` — `ShapeCoComplete` ⟹ `CoProduct`
### `CoProductData`
- `.toCoProduct` — `CoProductData` ⟹ `CoProduct`
-/

namespace CategoryTheory

variable {C : Category} {α : Type u} (f : α → C.obj)

/-- Indexed product：`Limit (discreteFunctor f)` -/
class Product extends Limit (discreteFunctor f)

/-- Indexed coproduct：`CoLimit (discreteFunctor f)` -/
class CoProduct extends CoLimit (discreteFunctor f)

/-- Indexed product：product object `obj`、projections `π`、universal `lift` -/
structure ProductData where
  obj : C.obj
  π a : obj ⟶ f a
  lift (g : ∀ a, Z ⟶ f a) : Z ⟶ obj
  lift_π (g : ∀ a, Z ⟶ f a) (a : α) : π a ○ lift g = g a
  lift_unique (g : ∀ a, Z ⟶ f a) (k : Z ⟶ obj)
      (hk : ∀ a, π a ○ k = g a) : k = lift g

/-- Indexed coproduct：coproduct object `obj`、injections `ι`、universal `desc` -/
structure CoProductData where
  obj : C.obj
  ι a : f a ⟶ obj
  desc (g : ∀ a, f a ⟶ Z) : obj ⟶ Z
  desc_ι (g : ∀ a, f a ⟶ Z) (a : α) : desc g ○ ι a = g a
  desc_unique (g : ∀ a, f a ⟶ Z) (k : obj ⟶ Z)
      (hk : ∀ a, k ○ ι a = g a) : k = desc g

-- ─── Product ──────────────────────────────────────────────────────────────────

namespace Product

/-- `Product` ⟹ `ProductData` -/
noncomputable def data [h : Product f] : ProductData f :=
  let ld := Limit.data
  { obj           := h.obj
    π a           := ld.cone·a
    lift g        := ld.lift { app a := g a
                               naturality h := by rcases h with ⟨rfl⟩; simp }
    lift_π g a    := ld.lift_π _ a
    lift_unique g k hk := ld.lift_unique _ k (fun a => hk a) }

/-- Product 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Product f) : h₁.obj ≅ h₂.obj :=
  Limit.unique h₁.toLimit h₂.toLimit

instance (priority := 100) ShapeComplete.Product
    [h : ShapeComplete (DiscreteCat α) C] : Product f where
  obj := (h.hasLimit (discreteFunctor f)).obj
  rep := (h.hasLimit (discreteFunctor f)).rep

end Product

/-- family `f` 的 product object -/
def Function.Product [h : Product f] := h.obj
notation "∏" f => Function.Product f

/-- `ProductData` ⟹ `Product` -/
instance ProductData.toProduct (pd : ProductData f) : Product f where
  obj := pd.obj
  rep := (LimitData.toLimit {
    obj  := pd.obj
    cone := show Δ[pd.obj] ⇒ discreteFunctor f from {
      app a := pd.π a
      naturality h := by rcases h with ⟨rfl⟩; simp }
    lift φ := pd.lift (fun a => φ·a)
    lift_π φ a := pd.lift_π _ a
    lift_unique φ k hk := pd.lift_unique _ k (fun a => hk a)
  }).rep

-- ─── CoProduct ────────────────────────────────────────────────────────────────

namespace CoProduct

/-- `CoProduct` ⟹ `CoProductData` -/
noncomputable def data [h : CoProduct f] : CoProductData f :=
  let cd := CoLimit.data
  { obj            := h.obj
    ι a            := cd.cocone·a
    desc g         := cd.desc { app a := g a
                                naturality h := by rcases h with ⟨rfl⟩; simp }
    desc_ι g a     := cd.desc_ι _ a
    desc_unique g k hk := cd.desc_unique _ k (fun a => hk a) }

/-- Coproduct 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : CoProduct f) : h₁.obj ≅ h₂.obj :=
  CoLimit.unique h₁.toCoLimit h₂.toCoLimit

instance (priority := 100) ShapeCoComplete.CoProduct
    [h : ShapeCoComplete (DiscreteCat α) C] : CoProduct f where
  obj := (h.hasCoLimit (discreteFunctor f)).obj
  rep := (h.hasCoLimit (discreteFunctor f)).rep

end CoProduct

/-- family `f` 的 coproduct object -/
def Function.CoProduct [h : CoProduct f] := h.obj
notation "⨿" f => Function.CoProduct f

/-- `CoProductData` ⟹ `CoProduct` -/
instance CoProductData.toCoProduct (cpd : CoProductData f) : CoProduct f where
  obj := cpd.obj
  rep := (CoLimitData.toCoLimit {
    obj    := cpd.obj
    cocone := show discreteFunctor f ⇒ Δ[cpd.obj] from {
      app a := cpd.ι a
      naturality h := by rcases h with ⟨rfl⟩; simp }
    desc φ := cpd.desc (fun a => φ·a)
    desc_ι φ a := cpd.desc_ι _ a
    desc_unique φ k hk := cpd.desc_unique _ k (fun a => hk a)
  }).rep

end CategoryTheory
