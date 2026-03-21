import MATH.Category.Limits.Shapes.InitialTerminal
import MATH.Category.Limits.Shapes.BinaryProduct
import MATH.Category.Limits.Shapes.Product
import MATH.Category.Limits.Shapes.Equalizer
import MATH.Category.Limits.Shapes.Pullback
import MATH.Category.Structure.Types

/-!
# Limits/Instances/Types.lean

`Types` 範疇的 limit shape 實例。

## 定理
### `Types`
- `Initial Types` — initial object = `PEmpty`
- `Terminal Types` — terminal object = `PUnit`
- `BinaryProduct A B` — binary product = `A × B`
- `BinaryCoproduct A B` — binary coproduct = `A ⊕ B`
- `Product f` — indexed product = `(a : α) → f a`
- `CoProduct f` — indexed coproduct = `Σ a, f a`
- `Equalizer f g` — equalizer = `{x // f x = g x}`
- `Pullback f g` — pullback = `{p : A × B // f p.1 = g p.2}`
-/

namespace CategoryTheory

-- ─── Initial / Terminal ───────────────────────────────────────────────────────

/-- `Types` 的 initial object 為 `PEmpty`：唯一態射 `PEmpty → X` 是 `PEmpty.elim` -/
noncomputable instance Types_Initial : Initial Types :=
  InitialData.toInitial (C := Types) {
    obj := PEmpty
    map _ := PEmpty.elim
    map_unique _ := funext fun x => x.elim }

/-- `Types` 的 terminal object 為 `PUnit`：唯一態射 `X → PUnit` 是常數函數 -/
noncomputable instance Types_Terminal : Terminal Types :=
  TerminalData.toTerminal (C := Types) {
    obj := PUnit
    map _ := fun _ => PUnit.unit
    map_unique _ := funext fun _ => Subsingleton.elim _ _ }

-- ─── BinaryProduct ────────────────────────────────────────────────────────────

/-- `Types` 的 binary product：`A × B` with `Prod.fst` / `Prod.snd` -/
noncomputable instance Types_BinaryProduct
    (A B : Types.obj) : BinaryProduct (C := Types) A B :=
  BinaryProductData.toBinaryProduct (A := A) (B := B) {
    obj := A × B
    π₁ := Prod.fst
    π₂ := Prod.snd
    lift h₁ h₂ x := (h₁ x, h₂ x)
    lift_π₁ _ _ := rfl
    lift_π₂ _ _ := rfl
    lift_unique _ _ _ hk₁ hk₂ :=
      funext fun x => Prod.ext (congrFun hk₁ x) (congrFun hk₂ x) }

-- ─── BinaryCoproduct ──────────────────────────────────────────────────────────

/-- `Types` 的 binary coproduct：`A ⊕ B` with `Sum.inl` / `Sum.inr` -/
noncomputable instance Types_BinaryCoproduct
    (A B : Types.obj) : BinaryCoproduct (C := Types) A B :=
  BinaryCoproductData.toBinaryCoproduct (A := A) (B := B) {
    obj := A ⊕ B
    ι₁ := Sum.inl
    ι₂ := Sum.inr
    desc h₁ h₂ := Sum.elim h₁ h₂
    desc_ι₁ _ _ := rfl
    desc_ι₂ _ _ := rfl
    desc_unique _ _ _ hk₁ hk₂ := funext fun
      | .inl a => congrFun hk₁ a
      | .inr b => congrFun hk₂ b }

-- ─── Product ──────────────────────────────────────────────────────────────────

/-- `Types` 的 indexed product：`(a : α) → f a` with pointwise projection -/
noncomputable instance Types_Product
    (f : α → Types.obj) : Product (C := Types) f :=
  ProductData.toProduct (f := f) {
    obj := (a : α) → f a
    π a g := g a
    lift gs x a := gs a x
    lift_π _ _ := rfl
    lift_unique _ _ hk :=
      funext fun x => funext fun a => congrFun (hk a) x }

-- ─── CoProduct ────────────────────────────────────────────────────────────────

/-- `Types` 的 indexed coproduct：`Σ a, f a` with sigma injection -/
noncomputable instance Types_CoProduct
    (f : α → Types.obj) : CoProduct (C := Types) f :=
  CoProductData.toCoProduct (f := f) {
    obj := Σ a, f a
    ι a x := ⟨a, x⟩
    desc gs | ⟨a, x⟩ => gs a x
    desc_ι _ _ := rfl
    desc_unique _ _ hk :=
      funext fun ⟨a, x⟩ => congrFun (hk a) x }

-- ─── Equalizer ────────────────────────────────────────────────────────────────

/-- `Types` 的 equalizer：`{x : A // f x = g x}` -/
noncomputable instance Types_Equalizer
    (f g : A ⟶[Types] B) : Equalizer (C := Types) f g :=
  EqualizerData.toEqualizer (f := f) (g := g) {
    obj := { x : A // f x = g x }
    π := Subtype.val
    cond := funext fun ⟨_, h⟩ => h
    lift h hh x := ⟨h x, congrFun hh x⟩
    lift_π _ _ := rfl
    lift_unique _ _ _ hk :=
      funext fun x => Subtype.ext (congrFun hk x) }

-- ─── Pullback ─────────────────────────────────────────────────────────────────

/-- `Types` 的 pullback：`{p : A × B // f p.1 = g p.2}` -/
noncomputable instance Types_Pullback
    (f : A ⟶[Types] X) (g : B ⟶[Types] X) :
    Pullback (C := Types) f g :=
  PullbackData.toPullback (f := f) (g := g) {
    obj := { p : A × B // f p.1 = g p.2 }
    π₁ p := p.val.1
    π₂ p := p.val.2
    cond := funext fun ⟨_, h⟩ => h
    lift h₁ h₂ hc x := ⟨(h₁ x, h₂ x), congrFun hc x⟩
    lift_π₁ _ _ _ := rfl
    lift_π₂ _ _ _ := rfl
    lift_unique _ _ _ _ hk₁ hk₂ := funext fun x =>
      Subtype.ext (Prod.ext (congrFun hk₁ x) (congrFun hk₂ x)) }

end CategoryTheory
