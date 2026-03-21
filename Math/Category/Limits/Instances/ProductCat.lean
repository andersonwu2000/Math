import MATH.Category.Limits.Shapes.InitialTerminal
import MATH.Category.Limits.Shapes.BinaryProduct
import MATH.Category.Limits.Shapes.Product
import MATH.Category.Limits.Shapes.Equalizer
import MATH.Category.Limits.Shapes.Pullback
import MATH.Category.Structure.ProductCat

/-!
# Limits/Instances/ProductCat.lean

`ProductCat`（積範疇）的 limit shape 實例——逐分量構造。

## 定理
### `ProductCat`
- `Initial (C × D)` — initial object = `(init_C, init_D)`
- `Terminal (C × D)` — terminal object = `(term_C, term_D)`
- `BinaryProduct (A₁, A₂) (B₁, B₂)` — binary product = `(A₁ ×_C B₁, A₂ ×_D B₂)`
- `BinaryCoproduct (A₁, A₂) (B₁, B₂)` — binary coproduct = `(A₁ ⊔_C B₁, A₂ ⊔_D B₂)`
- `Product f` — indexed product，逐分量（需 `C D : Category.{u, max u v}`）
- `CoProduct f` — indexed coproduct，逐分量（需 `C D : Category.{u, max u v}`）
- `Equalizer (f₁, f₂) (g₁, g₂)` — equalizer，逐分量
- `CoEqualizer (f₁, f₂) (g₁, g₂)` — coequalizer，逐分量
- `Pullback (f₁, f₂) (g₁, g₂)` — pullback，逐分量
- `Pushout (f₁, f₂) (g₁, g₂)` — pushout，逐分量
-/

namespace CategoryTheory

variable {C D : Category}

-- 輔助：從 product category 的態射中取出分量
private abbrev fstHom {X Y : (C × D).obj} (f : X ⟶[C × D] Y) : X.1 ⟶[C] Y.1 := f.1
private abbrev sndHom {X Y : (C × D).obj} (f : X ⟶[C × D] Y) : X.2 ⟶[D] Y.2 := f.2

-- ─── Initial / Terminal ───────────────────────────────────────────────────────

/-- Product category 的 initial object：`(init_C, init_D)` -/
noncomputable instance ProductCat_Initial [hC : Initial C] [hD : Initial D] : Initial (C × D) :=
  let idC := Initial.data C
  let idD := Initial.data D
  InitialData.toInitial (C := C × D) {
    obj := (idC.obj, idD.obj)
    map p := (idC.map p.1, idD.map p.2)
    map_unique f := Prod.ext (idC.map_unique f.1) (idD.map_unique f.2) }

/-- Product category 的 terminal object：`(term_C, term_D)` -/
noncomputable instance ProductCat_Terminal
    [hC : Terminal C] [hD : Terminal D] : Terminal (C × D) :=
  let tdC := Terminal.data C
  let tdD := Terminal.data D
  TerminalData.toTerminal (C := C × D) {
    obj := (tdC.obj, tdD.obj)
    map p := (tdC.map p.1, tdD.map p.2)
    map_unique f := Prod.ext (tdC.map_unique f.1) (tdD.map_unique f.2) }

-- ─── BinaryProduct / BinaryCoproduct ─────────────────────────────────────────

variable {A₁ B₁ : C.obj} {A₂ B₂ : D.obj}

/-- Product category 的 binary product：`((A₁ ×_C B₁), (A₂ ×_D B₂))` -/
noncomputable instance ProductCat_BinaryProduct
    [hC : BinaryProduct A₁ B₁] [hD : BinaryProduct A₂ B₂] :
    BinaryProduct (C := C × D) (A₁, A₂) (B₁, B₂) :=
  let dC := BinaryProduct.data A₁ B₁
  let dD := BinaryProduct.data A₂ B₂
  BinaryProductData.toBinaryProduct (pd :=
    ({ obj := (dC.obj, dD.obj)
       π₁ := (dC.π₁, dD.π₁)
       π₂ := (dC.π₂, dD.π₂)
       lift h₁ h₂ :=
         (dC.lift (fstHom h₁) (fstHom h₂),
          dD.lift (sndHom h₁) (sndHom h₂))
       lift_π₁ _ _ :=
         Prod.ext (dC.lift_π₁ _ _) (dD.lift_π₁ _ _)
       lift_π₂ _ _ :=
         Prod.ext (dC.lift_π₂ _ _) (dD.lift_π₂ _ _)
       lift_unique _ _ k hk₁ hk₂ :=
         Prod.ext
           (dC.lift_unique _ _ k.1
             (congrArg Prod.fst hk₁) (congrArg Prod.fst hk₂))
           (dD.lift_unique _ _ k.2
             (congrArg Prod.snd hk₁) (congrArg Prod.snd hk₂))
     } : BinaryProductData (C := C × D) (A₁, A₂) (B₁, B₂)))

/-- Product category 的 binary coproduct：`((A₁ ⊔_C B₁), (A₂ ⊔_D B₂))` -/
noncomputable instance ProductCat_BinaryCoproduct
    [hC : BinaryCoproduct A₁ B₁] [hD : BinaryCoproduct A₂ B₂] :
    BinaryCoproduct (C := C × D) (A₁, A₂) (B₁, B₂) :=
  let dC := BinaryCoproduct.data A₁ B₁
  let dD := BinaryCoproduct.data A₂ B₂
  BinaryCoproductData.toBinaryCoproduct (cpd :=
    ({ obj := (dC.obj, dD.obj)
       ι₁ := (dC.ι₁, dD.ι₁)
       ι₂ := (dC.ι₂, dD.ι₂)
       desc h₁ h₂ :=
         (dC.desc (fstHom h₁) (fstHom h₂),
          dD.desc (sndHom h₁) (sndHom h₂))
       desc_ι₁ _ _ :=
         Prod.ext (dC.desc_ι₁ _ _) (dD.desc_ι₁ _ _)
       desc_ι₂ _ _ :=
         Prod.ext (dC.desc_ι₂ _ _) (dD.desc_ι₂ _ _)
       desc_unique _ _ k hk₁ hk₂ :=
         Prod.ext
           (dC.desc_unique _ _ k.1
             (congrArg Prod.fst hk₁) (congrArg Prod.fst hk₂))
           (dD.desc_unique _ _ k.2
             (congrArg Prod.snd hk₁) (congrArg Prod.snd hk₂))
     } : BinaryCoproductData (C := C × D) (A₁, A₂) (B₁, B₂)))

-- ─── Product / CoProduct ─────────────────────────────────────────────────────
-- Product / CoProduct 需要 Limit 的 rep 欄位在 universe 上一致
-- 因此限制 C D 為 Category.{u, max u v}

section ProductCoProduct

universe u' v'

variable {C' : Category.{u', max u' v'}} {D' : Category.{u', max u' v'}}

private abbrev fstHom' {X Y : (C' × D').obj} (f : X ⟶[C' × D'] Y) : X.1 ⟶[C'] Y.1 := f.1
private abbrev sndHom' {X Y : (C' × D').obj} (f : X ⟶[C' × D'] Y) : X.2 ⟶[D'] Y.2 := f.2

/-- Product category 的 indexed product：逐分量 -/
noncomputable instance ProductCat_Product
    {α : Type u'} {f : α → (C' × D').obj}
    [hC : Product (fun a => (f a).1)] [hD : Product (fun a => (f a).2)] :
    Product f :=
  let dC := Product.data (fun a => (f a).1)
  let dD := Product.data (fun a => (f a).2)
  ProductData.toProduct (f := f) {
    obj := (dC.obj, dD.obj)
    π a := (dC.π a, dD.π a)
    lift g := (dC.lift (fun a => fstHom' (g a)), dD.lift (fun a => sndHom' (g a)))
    lift_π _ a := Prod.ext (dC.lift_π _ a) (dD.lift_π _ a)
    lift_unique _ k hk :=
      Prod.ext
        (dC.lift_unique _ k.1 (fun a => congrArg Prod.fst (hk a)))
        (dD.lift_unique _ k.2 (fun a => congrArg Prod.snd (hk a))) }

/-- Product category 的 indexed coproduct：逐分量 -/
noncomputable instance ProductCat_CoProduct
    {α : Type u'} {f : α → (C' × D').obj}
    [hC : CoProduct (fun a => (f a).1)] [hD : CoProduct (fun a => (f a).2)] :
    CoProduct f :=
  let dC := CoProduct.data (fun a => (f a).1)
  let dD := CoProduct.data (fun a => (f a).2)
  CoProductData.toCoProduct (f := f) {
    obj := (dC.obj, dD.obj)
    ι a := (dC.ι a, dD.ι a)
    desc g := (dC.desc (fun a => fstHom' (g a)), dD.desc (fun a => sndHom' (g a)))
    desc_ι _ a := Prod.ext (dC.desc_ι _ a) (dD.desc_ι _ a)
    desc_unique _ k hk :=
      Prod.ext
        (dC.desc_unique _ k.1 (fun a => congrArg Prod.fst (hk a)))
        (dD.desc_unique _ k.2 (fun a => congrArg Prod.snd (hk a))) }

end ProductCoProduct

-- ─── Equalizer / CoEqualizer ─────────────────────────────────────────────────

/-- Product category 的 equalizer：逐分量 -/
noncomputable instance ProductCat_Equalizer
    {X Y : (C × D).obj} {f g : X ⟶[C × D] Y}
    [hC : Equalizer (fstHom f) (fstHom g)] [hD : Equalizer (sndHom f) (sndHom g)] :
    Equalizer f g :=
  let dC := Equalizer.data (fstHom f) (fstHom g)
  let dD := Equalizer.data (sndHom f) (sndHom g)
  EqualizerData.toEqualizer (f := f) (g := g) {
    obj := (dC.obj, dD.obj)
    π := (dC.π, dD.π)
    cond := Prod.ext dC.cond dD.cond
    lift h hh :=
      (dC.lift (fstHom h) (congrArg Prod.fst hh),
       dD.lift (sndHom h) (congrArg Prod.snd hh))
    lift_π _ _ := Prod.ext (dC.lift_π _ _) (dD.lift_π _ _)
    lift_unique _ _ k hk :=
      Prod.ext
        (dC.lift_unique _ _ k.1 (congrArg Prod.fst hk))
        (dD.lift_unique _ _ k.2 (congrArg Prod.snd hk)) }

/-- Product category 的 coequalizer：逐分量 -/
noncomputable instance ProductCat_CoEqualizer
    {X Y : (C × D).obj} {f g : X ⟶[C × D] Y}
    [hC : CoEqualizer (fstHom f) (fstHom g)] [hD : CoEqualizer (sndHom f) (sndHom g)] :
    CoEqualizer f g :=
  let dC := CoEqualizer.data (fstHom f) (fstHom g)
  let dD := CoEqualizer.data (sndHom f) (sndHom g)
  CoEqualizerData.toCoEqualizer (f := f) (g := g) {
    obj := (dC.obj, dD.obj)
    ι := (dC.ι, dD.ι)
    cond := Prod.ext dC.cond dD.cond
    desc h hh :=
      (dC.desc (fstHom h) (congrArg Prod.fst hh),
       dD.desc (sndHom h) (congrArg Prod.snd hh))
    desc_ι _ _ := Prod.ext (dC.desc_ι _ _) (dD.desc_ι _ _)
    desc_unique _ _ k hk :=
      Prod.ext
        (dC.desc_unique _ _ k.1 (congrArg Prod.fst hk))
        (dD.desc_unique _ _ k.2 (congrArg Prod.snd hk)) }

-- ─── Pullback / Pushout ──────────────────────────────────────────────────────

/-- Product category 的 pullback：逐分量 -/
noncomputable instance ProductCat_Pullback
    {A B X : (C × D).obj} {f : A ⟶[C × D] X} {g : B ⟶[C × D] X}
    [hC : Pullback (fstHom f) (fstHom g)] [hD : Pullback (sndHom f) (sndHom g)] :
    Pullback f g :=
  let dC := Pullback.data (fstHom f) (fstHom g)
  let dD := Pullback.data (sndHom f) (sndHom g)
  PullbackData.toPullback (f := f) (g := g) {
    obj := (dC.obj, dD.obj)
    π₁ := (dC.π₁, dD.π₁)
    π₂ := (dC.π₂, dD.π₂)
    cond := Prod.ext dC.cond dD.cond
    lift h₁ h₂ hc :=
      (dC.lift (fstHom h₁) (fstHom h₂) (congrArg Prod.fst hc),
       dD.lift (sndHom h₁) (sndHom h₂) (congrArg Prod.snd hc))
    lift_π₁ _ _ _ := Prod.ext (dC.lift_π₁ _ _ _) (dD.lift_π₁ _ _ _)
    lift_π₂ _ _ _ := Prod.ext (dC.lift_π₂ _ _ _) (dD.lift_π₂ _ _ _)
    lift_unique _ _ _ k hk₁ hk₂ :=
      Prod.ext
        (dC.lift_unique _ _ _ k.1 (congrArg Prod.fst hk₁) (congrArg Prod.fst hk₂))
        (dD.lift_unique _ _ _ k.2 (congrArg Prod.snd hk₁) (congrArg Prod.snd hk₂)) }

/-- Product category 的 pushout：逐分量 -/
noncomputable instance ProductCat_Pushout
    {A B X : (C × D).obj} {f : X ⟶[C × D] A} {g : X ⟶[C × D] B}
    [hC : Pushout (fstHom f) (fstHom g)] [hD : Pushout (sndHom f) (sndHom g)] :
    Pushout f g :=
  let dC := Pushout.data (f := fstHom f) (g := fstHom g)
  let dD := Pushout.data (f := sndHom f) (g := sndHom g)
  PushoutData.toPushout (f := f) (g := g) {
    obj := (dC.obj, dD.obj)
    ι₁ := (dC.ι₁, dD.ι₁)
    ι₂ := (dC.ι₂, dD.ι₂)
    cond := Prod.ext dC.cond dD.cond
    desc h₁ h₂ hc :=
      (dC.desc (fstHom h₁) (fstHom h₂) (congrArg Prod.fst hc),
       dD.desc (sndHom h₁) (sndHom h₂) (congrArg Prod.snd hc))
    desc_ι₁ _ _ _ := Prod.ext (dC.desc_ι₁ _ _ _) (dD.desc_ι₁ _ _ _)
    desc_ι₂ _ _ _ := Prod.ext (dC.desc_ι₂ _ _ _) (dD.desc_ι₂ _ _ _)
    desc_unique _ _ _ k hk₁ hk₂ :=
      Prod.ext
        (dC.desc_unique _ _ _ k.1 (congrArg Prod.fst hk₁) (congrArg Prod.fst hk₂))
        (dD.desc_unique _ _ _ k.2 (congrArg Prod.snd hk₁) (congrArg Prod.snd hk₂)) }

end CategoryTheory
