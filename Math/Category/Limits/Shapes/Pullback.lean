import MATH.Category.Limits.Complete
import MATH.Category.Structure.Shapes

/-!
# Limits/Shapes/Pullback.lean

Pullback / pushout：cospan / span 圖的 limit / colimit。

## 定義
- `Pullback f g` — `Limit (cospanFunctor f g)`
- `Pushout f g` — `CoLimit (spanFunctor f g)`
- `PullbackData f g` — pullback object `obj`、projections `π₁` `π₂`、universal `lift`
- `PushoutData f g` — pushout object `obj`、injections `ι₁` `ι₂`、universal `desc`
- `Hom.Pullback` — `f` 和 `g` 的 pullback object
- `Hom.Pushout` — `f` 和 `g` 的 pushout object

## 定理
### `Pullback`
- `.data` — `Pullback` ⟹ `PullbackData`
- `.unique` — pullback 在 iso 下唯一
- `ShapeComplete.Pullback` — `ShapeComplete` ⟹ `Pullback`
### `PullbackData`
- `.toPullback` — `PullbackData` ⟹ `Pullback`
### `Pushout`
- `.data` — `Pushout` ⟹ `PushoutData`
- `.unique` — pushout 在 iso 下唯一
- `ShapeCoComplete.Pushout` — `ShapeCoComplete` ⟹ `Pushout`
### `PushoutData`
- `.toPushout` — `PushoutData` ⟹ `Pushout`
-/

namespace CategoryTheory

variable (f : A ⟶[C] X) (g : B ⟶[C] X)

/-- Pullback：`Limit (cospanFunctor f g)` -/
class Pullback extends Limit (cospanFunctor f g)

/-- Pushout：`CoLimit (spanFunctor f g)` -/
class Pushout (f : X ⟶[C] A) (g : X ⟶[C] B) extends CoLimit (spanFunctor f g)

/-- Pullback：pullback object `obj`、projections `π₁` `π₂`、universal `lift` -/
structure PullbackData where
  obj : C.obj
  π₁ : obj ⟶ A
  π₂ : obj ⟶ B
  cond : f ○ π₁ = g ○ π₂
  lift (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) (hc : f ○ h₁ = g ○ h₂) : Z ⟶ obj
  lift_π₁ (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) (hc : f ○ h₁ = g ○ h₂) : π₁ ○ lift h₁ h₂ hc = h₁
  lift_π₂ (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) (hc : f ○ h₁ = g ○ h₂) : π₂ ○ lift h₁ h₂ hc = h₂
  lift_unique (h₁ : Z ⟶ A) (h₂ : Z ⟶ B) (hc : f ○ h₁ = g ○ h₂) (k : Z ⟶ obj)
      (hk₁ : π₁ ○ k = h₁) (hk₂ : π₂ ○ k = h₂) : k = lift h₁ h₂ hc

/-- Pushout：pushout object `obj`、injections `ι₁` `ι₂`、universal `desc` -/
structure PushoutData (f : X ⟶[C] A) (g : X ⟶[C] B) where
  obj : C.obj
  ι₁ : A ⟶ obj
  ι₂ : B ⟶ obj
  cond : ι₁ ○ f = ι₂ ○ g
  desc (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) (hc : h₁ ○ f = h₂ ○ g) : obj ⟶ Z
  desc_ι₁ (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) (hc : h₁ ○ f = h₂ ○ g) : desc h₁ h₂ hc ○ ι₁ = h₁
  desc_ι₂ (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) (hc : h₁ ○ f = h₂ ○ g) : desc h₁ h₂ hc ○ ι₂ = h₂
  desc_unique (h₁ : A ⟶ Z) (h₂ : B ⟶ Z) (hc : h₁ ○ f = h₂ ○ g) (k : obj ⟶ Z)
      (hk₁ : k ○ ι₁ = h₁) (hk₂ : k ○ ι₂ = h₂) : k = desc h₁ h₂ hc

-- ─── Pullback ────────────────────────────────────────────────────────────────

namespace Pullback

private def mkCone (π₁ : Z ⟶ A) (π₂ : Z ⟶ B) (hc : f ○ π₁ = g ○ π₂) :
    Δ[Z] ⇒ cospanFunctor f g where
  app j := match j with | .left => π₁ | .right => π₂ | .bot => f ○ π₁
  naturality m := by
    match m with
    | .refl x => cases x <;> simp
    | .inl    => simp
    | .inr    => simpa using hc

/-- `Pullback` ⟹ `PullbackData` -/
noncomputable def data [h : Pullback f g] : PullbackData f g :=
  let ld := Limit.data
  { obj  := h.obj
    π₁   := ld.cone·WalkingCospan.left
    π₂   := ld.cone·WalkingCospan.right
    cond := by
      have l := ld.cone.naturality WalkingCospanMor.inl
      have r := ld.cone.naturality WalkingCospanMor.inr
      simpa using l.symm.trans r
    lift h₁ h₂ hc := ld.lift (mkCone f g h₁ h₂ hc)
    lift_π₁ h₁ h₂ hc := by simpa using ld.lift_π (mkCone f g h₁ h₂ hc) WalkingCospan.left
    lift_π₂ h₁ h₂ hc := by simpa using ld.lift_π (mkCone f g h₁ h₂ hc) WalkingCospan.right
    lift_unique h₁ h₂ hc k hk₁ hk₂ :=
      ld.lift_unique (mkCone f g h₁ h₂ hc) k (by
        intro j; cases j
        next => -- bot
          have hnat := ld.cone.naturality WalkingCospanMor.inl
          simp only [Diagonal, Category.id_comp] at hnat
          simp only [mkCone, ← hk₁, ← Category.assoc]
          exact congrArg (· ○ k) hnat
        next => simpa using hk₁
        next => simpa using hk₂) }

/-- Pullback 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Pullback f g) : h₁.obj ≅ h₂.obj :=
  Limit.unique h₁.toLimit h₂.toLimit

instance (priority := 100) ShapeComplete.Pullback
    [h : ShapeComplete WalkingCospanCat C] : Pullback f g where
  obj := (h.hasLimit (cospanFunctor f g)).obj
  rep := (h.hasLimit (cospanFunctor f g)).rep

end Pullback

/-- `f` 和 `g` 的 pullback object -/
def Hom.Pullback [h : Pullback f g] := h.obj

/-- `PullbackData` ⟹ `Pullback` -/
@[reducible]
noncomputable def PullbackData.toPullback (pd : PullbackData f g) : Pullback f g where
  obj := pd.obj
  rep := (LimitData.toLimit {
    obj  := pd.obj
    cone := show Δ[pd.obj] ⇒ cospanFunctor f g from {
      app j := match j with | .left => pd.π₁ | .right => pd.π₂ | .bot => f ○ pd.π₁
      naturality m := by
        match m with
        | .refl x => cases x <;> simp
        | .inl    => simp
        | .inr    => simpa using pd.cond }
    lift φ := pd.lift (φ·WalkingCospan.left) (φ·WalkingCospan.right) (by
      have l := φ.naturality WalkingCospanMor.inl
      have r := φ.naturality WalkingCospanMor.inr
      simpa using l.symm.trans r)
    lift_π φ j := by
      cases j
      next => -- bot
        rw [Category.assoc, pd.lift_π₁]
        have := φ.naturality WalkingCospanMor.inl
        simpa using this.symm
      next => exact pd.lift_π₁ _ _ _
      next => exact pd.lift_π₂ _ _ _
    lift_unique φ k hk :=
      pd.lift_unique _ _ _ k
        (by simpa using hk WalkingCospan.left)
        (by simpa using hk WalkingCospan.right)
  }).rep

-- ─── Pushout ─────────────────────────────────────────────────────────────────

namespace Pushout

variable {f : X ⟶[C] A} {g : X ⟶[C] B}

private def mkCocone (ι₁ : A ⟶ Z) (ι₂ : B ⟶ Z) (hc : ι₁ ○ f = ι₂ ○ g) :
    spanFunctor f g ⇒ Δ[Z] where
  app j := match j with | .top => ι₁ ○ f | .left => ι₁ | .right => ι₂
  naturality m := by
    match m with
    | .refl x => cases x <;> simp
    | .fst    => simp
    | .snd    => simpa using hc.symm

/-- `Pushout` ⟹ `PushoutData` -/
noncomputable def data [h : Pushout f g] : PushoutData f g :=
  let cd := CoLimit.data
  { obj  := h.obj
    ι₁   := cd.cocone·WalkingSpan.left
    ι₂   := cd.cocone·WalkingSpan.right
    cond := by
      have l := cd.cocone.naturality WalkingSpanMor.fst
      have r := cd.cocone.naturality WalkingSpanMor.snd
      simp at l r; exact l.trans r.symm
    desc h₁ h₂ hc := cd.desc (mkCocone h₁ h₂ hc)
    desc_ι₁ h₁ h₂ hc := by simpa using cd.desc_ι (mkCocone h₁ h₂ hc) WalkingSpan.left
    desc_ι₂ h₁ h₂ hc := by simpa using cd.desc_ι (mkCocone h₁ h₂ hc) WalkingSpan.right
    desc_unique h₁ h₂ hc k hk₁ hk₂ :=
      cd.desc_unique (mkCocone h₁ h₂ hc) k (by
        intro j; cases j
        next => -- top
          have hnat := cd.cocone.naturality WalkingSpanMor.fst
          simp only [Diagonal, Category.comp_id, mkCocone] at hnat ⊢
          rw [← hnat, ← Category.assoc]; congr 1
        next => simpa using hk₁
        next => simpa using hk₂) }

/-- Pushout 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Pushout f g) : h₁.obj ≅ h₂.obj :=
  CoLimit.unique h₁.toCoLimit h₂.toCoLimit

instance (priority := 100) ShapeCoComplete.Pushout
    [h : ShapeCoComplete WalkingSpanCat C] : Pushout f g where
  obj := (h.hasCoLimit (spanFunctor f g)).obj
  rep := (h.hasCoLimit (spanFunctor f g)).rep

end Pushout

/-- `f` 和 `g` 的 pushout object -/
def Hom.Pushout {f : X ⟶[C] A} {g : X ⟶[C] B} [h : Pushout f g] := h.obj

/-- `PushoutData` ⟹ `Pushout` -/
@[reducible]
noncomputable def PushoutData.toPushout {f : X ⟶[C] A} {g : X ⟶[C] B}
    (pod : PushoutData f g) : Pushout f g where
  obj := pod.obj
  rep := (CoLimitData.toCoLimit {
    obj    := pod.obj
    cocone := show spanFunctor f g ⇒ Δ[pod.obj] from {
      app j := match j with | .top => pod.ι₁ ○ f | .left => pod.ι₁ | .right => pod.ι₂
      naturality m := by
        match m with
        | .refl x => cases x <;> simp
        | .fst    => simp
        | .snd    => simpa using pod.cond.symm }
    desc φ := pod.desc (φ·WalkingSpan.left) (φ·WalkingSpan.right) (by
      have l := φ.naturality WalkingSpanMor.fst
      have r := φ.naturality WalkingSpanMor.snd
      simp at l r; exact l.trans r.symm)
    desc_ι φ j := by
      cases j
      next => -- top
        rw [← Category.assoc, pod.desc_ι₁]
        have := φ.naturality WalkingSpanMor.fst
        simpa using this
      next => exact pod.desc_ι₁ _ _ _
      next => exact pod.desc_ι₂ _ _ _
    desc_unique φ k hk :=
      pod.desc_unique _ _ _ k
        (by simpa using hk WalkingSpan.left)
        (by simpa using hk WalkingSpan.right)
  }).rep

end CategoryTheory
