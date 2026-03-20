import MATH.Category.Morphism.Iso
import MATH.Category.NatTrans.Basic

/-!
# Structure/Shapes.lean

Limit / colimit 計算中常用的 index category（shape category）及其標準 functor。

## 定義
- `DiscreteCat α` — 只有 identity morphism，用於 product / coproduct
- `EmptyCat` — `DiscreteCat PEmpty`，initial object 的典型 index
- `UnitCat` — `DiscreteCat PUnit`，單元範疇（一個 object）
- `BoolCat` — `DiscreteCat (ULift Bool)`，用於 binary product / coproduct
- `WalkingArrowCat` — `src → tgt`，用於 arrow category
- `WalkingParallelPairCat` — `zero ⇉ one`，用於 equalizer / coequalizer
- `WalkingSpanCat` — `left ← top → right`，用於 pushout
- `WalkingCospanCat` — `left → bot ← right`，用於 pullback

- `emptyFunctor C` — `EmptyCat ⥤ C`，唯一存在
- `emptyNatTrans F G` — `EmptyCat` 形狀的唯一 natural transformation
- `unitFunctor X` — `UnitCat ⥤ C`，選定 object `X`
- `discreteFunctor f` — `DiscreteCat α ⥤ C`，`a ↦ f a`
- `arrowFunctor f` — `WalkingArrowCat ⥤ C`，編碼態射 `f : A ⟶ B`
- `parallelPairFunctor f g` — `WalkingParallelPairCat ⥤ C`，編碼 parallel pair
- `cospanFunctor f g` — `WalkingCospanCat ⥤ C`，編碼 cospan `A –f→ X ←g– B`
- `spanFunctor f g` — `WalkingSpanCat ⥤ C`，編碼 span `A ←f– X –g→ B`
-/

namespace CategoryTheory

-- ─── Discrete Category ────────────────────────────────────────────────────────

/-- Discrete category：只有 identity morphism，用於 product / coproduct 的 index -/
@[reducible]
def DiscreteCat (α : Type u) : Category where
  obj := α
  hom X Y := PLift (X = Y)
  id X := ⟨rfl⟩
  comp g f := ⟨f.down.trans g.down⟩
  id_comp _ := rfl
  comp_id f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- 空範疇：`DiscreteCat PEmpty`，無 object，initial object 的典型 index -/
abbrev EmptyCat := DiscreteCat PEmpty

/-- `EmptyCat ⥤ C` 的唯一 functor -/
def emptyFunctor (C : Category) : EmptyCat ⥤ C where
  obj := PEmpty.elim
  map {x} _ := x.elim
  map_id x := x.elim
  map_comp {x} _ _ := x.elim

/-- `EmptyCat` 形狀的唯一 natural transformation（vacuous） -/
def emptyNatTrans (F G : EmptyCat ⥤ C) : F ⇒ G where
  app x := x.elim
  naturality {x} _ := x.elim

/-- 單元範疇：`DiscreteCat PUnit`，一個 object -/
abbrev UnitCat := DiscreteCat PUnit

/-- Functor `UnitCat ⥤ C`，選定 object `X` -/
def unitFunctor (X : C.obj) : UnitCat ⥤ C where
  obj _ := X
  map _ := 𝟙 X
  map_id _ := rfl
  map_comp _ _ := by simp

/-- Two-object discrete category：`DiscreteCat (ULift Bool)`，用於 binary product / coproduct 的 index -/
abbrev BoolCat := DiscreteCat (ULift Bool)

/-- Functor `DiscreteCat α ⥤ C`，將 `a` 映到 `f a` -/
@[reducible]
def discreteFunctor (f : α → C.obj) : DiscreteCat α ⥤ C where
  obj a := f a
  map g := g.down ▸ 𝟙 _
  map_id _ := rfl
  map_comp g f := by
    rcases g with ⟨g⟩; rcases f with ⟨f⟩
    subst f g; simp

-- ─── Walking Arrow ────────────────────────────────────────────────────────────

/-- Walking arrow 的 object -/
inductive WalkingArrow | src | tgt

/-- Walking arrow 的 morphism -/
inductive WalkingArrowMor : WalkingArrow → WalkingArrow → Type
  | refl (X : WalkingArrow) : WalkingArrowMor X X
  | arr : WalkingArrowMor .src .tgt

/-- Walking arrow category：`src → tgt`，用於 arrow category 的 index -/
def WalkingArrowCat : Category where
  obj := WalkingArrow
  hom X Y := WalkingArrowMor X Y
  id X := WalkingArrowMor.refl X
  comp g f := by
    cases g with
    | refl _ => exact f
    | arr => cases f with | refl _ => exact .arr
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

/-- Functor `WalkingArrowCat ⥤ C`，編碼態射 `f : A ⟶ B` -/
@[reducible]
def arrowFunctor (f : A ⟶[C] B) : WalkingArrowCat ⥤ C where
  obj X := match X with | .src => A | .tgt => B
  map m := match m with
    | .refl .src => 𝟙 A
    | .refl .tgt => 𝟙 B
    | .arr => f
  map_id X := by cases X <;> rfl
  map_comp h k := by
    cases h with
    | refl _ => aesop_cat
    | _ => cases k with | refl _ => aesop_cat

-- ─── Walking Parallel Pair ────────────────────────────────────────────────────

/-- Walking parallel pair 的 object -/
inductive WalkingParallelPair | zero | one

/-- Walking parallel pair 的 morphism -/
inductive WalkingParallelPairMor : WalkingParallelPair → WalkingParallelPair → Type
  | refl  (X : WalkingParallelPair) : WalkingParallelPairMor X X
  | left  : WalkingParallelPairMor .zero .one
  | right : WalkingParallelPairMor .zero .one

/-- Walking parallel pair category：`zero ⇉ one`，用於 equalizer / coequalizer 的 index -/
@[reducible]
def WalkingParallelPairCat : Category where
  obj := WalkingParallelPair
  hom X Y := WalkingParallelPairMor X Y
  id X := WalkingParallelPairMor.refl X
  comp g f := by
    cases g with
    | refl _ => exact f
    | left  => cases f with | refl _ => exact .left
    | right => cases f with | refl _ => exact .right
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

/-- Functor `WalkingParallelPairCat ⥤ C`，編碼 `f g : A ⟶ B` 為 parallel pair -/
@[reducible]
def parallelPairFunctor (f g : A ⟶[C] B) :
    WalkingParallelPairCat ⥤ C where
  obj X := match X with | .zero => A | .one => B
  map m := match m with
    | .refl .zero => 𝟙 A
    | .refl .one  => 𝟙 B
    | .left  => f
    | .right => g
  map_id obj := by cases obj <;> rfl
  map_comp h k := by
    cases h with
    | refl _ => aesop_cat
    | _  => cases k; aesop_cat

-- ─── Walking Span ─────────────────────────────────────────────────────────────

/-- Walking span 的 object -/
inductive WalkingSpan | top | left | right

/-- Walking span 的 morphism -/
inductive WalkingSpanMor : WalkingSpan → WalkingSpan → Type
  | refl (X : WalkingSpan) : WalkingSpanMor X X
  | fst : WalkingSpanMor .top .left
  | snd : WalkingSpanMor .top .right

/-- Walking span category：`left ← top → right`，用於 pushout 的 index -/
@[reducible]
def WalkingSpanCat : Category where
  obj := WalkingSpan
  hom X Y := WalkingSpanMor X Y
  id X := WalkingSpanMor.refl X
  comp g f := by
    cases g with
    | refl _ => exact f
    | fst => cases f with | refl _ => exact .fst
    | snd => cases f with | refl _ => exact .snd
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

-- ─── Walking Cospan ───────────────────────────────────────────────────────────

/-- Walking cospan 的 object -/
inductive WalkingCospan | bot | left | right

/-- Walking cospan 的 morphism -/
inductive WalkingCospanMor : WalkingCospan → WalkingCospan → Type
  | refl (X : WalkingCospan) : WalkingCospanMor X X
  | inl : WalkingCospanMor .left .bot
  | inr : WalkingCospanMor .right .bot

/-- Walking cospan category：`left → bot ← right`，用於 pullback 的 index -/
@[reducible]
def WalkingCospanCat : Category where
  obj := WalkingCospan
  hom X Y := WalkingCospanMor X Y
  id X := WalkingCospanMor.refl X
  comp g f := by
    cases g with
    | refl _ => exact f
    | inl => cases f with | refl _ => exact .inl
    | inr => cases f with | refl _ => exact .inr
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc f g h := by cases f <;> cases g <;> cases h <;> rfl

-- ─── Shape Functors ─────────────────────────────────────────────────────────

/-- Functor `WalkingCospanCat ⥤ C`，編碼 cospan `A –f→ X ←g– B` -/
@[reducible]
def cospanFunctor (f : A ⟶[C] X) (g : B ⟶[C] X) : WalkingCospanCat ⥤ C where
  obj j := match j with | .left => A | .right => B | .bot => X
  map m := match m with
    | .refl .left  => 𝟙 A
    | .refl .right => 𝟙 B
    | .refl .bot   => 𝟙 X
    | .inl => f
    | .inr => g
  map_id j := by cases j <;> rfl
  map_comp h k := by
    cases h with
    | refl _ => aesop_cat
    | _ => cases k with | refl _ => aesop_cat

/-- Functor `WalkingSpanCat ⥤ C`，編碼 span `A ←f– X –g→ B` -/
@[reducible]
def spanFunctor (f : X ⟶[C] A) (g : X ⟶[C] B) : WalkingSpanCat ⥤ C where
  obj j := match j with | .top => X | .left => A | .right => B
  map m := match m with
    | .refl .top   => 𝟙 X
    | .refl .left  => 𝟙 A
    | .refl .right => 𝟙 B
    | .fst => f
    | .snd => g
  map_id j := by cases j <;> rfl
  map_comp h k := by
    cases h with
    | refl _ => aesop_cat
    | _ => cases k with | refl _ => aesop_cat

end CategoryTheory
