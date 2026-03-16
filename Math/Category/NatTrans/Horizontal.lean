import MATH.Category.Functor.BiFunctor

/-!
# NatTrans/Horizontal.lean

Horizontal composition 與 whiskering。

## 定義
- `HorizontalComp` — horizontal composition `β ◫ α : H ○ F ⇒ K ○ G`
- `Whisker.Functor_NatTrans` — 右 whiskering `H ◫ α`
- `Whisker.NatTrans_Functor` — 左 whiskering `β ◫ F`

## 定理
- `HorizontalComp.interchange` — Godement interchange law
-/

namespace CategoryTheory

/-- Horizontal composition `β ◫ α : H ○ F ⇒ K ○ G`，分量 `(β ◫ α)·X = K[α·X] ○ β·F[X]` -/
abbrev HorizontalComp
  (α : F ⇒[C, D] G) (β : H ⇒[D, E] K) :
  H ○[Cat] F ⇒ K ○[Cat] G where
  app X := K[α·X] ○ β·F[X]

notation:60 β:61 "◫" α:60 => HorizontalComp α β

/-- Horizontal composition functor `⟦D, E⟧ × ⟦C, D⟧ ⥤ ⟦C, E⟧` -/
abbrev Transformation.HorizontalFunctor :
  ⟦D, E⟧ × ⟦C, D⟧ ⥤ ⟦C, E⟧ where
  obj X := X.1 ○[Cat] X.2
  map α := α.1 ◫ α.2

/-- Godement interchange law：`(β₂ ○ β₁) ◫ (α₂ ○ α₁) = (β₂ ◫ α₂) ○ (β₁ ◫ α₁)` -/
lemma HorizontalComp.interchange
  {F₁ F₂ F₃ : C ⥤ D} {G₁ G₂ G₃ : D ⥤ E}
  (α₁ : F₁ ⇒ F₂) (α₂ : F₂ ⇒ F₃) (β₁ : G₁ ⇒ G₂) (β₂ : G₂ ⇒ G₃) :
  (β₂ ○[⟦D, E⟧] β₁) ◫ (α₂ ○[⟦C, D⟧] α₁) = (β₂ ◫ α₂) ○[⟦C, E⟧] (β₁ ◫ α₁) := by grind

namespace Whisker

/-- 右 whiskering：`H ◫ α : H ○ F ⇒ H ○ G` -/
abbrev Functor_NatTrans
  (α : F ⇒[C, D] G) (H : D ⥤ E) := 𝟙[⟦D, E⟧] H ◫ α

notation:60 F:61 "◫" α:60 => Functor_NatTrans α F

/-- 左 whiskering：`β ◫ F : H ○ F ⇒ K ○ F` -/
abbrev NatTrans_Functor
  (F : C ⥤ D) (β : H ⇒[D, E] K) := β ◫ 𝟙[⟦C, D⟧] F

notation:60 β:61 "◫" F:60 => NatTrans_Functor F β

end Whisker

end CategoryTheory
