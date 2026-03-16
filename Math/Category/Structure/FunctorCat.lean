import MATH.Category.NatTrans.Basic

/-!
# Structure/FunctorCat.lean

Functor category。

## 定義
- `FunctorCat` — functor category `⟦C, D⟧`

## 定理
### `NatTrans`
- `.vcomp_app` — `(β ○ α)·X = β·X ○ α·X`
- `.naturality_app` — naturality 的逐點版本
-/

namespace CategoryTheory

/-- Functor category `⟦C, D⟧`：object 為 functor，morphism 為 natural transformation -/
abbrev FunctorCat (C D : Category) : Category where
  obj := C ⥤ D
  hom F G := NatTrans F G
  id F := {app X := 𝟙}
  comp β α := {app X := β·X ○ α·X}

notation "⟦" C ", " D "⟧" => FunctorCat C D

namespace NatTrans

lemma vcomp_app {F G H : C ⥤ D}
  (β : G ⇒ H) (α : F ⇒ G) (X : C.obj) :
  (β ○[⟦C, D⟧] α)·X = β·X ○ α·X := rfl

/-- Naturality 逐點版：`((α·Y)·A) ○ F[f]·A = (G[f]·A) ○ (α·X)·A` -/
@[simp, grind _=_]
lemma naturality_app {F G : C ⥤ ⟦D, E⟧} (α : F ⇒ G)
  {X Y : C.obj} {A : D.obj} (f : X ⟶[C] Y) :
  ((α·Y)·A) ○ F[f]·A = (G[f]·A) ○ (α·X)·A :=
  congrFun (congrArg NatTrans.app (α.naturality f)) A

end NatTrans
end CategoryTheory
