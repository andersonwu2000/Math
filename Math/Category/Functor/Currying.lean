import MATH.Category.Functor.BiFunctor

namespace CategoryTheory

/-!
# Functor/Currying.lean

Currying / uncurrying functor 及其互為逆的 natural isomorphism。

## 定義
- `curry` — `⟦C × D, E⟧ ⥤ ⟦C, ⟦D, E⟧⟧`
- `uncurry` — `⟦C, ⟦D, E⟧⟧ ⥤ ⟦C × D, E⟧`

## 定理
### `Currying`
- `.uncurry_curry_iso` — `uncurry (curry F) ≅ F`
- `.curry_uncurry_iso` — `curry (uncurry G) ≅ G`
-/

/-- Currying：`curry[F][X] = F[X, –]` -/
abbrev curry : ⟦C × D, E⟧ ⥤ ⟦C, ⟦D, E⟧⟧ where
  obj F := {
    obj X := F[X, –]
    map f := F[f, –]
  }
  map α := {app X := α·(X, –)}

/-- Uncurrying：`uncurry[G][X, Y] = G[X][Y]` -/
abbrev uncurry : ⟦C, ⟦D, E⟧⟧ ⥤ ⟦C × D, E⟧ where
  obj F := {
    obj p := F[p.1][p.2]
    map {p q} m := F[q.1][m.2] ○ F[m.1]·p.2
  }
  map {F G} α := {app p := (α·p.1)·p.2}

namespace Currying

/-! ### 計算 lemma -/

@[simp]
lemma curry_obj_obj (F : C × D ⥤ E) (X : C.obj) (Y : D.obj) :
    curry[F][X][Y] = F[X, Y] := rfl

@[simp]
lemma curry_obj_map (F : C × D ⥤ E) (X : C.obj) {Y₁ Y₂ : D.obj} (f : Y₁ ⟶ Y₂) :
    curry[F][X][f] = F[𝟙X, f] := rfl

@[simp]
lemma curry_map_app {F G : C × D ⥤ E} (α : F ⇒ G) (X : C.obj) (Y : D.obj) :
    (curry[α]·X)·Y = α·(X, Y) := rfl

@[simp]
lemma uncurry_obj_obj (G : C ⥤ ⟦D, E⟧) (X : C.obj) (Y : D.obj) :
    uncurry[G][X, Y] = G[X][Y] := rfl

@[simp]
lemma uncurry_obj_map (G : C ⥤ ⟦D, E⟧) {p q : (C × D).obj} (m : p ⟶ q) :
    uncurry[G][m] = G[q.1][m.2] ○ G[m.1]·p.2 := rfl

@[simp]
lemma uncurry_map_app {F G : C ⥤ ⟦D, E⟧} (α : F ⇒ G) (X : C.obj) (Y : D.obj) :
    uncurry[α]·(X, Y) = (α·X)·Y := rfl

/-! ### 來回 isomorphism -/

/-- `uncurry (curry F) ≅ F` -/
def uncurry_curry_iso (F : C × D ⥤ E) : uncurry[curry[F]] ≅[⟦C × D, E⟧] F where
  hom := { app p := 𝟙 }
  inv := { app p := 𝟙 }

/-- `curry (uncurry G) ≅ G` -/
def curry_uncurry_iso (G : C ⥤ ⟦D, E⟧) : curry[uncurry[G]] ≅[⟦C, ⟦D, E⟧⟧] G where
  hom := {
    app X := { app Y := 𝟙 }
    naturality f := by ext; grind
  }
  inv := {
    app X := { app Y := 𝟙 }
    naturality f := by ext; grind
  }

end Currying

end CategoryTheory
