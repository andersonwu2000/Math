import MATH.Category.Structure.ProductCat

/-!
# Functor/BiFunctor.lean

Bifunctor 操作。

## 定義
- `.fix_left` / `.fix_right` — 固定一側 `F[X, –]`、`F[–, Y]`
- `.hom_left` / `.hom_right` — 固定一側的 natural transformation
- `.comp_left` / `.comp_right` / `.comp_both` — 與 functor 合成
- `Functor.swap` — 交換兩側 `F.swap : D × C ⥤ E`

## 定理
### `BiFunctor`
- `.interchange` / `.interchange'` — `F[𝟙, g] ○ F[f, 𝟙] = F[f, g]`

## 記號
| 記號 | 意義 |
|---|---|
| `F[X, Y]` / `F[f, g]` | bifunctor 作用於物件 / 態射 |
| `F[X, –]` / `F[–, Y]` | 固定一側 |
| `F[f, X]` / `F[X, f]` | 固定一側的態射 |
| `F[f, –]` / `F[–, f]` | 固定一側的 natural transformation |
| `F[G–, –]` / `F[–, G–]` / `F[G–, H–]` | 與 functor 合成 |
| `F[G–, Y]` / `F[X, G–]` | 合成後固定 |
| `F[G–, f]` / `F[f, G–]` | 合成後固定一側的 natural transformation |
| `α·(X, –)` / `α·(–, X)` | natural transformation 固定一側 |
| `α(X, –)` / `α(–, X)` | natural isomorphism 固定一側 |
-/

namespace CategoryTheory
variable (F : C × D ⥤ E) (X : C.obj) (Y : D.obj)

/-- `F.swap : D × C ⥤ E` -/
abbrev Functor.swap : D × C ⥤ E :=
  F ○ ProductCat.swap.hom

namespace BiFunctor

notation:max F "[" X ", " Y "]" => Functor.obj F (X, Y)
notation:max F "[" f ", " g "]" => Functor.map F (f, g)
@[simp, grind =]
lemma id :
  𝟙 F[X, Y] = F[𝟙, 𝟙] :=
  (F.map_id (X, Y)).symm

@[simp, grind =]
lemma comp :
  F.map f ○ F.map g = F.map (f.1 ○ g.1, f.2 ○ g.2) :=
  Eq.symm (F.map_comp f g)

/-- `F[X, –] : D ⥤ E` -/
abbrev fix_left : D ⥤ E where
  obj A := F[X, A]
  map f := F[𝟙, f]

/-- `F[–, Y] : C ⥤ E` -/
abbrev fix_right : C ⥤ E where
  obj A := F[A, Y]
  map f := F[f, 𝟙]

notation:max F "[–" ", " X "]" => fix_right F X
notation:max F "[" X ", " "–]" => fix_left F X

abbrev fix_left_hom (f : A ⟶ B) : F[A, Y] ⟶ F[B, Y] :=
  F[–, Y][f]

abbrev fix_right_hom (f : A ⟶ B) : F[X, A] ⟶ F[X, B] :=
  F[X, –][f]

notation:max F "[" f ", " X "]" => fix_left_hom F X f
notation:max F "[" X ", " f "]" => fix_right_hom F X f

abbrev hom_left (f : A ⟶[C] B) : F[A, –] ⇒ F[B, –] where
  app X := F[f, X]

abbrev hom_right (f : A ⟶ B) : F[–, A] ⇒ F[–, B] where
  app X := F[X, f]

notation:max F "[" f ", " "–]" => hom_left F f
notation:max F "[–" ", " f "]" => hom_right F f

abbrev comp_left (G : B ⥤ C) : B × D ⥤ E where
  obj := fun (X, Y) => F[G[X], Y]
  map := fun (f, g) => F[G[f], g]

abbrev comp_right (G : B ⥤ D) : C × B ⥤ E where
  obj := fun (X, Y) => F[X, G[Y]]
  map := fun (f, g) => F[f, G[g]]

abbrev comp_both (G : A ⥤ C) (H : B ⥤ D) :
  A × B ⥤ E where
  obj := fun (X, Y) => F[G[X], H[Y]]
  map := fun (f, g) => F[G[f], H[g]]

notation:max F "[" G "–" ", " "–]" => comp_left F G
notation:max F "[–" ", " G "–]" => comp_right F G
notation:max F "[" G "–" ", " H "–]" => comp_both F G H

abbrev comp_fix (G : B ⥤ C) : B ⥤ E where
  obj := fun X => F[G[X], Y]
  map := fun f => F[G[f], 𝟙]

abbrev fix_comp (G : B ⥤ D) : B ⥤ E where
  obj := fun Y => F[X, G[Y]]
  map := fun f => F[𝟙, G[f]]

notation:max F "[" G "–" ", " Y "]" => comp_fix F Y G
notation:max F "[" Y ", " G "–]" => fix_comp F Y G

abbrev comp_fix_hom
  (G : B ⥤ C) (f : M ⟶ N) : F[G–, M] ⇒ F[G–, N] where
  app W := F[G–, –][(𝟙).Prod f]

abbrev fix_comp_hom
  (G : B ⥤ D) (f : M ⟶ N) : F[M, G–] ⇒ F[N, G–] where
  app W := F[–, G–][f.Prod (𝟙)]

notation:max F "[" G "–" ", " f "]" => comp_fix_hom F G f
notation:max F "[" f  ", " G "–]" => fix_comp_hom F G f

section NatTrans
variable {F G : C × D ⥤ E} (α : F ⇒ G)

abbrev NatTrans_fix_left (X : C.obj) :
  F[X, –] ⇒ G[X, –] where
  app Y := α·(X, Y)

abbrev NatTrans_fix_right (Y : D.obj) :
  F[–, Y] ⇒ G[–, Y] where
  app X := α·(X, Y)

notation:max α "·" "(" "–" ", " X ")" => NatTrans_fix_right α X
notation:max α "·" "(" X ", " "–)" => NatTrans_fix_left α X

/-! ### Interchange Law -/

/-- `F[𝟙, g] ○ F[f, 𝟙] = F[f, g]` -/
@[simp, grind =]
lemma interchange (F : C × D ⥤ E)
    {X₁ X₂ : C.obj} {Y₁ Y₂ : D.obj}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    F[𝟙X₂, g] ○ F[f.Prod (𝟙Y₁)] = F[f.Prod g] := by
  simp [BiFunctor.comp]

/-- `F[f, 𝟙] ○ F[𝟙, g] = F[f, g]` -/
@[simp, grind =]
lemma interchange' (F : C × D ⥤ E)
    {X₁ X₂ : C.obj} {Y₁ Y₂ : D.obj}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    F[f, 𝟙Y₂] ○ F[(𝟙X₁).Prod g] = F[f.Prod g] := by
  simp [BiFunctor.comp]

end NatTrans
section NatIso

variable {F G : C × D ⥤ E} (α : F ≅ G)

abbrev NatIso_fix_left (X : C.obj) : F[X, –] ≅ G[X, –] where
  hom := {app Y := α·(X, Y)}
  inv := {app Y := α⁻¹·(X, Y)}

abbrev NatIso_fix_right (Y : D.obj) : F[–, Y] ≅ G[–, Y] where
  hom := {app X := α·(X, Y)}
  inv := {app X := α⁻¹·(X, Y)}

notation α "(" X ", " "–)" => NatIso_fix_left α X
notation α "(" "–" ", " X ")" => NatIso_fix_right α X

end NatIso

end BiFunctor

end CategoryTheory
