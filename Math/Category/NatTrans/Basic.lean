import MATH.Category.Functor.Basic

/-!
# NatTrans/Basic.lean

Natural transformation。

## 定義
- `NatTrans` — natural transformation `α : F ⇒ G`（app、naturality）
- `NatTrans.op` — opposite `αᵒᵖ : Gᵒᵖ ⇒ Fᵒᵖ`

## 定理
### `NatTrans`
- `.functor_naturality` — `F[α·Y] ○ F[G[f]] = F[H[f]] ○ F[α·X]`
- `.naturality_assoc` — naturality 的 associativity 版本
-/

namespace CategoryTheory

/-- `NatTrans α : F ⇒ G`：分量 `app X` 與自然性 `α·Y ○ F[f] = G[f] ○ α·X`。 -/
@[ext]
structure NatTrans (F G : C ⥤ D) where
  app X : F[X] ⟶ G[X]
  naturality (f : X ⟶ Y) : app Y ○ F[f] = G[f] ○ app X := by aesop_cat

namespace NatTrans

notation:30 F " ⇒[" C ", " D "] " G => @NatTrans C D F G
notation:30 F " ⇒ " G => NatTrans F G
notation:max α "·" X:max => app α X
attribute [simp, grind =, grind _=_] naturality

variable {C D : Category} {F G : C ⥤ D}

lemma congr_app {α β : F ⇒ G} (h : α = β) (X : C.obj) : α·X = β·X :=
  h ▸ rfl

@[simp, grind _=_]
lemma functor_naturality
  (F : D ⥤ E) (α : G ⇒[C, D] H) (f : X ⟶ Y) :
  F[α·Y] ○ F[G[f]] = F[H[f]] ○ F[α·X] := by grind

@[simp, grind _=_]
lemma functor_naturality'
  (F : D ⥤ E) (α : G ⇒[C, D] H) (f : X ⟶ Y) (h : Z ⟶ F[G[X]]) :
  F[α·Y] ○ F[G[f]] ○ h = F[H[f]] ○ F[α·X] ○ h := by grind

@[simp, grind _=_]
lemma naturality_assoc
  (α : F ⇒[C, D] G) (f : X ⟶ Y) (h : Z ⟶ F[X]) :
  α·Y ○ F[f] ○ h = G[f] ○ α·X ○ h := by grind

/-- Opposite natural transformation `αᵒᵖ : Gᵒᵖ ⇒ Fᵒᵖ` -/
abbrev op (α : F ⇒ G) : Gᵒᵖ ⇒ Fᵒᵖ where
  app X := α·X

notation α "ᵒᵖ" => op α

end NatTrans
end CategoryTheory
