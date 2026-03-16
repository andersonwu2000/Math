import MATH.Category.Structure.FunctorCat
import MATH.Category.Morphism.Iso

/-!
# NatTrans/Iso.lean

Natural isomorphism。

## 定義
- `NatIso` — natural isomorphism `F ≅ G`（`⟦C, D⟧` 中的 iso）
- `NatIso.ofComponents` — 從逐點 isomorphism 建構 nat iso
- `FunctorCat.op` — `⟦Cᵒᵖ, Dᵒᵖ⟧ ≅[Cat] ⟦C, D⟧ᵒᵖ`

## 定理
### `NatIso`
- `.inv_hom_id_app` / `.hom_inv_id_app` — 逐點消去律
-/

namespace CategoryTheory

/-- `⟦Cᵒᵖ, Dᵒᵖ⟧ ≅[Cat] ⟦C, D⟧ᵒᵖ` -/
def FunctorCat.op : ⟦Cᵒᵖ, Dᵒᵖ⟧ ≅[Cat] ⟦C, D⟧ᵒᵖ where
  hom := {obj F := Fᵒᵖ, map α := αᵒᵖ}
  inv := {obj F := Fᵒᵖ, map α := αᵒᵖ}

/-- Natural isomorphism `F ≅ G`：`⟦C, D⟧` 中的 isomorphism -/
abbrev NatIso (F G : C ⥤ D) := F ≅[⟦C, D⟧] G
notation:50 F " ≅ " G => NatIso F G

namespace NatIso

/-- 從逐點 isomorphism 建構 natural isomorphism -/
def ofComponents
  (α : F ⇒[C, D] G) (eq : ∀ X, (α·X).IsIso) : F ≅ G where
  hom := α
  inv := {
    app X := (eq X).inv,
    naturality {X Y} f := calc
      _ = (α·Y)⁻¹ ○ α·Y ○ F[f] ○ (α·X)⁻¹ := by simp
      _ = F[f] ○ (α·X)⁻¹ := by grind}

variable {F G : C ⥤ D} (α : F ≅ G)

abbrev app (X : C.obj) := α.hom·X
notation:max α "·" X:max => app α X

abbrev inv_app (X : C.obj) := α.inv·X
notation:max α "⁻¹" "·" X:max => inv_app α X

/-- `α⁻¹·X ○ α·X = 𝟙` -/
@[simp, grind =]
lemma inv_hom_id_app (X : C.obj) :
  α⁻¹·X ○ α·X = 𝟙 :=
  congrFun (congrArg NatTrans.app α.inv_hom_id) X

/-- `α·X ○ α⁻¹·X = 𝟙` -/
@[simp, grind =]
lemma hom_inv_id_app (X : C.obj) :
  α·X ○ α⁻¹·X = 𝟙 :=
  congrFun (congrArg NatTrans.app α.hom_inv_id) X

/-- 逐點 isomorphism `F[X] ≅ G[X]` -/
instance Iso (X : C.obj) : F[X] ≅ G[X] where
  hom := α·X
  inv := α⁻¹·X

/-- `α·X` 是可逆 morphism -/
instance IsIso (X : C.obj) : (α·X).IsIso where
  inv := α⁻¹·X

end NatIso
end CategoryTheory
