import MATH.Category.Limits.Shapes.InitialTerminal
import MATH.Category.Limits.Shapes.BinaryProduct
import MATH.Category.Structure.Shapes

/-!
# Limits/Instances/Cat.lean

`Cat`（範疇的範疇）的 limit shape 實例。

## 定理
### `Cat`
- `Initial Cat` — initial object = `EmptyCat`
- `Terminal Cat` — terminal object = `UnitCat`
- `BinaryProduct C D` — binary product = `ProductCat C D`
-/

namespace CategoryTheory

-- ─── Initial / Terminal ───────────────────────────────────────────────────────

/-- `Cat` 的 initial object 為 `EmptyCat` -/
noncomputable instance Cat_Initial : Initial Cat :=
  InitialData.toInitial (C := Cat) {
    obj := EmptyCat
    map C := {
      obj := PEmpty.elim
      map := fun {x} _ => x.elim
      map_id x := x.elim
      map_comp := fun {x} _ _ => x.elim }
    map_unique F := by
      obtain ⟨fo, fm, mi, mc⟩ := F
      have ho : fo = PEmpty.elim := funext fun x => x.elim
      subst ho; congr 1; funext x; exact x.elim }

/-- `Cat` 的 terminal object 為 `UnitCat` -/
noncomputable instance Cat_Terminal : Terminal Cat :=
  TerminalData.toTerminal (C := Cat) {
    obj := UnitCat
    map C := {
      obj := fun _ => PUnit.unit
      map := fun _ => ⟨rfl⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
    map_unique F := by
      obtain ⟨fo, fm, mi, mc⟩ := F
      have ho : fo = fun _ => PUnit.unit := funext fun _ => Subsingleton.elim _ _
      subst ho; congr 1 }

-- ─── BinaryProduct ──────────────────────────────────────────────────────────

/-- `Cat` 的 binary product 為 `ProductCat C D` -/
noncomputable instance Cat_BinaryProduct (C D : Cat.obj) : BinaryProduct (C := Cat) C D :=
  BinaryProductData.toBinaryProduct (A := C) (B := D) {
    obj := ProductCat C D
    π₁ := ProductCat.fst
    π₂ := ProductCat.snd
    lift F₁ F₂ := {
      obj := fun X => (F₁[X], F₂[X])
      map := fun f => (F₁[f], F₂[f])
      map_id X := Prod.ext (F₁.map_id X) (F₂.map_id X)
      map_comp f g := Prod.ext (F₁.map_comp f g) (F₂.map_comp f g) }
    lift_π₁ F₁ F₂ := by
      change Cat.comp ProductCat.fst _ = F₁
      obtain ⟨o₁, m₁, mi₁, mc₁⟩ := F₁; rfl
    lift_π₂ F₁ F₂ := by
      change Cat.comp ProductCat.snd _ = F₂
      obtain ⟨o₂, m₂, mi₂, mc₂⟩ := F₂; rfl
    lift_unique F₁ F₂ K hk₁ hk₂ := by
      subst hk₁; subst hk₂
      obtain ⟨ko, km, kmi, kmc⟩ := K
      congr 1 }

end CategoryTheory
