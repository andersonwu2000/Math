import MATH.Category.Limits.InitialTerminal
import MATH.Category.Structure.Types

/-!
# Limits/Instances/Types.lean

`Types` 範疇（Set）的 limit / colimit 實例。

## 定理
### `Types`
- `HasInitial Types` — initial object = `PEmpty`
- `HasTerminal Types` — terminal object = `PUnit`
-/

namespace CategoryTheory

/-- `Types` 的 initial object 為 `PEmpty`：唯一態射 `PEmpty → X` 是 `PEmpty.elim` -/
noncomputable instance : HasInitial Types :=
  HasInitial.ofData PEmpty
    (fun _ => ⟨PEmpty.elim, trivial, fun f _ => by funext x; exact x.elim⟩)

/-- `Types` 的 terminal object 為 `PUnit`：唯一態射 `X → PUnit` 是常數函數 -/
noncomputable instance : HasTerminal Types :=
  HasTerminal.ofData PUnit
    (fun _ => ⟨fun _ => PUnit.unit, trivial,
               fun f _ => by funext _; exact Subsingleton.elim _ _⟩)

end CategoryTheory
