import MATH.Category.Limits.InitialTerminal
import MATH.Category.Structure.Shapes

/-!
# Limits/Instances/Cat.lean

`Cat`（範疇的範疇）的 limit / colimit 實例。

## 定理
### `Cat`
- `HasInitial Cat` — initial object = `EmptyCat`
- `HasTerminal Cat` — terminal object = `UnitCat`
-/

namespace CategoryTheory

/-- `Cat` 的 initial object 為 `EmptyCat` -/
noncomputable instance : HasInitial Cat :=
  HasInitial.ofData EmptyCat
    (fun C => ⟨{ obj := PEmpty.elim
                 map := fun {x} _ => x.elim
                 map_id := fun x => x.elim
                 map_comp := fun {x} _ _ => x.elim },
               trivial,
               fun F _ => by
                 obtain ⟨fo, fm, mi, mc⟩ := F
                 have ho : fo = PEmpty.elim := funext fun x => x.elim
                 subst ho; congr 1; funext X; exact X.elim⟩)

/-- `Cat` 的 terminal object 為 `UnitCat` -/
noncomputable instance : HasTerminal Cat :=
  HasTerminal.ofData UnitCat
    (fun C => ⟨{ obj := fun _ => PUnit.unit
                 map := fun _ => PUnit.unit
                 map_id := fun _ => rfl
                 map_comp := fun _ _ => rfl },
               trivial,
               fun F _ => by
                 obtain ⟨fo, fm, mi, mc⟩ := F
                 have ho : fo = fun _ => PUnit.unit := funext fun _ => Subsingleton.elim _ _
                 subst ho; congr 1⟩)

end CategoryTheory
