import MATH.Category.Limits.InitialTerminal
import MATH.Category.Structure.FunctorCat

/-!
# Limits/Instances/FunctorCat.lean

`FunctorCat`（函子範疇）的 limit / colimit 實例。

## 定理
### `FunctorCat`
- `HasInitial ⟦C, D⟧` — initial object = `Δ[init]`（D 有 initial 時）
- `HasTerminal ⟦C, D⟧` — terminal object = `Δ[term]`（D 有 terminal 時）
-/

namespace CategoryTheory

variable {C D : Category}

/-- Functor category `⟦C, D⟧` 的 initial object `Δ[init]`（D 有 initial 時） -/
noncomputable instance [h : HasInitial D] : HasInitial ⟦C, D⟧ :=
  HasInitial.ofData Δ[h.colim]
    (fun F => ⟨{ app := fun X => HasInitial.map h F[X]
                 naturality := fun {X Y} f => by
                   simpa using (HasInitial.map_unique h (F[f] ○ HasInitial.map h F[X])).symm },
               trivial,
               fun α _ => by ext X; exact HasInitial.map_unique h (α·X)⟩)

/-- Functor category `⟦C, D⟧` 的 terminal object `Δ[term]`（D 有 terminal 時） -/
noncomputable instance [h : HasTerminal D] : HasTerminal ⟦C, D⟧ :=
  HasTerminal.ofData Δ[h.lim]
    (fun F => ⟨{ app := fun X => HasTerminal.map h F[X]
                 naturality := fun {X Y} f => by
                   simpa using HasTerminal.map_unique h (HasTerminal.map h F[Y] ○ F[f]) },
               trivial,
               fun α _ => by ext X; exact HasTerminal.map_unique h (α·X)⟩)

end CategoryTheory
