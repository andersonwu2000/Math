import MATH.Category.Limits.InitialTerminal
import MATH.Category.Structure.ProductCat

/-!
# Limits/Instances/ProductCat.lean

`ProductCat`（積範疇）的 limit / colimit 實例。

## 定理
### `ProductCat`
- `HasInitial (C × D)` — initial object = `(init₁, init₂)`
- `HasTerminal (C × D)` — terminal object = `(term₁, term₂)`
-/

namespace CategoryTheory

variable {C D : Category}

/-- Product category 的 initial object：`(init_C, init_D)` -/
noncomputable instance [hC : HasInitial C] [hD : HasInitial D] : HasInitial (C × D) :=
  HasInitial.ofData (hC.colim, hD.colim)
    (fun p => ⟨(HasInitial.map hC p.1, HasInitial.map hD p.2), trivial,
      fun f _ => Prod.ext (HasInitial.map_unique hC f.1) (HasInitial.map_unique hD f.2)⟩)

/-- Product category 的 terminal object：`(term_C, term_D)` -/
noncomputable instance [hC : HasTerminal C] [hD : HasTerminal D] : HasTerminal (C × D) :=
  HasTerminal.ofData (hC.lim, hD.lim)
    (fun p => ⟨(HasTerminal.map hC p.1, HasTerminal.map hD p.2), trivial,
      fun f _ => Prod.ext (HasTerminal.map_unique hC f.1) (HasTerminal.map_unique hD f.2)⟩)

end CategoryTheory
