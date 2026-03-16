import MATH.Category.Adjunction.Basic
import MATH.Category.Functor.Const

/-!
# Limits/Basic.lean

Complete category。

## 定義
- `Complete C` — `C` 具有所有 limit（`lim : ⟦J, C⟧ ⥤ C`、`Δ ⊣ lim`）
-/

-- set_option trace.Meta.synthInstance true
-- set_option profiler true
-- set_option trace.Meta.Tactic.simp.numSteps true
-- set_option trace.Meta.Tactic.simp.rewrite true

namespace CategoryTheory

/-- `Complete C`：`C` 具有所有 limit，由 `lim : ⟦J, C⟧ ⥤ C` 和 `Δ ⊣ lim` 見證 -/
structure Complete (C : Category) where
  lim : ⟦J, C⟧ ⥤ C
  adjunction : (Δ : C ⥤ ⟦J, C⟧) ⊣ lim

end CategoryTheory
