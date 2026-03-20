import MATH.Category.Structure.FunctorCat

/-!
# Functor/Const.lean

Constant diagram functor。

## 定義
- `Diagonal` (`Δ`) — `C ⥤ ⟦J, C⟧`，將所有 object 映射到同一 object
-/

namespace CategoryTheory

variable {C : Category} {J : Category}

/-- `Δ[X]` 將 `J` 所有 object 映射到 `X`，`Δ[f]` 每個分量均為 `f` -/
@[reducible, simp]
def Diagonal : C ⥤ ⟦J, C⟧ where
  obj X := {
    obj j := X
    map f := 𝟙 X }
  map f := {app := fun _ => f}

notation "Δ" => Diagonal

end CategoryTheory
