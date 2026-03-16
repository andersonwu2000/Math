import MATH.Category.Hom.Iso
import MATH.Category.Basic.FullyFaithful

/-!
## Structure/Shapes.lean

本檔案定義各種特殊 category 及其 typeclass：

- `Zero`：empty category，沒有 object 也沒有 morphism；初始 category。
- `One`：terminal category，只有一個 object 和一個 morphism（identity）。
- `Interval`：interval category，有兩個 object `false → true`，模擬 `0 → 1`；用於 homotopy theory。
- `Groupoid`：groupoid，每個 morphism 都可逆的 category。
- `Thin`：thin category，任意兩個 object 之間最多一個 morphism；等價於 preorder。
- `Discrete`：discrete category，thin 且只有 identity morphism；等價於集合。
- `Skeletal`：skeletal category，isomorphic objects 必然相等。
- `Concrete`：concrete category，配備一個 faithful functor 到 `Types`。
- `Connected`：connected category，非空，且任意 functor 到 discrete category 的像是 constant functor。
-/

namespace CategoryTheory
variable (C : Category)

/-- Empty category：沒有 object 也沒有 morphism。
是 terminal category 的對偶，也是 initial category。 -/
def Zero : Category where
  obj := Empty
  hom x y := Empty
  id := Empty.elim
  comp x y := x

/-- Terminal category：只有一個 object 和一個 morphism（identity）。
是所有 category 的 terminal object（在 `Cat` 中）。 -/
def One : Category where
  obj := Unit
  hom x y := Unit
  id x := Unit.unit
  comp x y := Unit.unit

/-- Interval category：有兩個 object `true, false`，
一個非 identity morphism `false ⟶ true`（模擬 `0 → 1`）。
用於建立 homotopy theory 的基礎概念。 -/
def Interval : Category where
  obj := Bool
  hom
    | true, false => Empty
    | _, _ => PUnit
  id x := match x with
    |  true => PUnit.unit
    | false => PUnit.unit
  comp {Y Z X} g f := by
    split
    . match Y with
      | true  => exact g
      | false => exact f
    . apply PUnit.unit

/-- Groupoid：每個 morphism 都可逆的 category。
例如：group 可視為單 object groupoid。 -/
class Groupoid where
  iso (f : X ⟶[C] Y) : f.IsIso

/-- Thin category：任意兩個 object 之間最多一個 morphism。
等價於 preorder。 -/
class Thin where
  subsingleton (X Y : C.obj) : Subsingleton (X ⟶ Y)

/-- Discrete category：thin category 且只有 identity morphism。
即 object 構成集合，沒有非平凡 morphism。 -/
class Discrete extends Thin C where
  eq_of_hom (f : X ⟶[C] Y) : X = Y

/-- Skeletal category：isomorphic objects 必然相等。
即在 isomorphism 意義下沒有冗餘 object。 -/
class Skeletal where
  auto {X Y : C.obj} : (X ≅ Y) → (X = Y)

/-- Concrete category：配備一個 faithful functor 到 `Types`。
允許將 object 視為帶結構的集合。 -/
class Concrete where
  forget : C ⥤ Types
  faithful : forget.Faithful

/-- Connected category：非空，且任意 functor 到 discrete category 的像是 constant functor。
等價於 category 的底圖（忽略方向）是連通的。 -/
class Connected where
  nonempty : Nonempty C.obj
  const (F : C ⥤ D) [Discrete D] (X : C.obj) : F ≅[⟦C, D⟧] Δ[F[X]]

end CategoryTheory
