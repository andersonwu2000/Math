import MATH.Category.Limits.Complete
import MATH.Category.Structure.Shapes

/-!
# Limits/Shapes/InitialTerminal.lean

Initial / terminal object：空圖的 colimit / limit。

## 定義
- `Initial C` — C 有 initial object，即空圖的 colimit
- `Terminal C` — C 有 terminal object，即空圖的 limit
- `InitialData C` — initial object `obj` 及唯一態射 `map`
- `TerminalData C` — terminal object `obj` 及唯一態射 `map`

## 定理
### `Initial`
- `.data` — `Initial` ⟹ `InitialData`
- `.unique` — initial object 在 iso 下唯一
- `ShapeCoComplete.instInitial` — `ShapeCoComplete` ⟹ `Initial`
### `InitialData`
- `.toInitial` — `InitialData` ⟹ `Initial`
### `Terminal`
- `.data` — `Terminal` ⟹ `TerminalData`
- `.unique` — terminal object 在 iso 下唯一
- `ShapeComplete.instTerminal` — `ShapeComplete` ⟹ `Terminal`
### `TerminalData`
- `.toTerminal` — `TerminalData` ⟹ `Terminal`
-/

namespace CategoryTheory

variable (C : Category)

/-- `Initial C`：C 有 initial object，即空圖的 colimit -/
class Initial extends @CoLimit EmptyCat.{0} C (emptyFunctor C)

/-- `Terminal C`：C 有 terminal object，即空圖的 limit -/
class Terminal extends @Limit EmptyCat.{0} C (emptyFunctor C)

/-- Initial object：`obj` 和唯一態射 `map Y : obj ⟶ Y` -/
structure InitialData where
  obj : C.obj
  map Y : obj ⟶ Y
  map_unique (f : obj ⟶ Y) : f = map Y

/-- Terminal object：`obj` 和唯一態射 `map X : X ⟶ obj` -/
structure TerminalData where
  obj : C.obj
  map X : X ⟶ obj
  map_unique (f : X ⟶ obj) : f = map X

/-- `InitialData` ⟹ `Initial` -/
@[reducible]
noncomputable def InitialData.toInitial (id : InitialData C) : Initial C where
  colim := id.obj
  universal := (CoLimitData.toCoLimit {
    obj             := id.obj
    cocone          := emptyNatTrans _ _
    desc _          := id.map _
    desc_ι _ j      := PEmpty.elim j
    desc_unique _ k _ := id.map_unique k
  }).universal

/-- `TerminalData` ⟹ `Terminal` -/
@[reducible]
noncomputable def TerminalData.toTerminal (td : TerminalData C) : Terminal C where
  lim := td.obj
  universal := (LimitData.toLimit {
    obj              := td.obj
    cone             := emptyNatTrans _ _
    lift _           := td.map _
    lift_π _ j       := PEmpty.elim j
    lift_unique _ k _ := td.map_unique k
  }).universal

-- ─── Initial ──────────────────────────────────────────────────────────────────

namespace Initial

/-- `Initial` ⟹ `InitialData` -/
noncomputable def data (h : Initial C) : InitialData C :=
  let cd := CoLimit.data (⟨h.colim, h.universal⟩ : CoLimit _)
  { obj       := h.colim
    map _     := cd.desc (emptyNatTrans _ _)
    map_unique f := cd.desc_unique _ f (fun j => PEmpty.elim j) }

/-- Initial object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Initial C) : h₁.colim ≅ h₂.colim :=
  Universal.unique h₁.universal h₂.universal

instance (priority := 100) ShapeCoComplete.instInitial
    [h : @ShapeCoComplete EmptyCat.{0} C] : Initial C where
  colim := (h.hascolimit (emptyFunctor C)).colim
  universal := (h.hascolimit (emptyFunctor C)).universal

end Initial

-- ─── Terminal ─────────────────────────────────────────────────────────────────

namespace Terminal

/-- `Terminal` ⟹ `TerminalData` -/
noncomputable def data (h : Terminal C) : TerminalData C :=
  let ld := Limit.data (⟨h.lim, h.universal⟩ : Limit _)
  { obj       := h.lim
    map _     := ld.lift (emptyNatTrans _ _)
    map_unique f := ld.lift_unique _ f (fun j => PEmpty.elim j) }

/-- Terminal object 在 isomorphism 下唯一 -/
noncomputable def unique (h₁ h₂ : Terminal C) : h₁.lim ≅ h₂.lim :=
  CoUniversal.unique h₁.universal h₂.universal

instance (priority := 100) ShapeComplete.instTerminal
    [h : @ShapeComplete EmptyCat.{0} C] : Terminal C where
  lim := (h.hasLimit (emptyFunctor C)).lim
  universal := (h.hasLimit (emptyFunctor C)).universal

end Terminal

end CategoryTheory
