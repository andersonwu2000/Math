import MATH.Category.Limits.Shapes.InitialTerminal

/-!
# Limits/Shapes/Zero.lean

Zero object：既是 initial 又是 terminal 的 object。

## 定義
- `ZeroData C` — C 有 zero object（既是 initial 又是 terminal）

## 定理
### `ZeroData`
- `.toInitialData` — `ZeroData` ⟹ `InitialData`
- `.toTerminalData` — `ZeroData` ⟹ `TerminalData`
- `.toInitial` — `ZeroData` ⟹ `Initial`
- `.toTerminal` — `ZeroData` ⟹ `Terminal`
- `.zeroHom` — zero morphism `X ⟶ Y`（透過 zero object）
-/

namespace CategoryTheory

/-- Zero object：既是 initial 又是 terminal -/
structure ZeroData (C : Category) where
  /-- Zero object -/
  zero : C.obj
  /-- 唯一態射 `zero ⟶ Y`（initial） -/
  fromZero (Y : C.obj) : zero ⟶ Y
  fromZeroUnique (f : zero ⟶ Y) : f = fromZero Y
  /-- 唯一態射 `X ⟶ zero`（terminal） -/
  toZero (X : C.obj) : X ⟶ zero
  toZeroUnique (f : X ⟶ zero) : f = toZero X

-- ─── ZeroData ─────────────────────────────────────────────────────────────────

namespace ZeroData

variable {C : Category}

/-- `ZeroData` ⟹ `InitialData` -/
def toInitialData (h : ZeroData C) : InitialData C where
  obj := h.zero
  map := h.fromZero
  map_unique := h.fromZeroUnique

/-- `ZeroData` ⟹ `TerminalData` -/
def toTerminalData (h : ZeroData C) : TerminalData C where
  obj := h.zero
  map := h.toZero
  map_unique := h.toZeroUnique

/-- `ZeroData` ⟹ `Initial` -/
@[reducible]
noncomputable def toInitial (h : ZeroData C) : Initial C :=
  h.toInitialData.toInitial

/-- `ZeroData` ⟹ `Terminal` -/
@[reducible]
noncomputable def toTerminal (h : ZeroData C) : Terminal C :=
  h.toTerminalData.toTerminal

/-- Zero morphism `X ⟶ Y`：透過 zero object 的合成 -/
def zeroHom (h : ZeroData C) (X Y : C.obj) : X ⟶ Y :=
  h.fromZero Y ○ h.toZero X

end ZeroData

end CategoryTheory
