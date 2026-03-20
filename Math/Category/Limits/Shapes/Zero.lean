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
  from_zero (Y : C.obj) : zero ⟶ Y
  from_zero_unique (f : zero ⟶ Y) : f = from_zero Y
  /-- 唯一態射 `X ⟶ zero`（terminal） -/
  to_zero (X : C.obj) : X ⟶ zero
  to_zero_unique (f : X ⟶ zero) : f = to_zero X

-- ─── ZeroData ─────────────────────────────────────────────────────────────────

namespace ZeroData

variable {C : Category}

/-- `ZeroData` ⟹ `InitialData` -/
def toInitialData (h : ZeroData C) : InitialData C where
  obj := h.zero
  map := h.from_zero
  map_unique := h.from_zero_unique

/-- `ZeroData` ⟹ `TerminalData` -/
def toTerminalData (h : ZeroData C) : TerminalData C where
  obj := h.zero
  map := h.to_zero
  map_unique := h.to_zero_unique

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
  h.from_zero Y ○ h.to_zero X

end ZeroData

end CategoryTheory
