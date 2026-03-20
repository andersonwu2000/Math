import MATH.Category.Limits.Shapes.InitialTerminal

/-!
# Limits/Shapes/Zero.lean

Zero object：既是 initial 又是 terminal 的 object。

## 定義
- `HasZero C` — C 有 zero object（既是 initial 又是 terminal）

## 定理
### `HasZero`
- `.toInitialData` — `HasZero` ⟹ `InitialData`
- `.toTerminalData` — `HasZero` ⟹ `TerminalData`
- `.toInitial` — `HasZero` ⟹ `Initial`
- `.toTerminal` — `HasZero` ⟹ `Terminal`
- `.zeroHom` — zero morphism `X ⟶ Y`（透過 zero object）
-/

namespace CategoryTheory

/-- Zero object：既是 initial 又是 terminal -/
structure HasZero (C : Category) where
  /-- Zero object -/
  zero : C.obj
  /-- 唯一態射 `zero ⟶ Y`（initial） -/
  from_zero (Y : C.obj) : zero ⟶ Y
  from_zero_unique (f : zero ⟶ Y) : f = from_zero Y
  /-- 唯一態射 `X ⟶ zero`（terminal） -/
  to_zero (X : C.obj) : X ⟶ zero
  to_zero_unique (f : X ⟶ zero) : f = to_zero X

-- ─── HasZero ─────────────────────────────────────────────────────────────────

namespace HasZero

variable {C : Category}

/-- `HasZero` ⟹ `InitialData` -/
def toInitialData (h : HasZero C) : InitialData C where
  obj := h.zero
  map := h.from_zero
  map_unique := h.from_zero_unique

/-- `HasZero` ⟹ `TerminalData` -/
def toTerminalData (h : HasZero C) : TerminalData C where
  obj := h.zero
  map := h.to_zero
  map_unique := h.to_zero_unique

/-- `HasZero` ⟹ `Initial` -/
@[reducible]
noncomputable def toInitial (h : HasZero C) : Initial C :=
  h.toInitialData.toInitial

/-- `HasZero` ⟹ `Terminal` -/
@[reducible]
noncomputable def toTerminal (h : HasZero C) : Terminal C :=
  h.toTerminalData.toTerminal

/-- Zero morphism `X ⟶ Y`：透過 zero object 的合成 -/
def zeroHom (h : HasZero C) (X Y : C.obj) : X ⟶ Y :=
  h.from_zero Y ○ h.to_zero X

end HasZero

end CategoryTheory
