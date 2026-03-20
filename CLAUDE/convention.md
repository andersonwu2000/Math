# 慣例規範

語言、命名、class / instance、證明風格。

---

## 語言

| 位置 | 語言 | 範例 |
|---|---|---|
| 註解、文件說明（`/-! -/`、`/-- -/`） | **繁體中文** | `-- 沿 iso 轉移` |
| 數學專有名詞 | **英文** | functor、morphism、adjunction |
| 定義、定理、namespace 名稱 | **英文** | `Limit`、`map_comp` |

- **禁止**使用簡體中文
- 文件說明中的分隔符號使用 em dash `—`，不使用 hyphen `-` 或 `--`

---

## 命名

### 基本規則

| 類型 | 慣例 | 範例 |
|---|---|---|
| 定義 / structure / class | `UpperCamelCase` | `HomEquiv`、`AdjointEquivalence` |
| lemma（回傳 `Prop`） | `snake_case` | `map_comp`、`mono_iff_injective` |
| def / abbrev（回傳非 `Prop`） | `lowerCamelCase` | `ofCone`、`ofHomEquiv`、`leftAdjoint`、`zeroHom` |
| typeclass | `Is` 前綴 | `IsMono`、`IsIso`、`IsSplitMono` |
| 性質 class | 形容詞 | `Full`、`Faithful`、`FullyFaithful` |

區分標準是**回傳型別**，不是關鍵字：
- 回傳 `Prop` → `snake_case`，使用 `lemma`
- 回傳非 `Prop` → `lowerCamelCase`，使用 `def` 或 `abbrev`

命題使用 `lemma` 而非 `theorem`（除非明確指定）。

### 對偶命名

- 對偶版本一律用 `Co` 前綴（UpperCamelCase）
  - 範例：`CoLimit`、`CoLimitData`、`CoProduct`、`CoUniversal`、`CoYoneda`
  - typeclass 複合：`IsCoLimit`、`ShapeCoComplete`
- 例外 1：`Is` + 對偶 typeclass → `Is` + `Co` + rest（如 `IsCoUniversal`）
- 例外 2：`co` 是術語本身的一部分時保持原寫法（如 `WalkingCospan`——cospan 是數學名詞）
- 例外 3：對偶概念有獨立名稱時不加前綴（如 `Mono` 的對偶是 `Epi`，不是 `CoMono`）

### Universal property 相關 class 的欄位

斷言「存在某物件滿足某性質」的 class 統一使用 `obj` / `rep`：

| 欄位 | 意義 | 範例 |
|---|---|---|
| `obj` | 存在的物件 | `Representable.obj`、`Limit.obj`、`Universal.obj` |
| `rep` | 表示該物件的 iso | `Representable.rep`、`Limit.rep`、`Universal.rep` |

對應的 Data structure 也使用 `obj` 作為 object 欄位名稱。

### Instance 命名

- `Parent.Target` 格式，不加 `inst` 前綴
- 範例：`Complete.ShapeComplete`、`ShapeComplete.Product`
- **不是** `Complete.instShapeComplete`、`ShapeComplete.instProduct`

### 複合命名模式

| 模式 | 慣例 | 範例 |
|---|---|---|
| 互轉 | `A.B` / `B.A` | `HomEquiv.Adjunction` ↔ `Adjunction.HomEquiv` |
| 保持 / 反射 | `Preserve.X` / `Reflect.X` | `Preserve.IsIso`、`Reflect.Iso` |
| 消去律 | `cancel` | `IsMono.cancel`、`IsSplitEpi.cancel` |
| 逐點版本 | `_app` / `_apply` 後綴 | `hom_inv_id_app`、`naturality_apply` |
| iso 相關 | `hom_inv_id` / `inv_hom_id` | 保持一致方向 |
| Typeclass `Is` 前綴 | 在複合名稱中保持大寫 | `splitMono_epi_IsIso`、`Preserve.IsIso` |

---

## Class / Instance

### 參數風格

| 情境 | 風格 | 範例 |
|---|---|---|
| 查詢唯一 instance | `[h : Foo]` 或 `[Foo]` | `Limit.data [Limit F]` |
| 操作多個 instance 或變換 | `(u : Foo)` | `Limit.unique (h₁ h₂ : Limit F)` |
| 返回 class type 的 def | **必須** `@[reducible]` | `LimitData.toLimit`、`Universal.ofIso` |
| 自動推導 instance | `instance` | `Limit.universal [Limit F] : CoUniversal Δ F` |

### 層級委託（instance chain）

更具體的 class 應提供 instance 到更一般的 class：

```
Limit F  ──instance──▸  CoUniversal Δ F  ──instance──▸  CoRepresentable Hom[Fᵒᵖ–, F]
CoLimit F  ──instance──▸  Universal Δ F  ──instance──▸  Representable Hom[X, G–]
```

### Hom 記號的 elaboration

`Hom[X, G–]` 等複合記號在 instance / def 中可能需要明確的 implicit category 參數：

```lean
-- ✗ 可能無法 elaborate
def foo (h : Universal G X) : Representable Hom[X, G–] := ...

-- ✓ 加上明確的 category 參數
instance foo {G : D ⥤ C} {X : C.obj}
    [h : Universal G X] : Representable Hom[X, G–] := ...
```

### 對偶對稱

對偶 pair **必須**具備平行的結構（相同的欄位名稱、相同的 API、相同的證明風格）：
- `Representable` / `CoRepresentable`
- `Universal` / `CoUniversal`
- `Limit` / `CoLimit`
- 各 Shapes（`Product` / `CoProduct`、`Equalizer` / `CoEqualizer` 等）

---

## 證明風格

- **禁止**將多行壓縮成一行當成簡化證明的手段
