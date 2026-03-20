# CLAUDE.md

此檔案提供 Claude Code 在本儲存庫中工作時的指引。
所有規範皆為**強制性**，除非明確標註「建議」。

---

## 建置指令

```bash
lake build              # 建置整個專案
lake build MATH         # 建置 MATH 目標（含所有已啟用的 import）
lake build MATH.<模組>  # 建置單一模組（如 MATH.Category.Yoneda）
lake update             # 更新相依套件（修改 lake-manifest.json 後執行）
```

本專案沒有獨立的測試執行器——`.lean` 檔案中的證明在建置時即會被驗證。

### 工作流程

1. **修改前**：`lake build MATH.<模組>` 確認目前狀態可編譯
2. **修改後**：`lake build MATH.<模組>` 確認無錯誤、無警告
3. **完成後**：更新該檔案的模組標頭（`/-! ... -/`），確保與程式碼一致
4. 若證明困難，考慮新增輔助 lemma，而非強行寫冗長的 tactic chain

---

## 架構

- 以 **Lean 4** 從頭建構的範疇論函式庫
- **不**包裝 Mathlib 的範疇論，僅使用 Mathlib 的策略（`aesop`、`simp`、`grind`）與 Lean 的 `Type`
- 工具鏈：`leanprover/lean4:v4.29.0-rc6`

### 模組結構

| 路徑 | 內容 |
|---|---|
| `Category/Basic.lean` | `Category`、opposite、Whisker |
| `Category/Tactic/` | 自訂策略 `aesop_cat` |
| `Category/Functor/` | `Functor`、`Cat`、Hom 函子、常數函子、雙函子、fully faithful、essentially surjective、representable |
| `Category/NatTrans/` | 自然變換、自然同構、水平合成 |
| `Category/Morphism/` | mono/epi、iso、preserve/reflect |
| `Category/Structure/` | 函子範疇、積範疇、`Types`、index category shapes |
| `Category/Adjunction/` | 伴隨、equivalence |
| `Category/Limits/` | 極限、colimit、complete、具體 shape（Product、Equalizer、InitialTerminal） |
| `Category/Yoneda.lean` | 米田引理 |
| `Category/UniversalProperty.lean` | Universal / couniversal property |

> `__Test__.lean` 直接使用 Mathlib 的伴隨 API，而非自訂版本。
> `Math/tmp/` 為實驗性／進行中的工作。

### 記號

| 記號 | 意義 |
|---|---|
| `X ⟶ Y` | Hom 集合 |
| `𝟙 X` | 單位態射 |
| `g ○ f` | 合成（g 接在 f 後） |
| `Cᵒᵖ` | 對偶範疇 |
| `C ⥤ D` | 函子 |
| `F ⇒ G` | 自然變換 |
| `F ≅ G` | 自然同構 |
| `F ⊣ G` | 伴隨 |
| `⟦C, D⟧` | 函子範疇 |
| `α·X` / `α⁻¹·X` | 自然變換 / 自然同構的逆 在 X 的分量 |
| `F[X]` / `F[f]` | 函子作用於物件 / 態射 |
| `φ♯` / `φ♭` | 伴隨的 sharp / flat 轉置 |

---

## 語言規範

| 位置 | 語言 | 範例 |
|---|---|---|
| 註解、文件說明（`/-! -/`、`/-- -/`） | **繁體中文** | `-- 沿 iso 轉移` |
| 數學專有名詞 | **英文** | functor、morphism、adjunction |
| 定義、定理、namespace 名稱 | **英文** | `Limit`、`map_comp` |

- **禁止**使用簡體中文
- 文件說明中的分隔符號使用 em dash `—`，不使用 hyphen `-` 或 `--`

---

## 命名慣例

### 基本規則

| 類型 | 慣例 | 範例 |
|---|---|---|
| 定義 / structure | `UpperCamelCase` | `HomEquiv`、`AdjointEquivalence` |
| lemma（命題） | `snake_case` | `map_comp`、`mono_iff_injective` |
| def（建構子，`of*`/`to*`） | `lowerCamelCase` | `ofCone`、`ofHomEquiv`、`ofIso` |
| typeclass | `Is` 前綴 | `IsMono`、`IsIso`、`IsSplitMono` |
| 性質 class | 形容詞 | `Full`、`Faithful`、`FullyFaithful` |

### 命題使用 `lemma`

- 使用 `lemma` 而非 `theorem`（除非明確指定）

### 對偶命名

- 對偶版本一律用 `Co` 前綴（UpperCamelCase）
  - 範例：`CoLimit`、`CoLimitData`、`CoProduct`、`CoUniversal`、`CoYoneda`
  - typeclass 複合：`IsCoLimit`、`ShapeCoComplete`
- 例外 1：`Is` + 對偶 typeclass → `Is` + `Co` + rest（如 `IsCoUniversal`）
- 例外 2：`co` 是術語本身的一部分時保持原寫法（如 `WalkingCospan`——cospan 是數學名詞）
- 例外 3：對偶概念有獨立名稱時不加前綴（如 `Mono` 的對偶是 `Epi`，不是 `CoMono`）

### 「UniversalProperty 相關 class」的欄位命名

斷言「存在某物件滿足某性質」的 class 統一使用 `obj` / `rep`：

| 欄位 | 意義 | 範例 |
|---|---|---|
| `obj` | 存在的物件 | `Representable.obj`、`Limit.obj`、`Universal.obj` |
| `rep` | 表示該物件的 iso | `Representable.rep`、`Limit.rep`、`Universal.rep` |

- 對應的 Data structure 也使用 `obj` 作為 object 欄位名稱
- 適用範圍：`Representable`、`CoRepresentable`、`Universal`、`CoUniversal`、`Limit`、`CoLimit`、以及未來的 concrete shape class

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

## 文件說明格式

### 模組標頭（`/-! ... -/`）

每個 `.lean` 檔案開頭**必須**有模組標頭：

```
/-!
# 模組路徑

一行摘要。

## 定義
- `Name` — 說明

## 定理
### `Namespace`
- `.method` — 說明
-/
```

規則：
- `#` 為檔案模組路徑（如 `Limits/Basic.lean`）
- `##` 只允許 `## 定義` 和 `## 定理` 兩個區段
- `###` 為 namespace 分組，名稱以 backtick 包裹（如 `` ### `Limit` ``）
- 同一 namespace 下的定理用 `.method` 省略前綴
- 只列出主要的定義和定理，不需列舉所有 simp lemma 或 instance
- 無定理的檔案可省略 `## 定理` 區段
- 標頭中的名稱**必須**與程式碼中的實際宣告一致；修改程式碼後**必須**同步更新標頭

### 行內文件說明（`/-- ... -/`）

| 宣告類型 | 要求 |
|---|---|
| `structure` / `class` | **必須**有說明，無例外 |
| 重要的 `lemma` / `def` | 應有說明；顯而易見的可省略 |
| `instance` / `simp` lemma | 只為重要的加說明 |

---

## 檔案結構

### 兩段式結構

多個 namespace 並列時，**必須**採用兩段式結構：

1. **頂層定義區**：共用 helper、private def、class 宣告（讓讀者先看到「有什麼」）
2. **各 namespace 實作區**：每個 namespace 的 lemma / def，以橫線分隔

### 橫線分隔

```lean
-- ─── NamespaceName ──────────────────────────────────────────────────────────────

namespace NamespaceName
...
end NamespaceName
```

- 橫線字元使用 `─`（U+2500），不是 `-`（hyphen）或 `—`（em dash）
- 性質類似的檔案須具備相同的結構順序（如 Product、Equalizer、InitialTerminal）

---

## Class / Instance 慣例

### 參數風格

| 情境 | 風格 | 範例 |
|---|---|---|
| 查詢唯一 instance | `[h : Foo]` 或 `[Foo]` | `Limit.data [Limit F]`、`Representable.data [h : Representable F]` |
| 操作多個 instance 或變換 | `(u : Foo)` | `Limit.unique (h₁ h₂ : Limit F)` |
| 返回 class type 的 def | **必須** `@[reducible]` | `LimitData.toLimit`、`Universal.ofIso` |
| 自動推導 instance | `instance` | `Limit.universal [Limit F] : CoUniversal Δ F` |

### 層級委託（instance chain）

更具體的 class 應提供 instance 到更一般的 class：

```
Limit F  ──instance──▸  CoUniversal Δ F  ──instance──▸  CoRepresentable Hom[Fᵒᵖ–, F]
CoLimit F  ──instance──▸  Universal Δ F  ──instance──▸  Representable Hom[X, G–]
```

這讓 `Limit` 自動繼承 `CoUniversal` 和 `CoRepresentable` 的所有 API（`data`、`unique` 等）。

### Hom 記號的 elaboration

`Hom[X, G–]` 等複合記號在 instance / def 中可能需要明確的 implicit category 參數：

```lean
-- ✗ 可能無法 elaborate
def foo (h : Universal G X) : Representable Hom[X, G–] := ...

-- ✓ 加上明確的 category 參數
instance foo {G : D ⥤ C} {X : C.obj}
    [h : Universal G X] : Representable Hom[X, G–] := ...
```

### 原版 / 對偶對稱

對偶 pair **必須**具備平行的結構（相同的欄位名稱、相同的 API、相同的證明風格）：
- `Representable` / `CoRepresentable`
- `Universal` / `CoUniversal`
- `Limit` / `CoLimit`
- 各 Shapes（`Product` / `CoProduct`、`Equalizer` / `CoEqualizer` 等）

---

## 證明風格

- 優先使用 term-mode 證明（如 `congrArg`、`congrFun`、`funext`）
- 簡單的等式證明用 `by simp` 或 `by grind`
- 需要 associativity 時用 `by grind` 或 `by simp [←Category.assoc]`
- 避免冗長的 tactic chain——若超過 5 行，考慮提取輔助 lemma
- `aesop_cat` 僅用於 structure 欄位的預設證明
- **禁止**將多行壓縮成一行當成簡化證明的手段
- 證明卡住時，用 `fail "stop"` 查看 goal state，而非盲目嘗試不同 tactic

---

## 注意事項

- 注意記憶體用量，盡力**避免記憶體洩漏**
- 修改程式碼後**必須**確保零警告（`lake build` 無 warning）
- 修改任何公開宣告的名稱後，**必須**同步更新該檔案的模組標頭
- 返回 class type 的 `def` **必須**加 `@[reducible]`（否則 Lean 會報錯）
