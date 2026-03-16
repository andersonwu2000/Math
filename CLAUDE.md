# CLAUDE.md

此檔案提供 Claude Code 在本儲存庫中工作時的指引。

## 建置指令

```bash
lake build              # 建置整個專案
lake build MATH         # 建置特定目標
lake update             # 更新相依套件（修改 lake-manifest.json 後執行）
```

本專案沒有獨立的測試執行器——`.lean` 檔案中的證明在建置時即會被驗證。

- **證明前**，以 `lake build MATH.<模組>` 檢查缺失和錯誤
- **證明後**，以 `lake build MATH.<模組>` 檢查證明是否有誤
- 若證明困難，可以考慮新增輔助 lemma
- 若證明難度過高或認為不可行，可以放棄，再行評估

## 架構

- 以 **Lean 4** 從頭建構的範疇論函式庫
- **不**包裝 Mathlib 的範疇論，僅使用 Mathlib 的策略（`aesop`、`simp`、`grind`）與 Lean 的 `Type`
- 工具鏈：`leanprover/lean4:v4.29.0-rc6`

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

### 模組結構

| 路徑 | 內容 |
|---|---|
| `Category/Basic.lean` | `Category`、opposite、Whisker |
| `Category/Tactic/` | 自訂策略 `aesop_cat` |
| `Category/Functor/` | `Functor`、`Cat`、Hom 函子、常數函子、雙函子、fully faithful、essentially surjective |
| `Category/NatTrans/` | 自然變換、自然同構、水平合成 |
| `Category/Morphism/` | mono/epi、iso、preserve/reflect |
| `Category/Structure/` | 函子範疇、積範疇、`Types` |
| `Category/Adjunction/` | 伴隨、equivalence |
| `Category/Limits/` | 極限、cone |
| `Category/Yoneda.lean` | 米田引理 |
| `Category/UniversalProperty.lean` | Universal / couniversal property |

> `__Test__.lean` 直接使用 Mathlib 的伴隨 API，而非自訂版本。
> `Math/tmp/` 為實驗性／進行中的工作。

## Coding 規範

### 語言

- 註解與文件說明以**繁體中文**撰寫
- 數學專有名詞保持**英文**（如 functor、morphism、adjunction）
- 定義和定理名稱以**英文**撰寫

### 命名慣例

| 類型 | 慣例 | 範例 |
|---|---|---|
| 定義 / structure | `UpperCamelCase` | `HomEquiv`、`AdjointEquivalence` |
| lemma / def | `snake_case` 或 `lowerCamelCase` | `map_comp`、`left_triangle` |
| typeclass | `Is` 前綴 | `IsMono`、`IsIso`、`IsSplitMono` |
| 性質 class | 形容詞 | `Full`、`Faithful`、`FullyFaithful` |
| 互轉 | `A.B` / `B.A` | `HomEquiv.Adjunction` ↔ `Adjunction.HomEquiv` |
| 保持 / 反射 | `Preserve.X` / `Reflect.X` | `Preserve.IsIso`、`Reflect.Iso` |
| 消去律 | `cancel` | `IsMono.cancel`、`IsSplitEpi.cancel` |
| 逐點版本 | `_app` / `_apply` 後綴 | `hom_inv_id_app`、`naturality_apply` |
| iso 相關 | `hom_inv_id` / `inv_hom_id` | 保持一致方向 |

- 使用 `lemma` 而非 `theorem`（除非手動指定）
- 對偶版本命名加 `co` 前綴（`coUniversal`、`IscoLimit`）

### 文件說明格式（`/-! ... -/`）

每個 `.lean` 檔案開頭使用以下格式：

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
- `#` 為檔名，`##` 為定義 / 定理區段，`###` 為 namespace
- 同一 namespace 的定理用 `.method` 省略前綴
- 只列出主要的定義和定理，不需列舉所有 simp lemma 或 instance
- 無定理的檔案可省略 `## 定理` 區段

### 行內文件說明（`/-- ... -/`）

- structure 和 class 需要簡短的 `/-- ... -/` 說明
- 重要的 lemma / def 加說明，顯而易見的可省略
- 只為重要的 instance 或 simp lemma 加說明

### 證明風格

- 優先使用 term-mode 證明（如 `congrArg`、`congrFun`、`funext`）
- 簡單的等式證明用 `by simp` 或 `by grind`
- 需要 associativity 時用 `by grind` 或 `by simp [←Category.assoc]`
- 避免冗長的 tactic chain——若超過 5 行，考慮提取輔助 lemma
- `aesop_cat` 僅用於 structure 欄位的預設證明

### 注意事項

- 注意記憶體用量，盡力**避免記憶體洩漏**
- `Representable.lean` 和 `Reassoc.lean` 暫不維護
