# CLAUDE.md

此檔案提供 Claude Code 在本儲存庫中工作時的指引。
所有規範皆為**強制性**，除非明確標註「建議」。

慣例規範：[`CLAUDE/convention.md`](CLAUDE/convention.md)
格式規範：[`CLAUDE/format.md`](CLAUDE/format.md)
證明策略：[`CLAUDE/proof.md`](CLAUDE/proof.md)

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

- 以 **Lean 4** 從頭建構的數學函式庫（目前以範疇論為核心，未來將擴充至其他領域）
- **不**包裝 Mathlib，僅使用 Mathlib 的策略（`aesop`、`simp`、`grind`）與 Lean 的 `Type`
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

## 注意事項

- 注意記憶體用量，盡力**避免記憶體洩漏**
- 修改程式碼後**必須**確保零警告（`lake build` 無 warning）
- 修改任何公開宣告的名稱後，**必須**同步更新該檔案的模組標頭
- 返回 class type 的 `def` **必須**加 `@[reducible]`（否則 Lean 會報錯）

---

## 證明策略

詳見 [`CLAUDE/proof.md`](CLAUDE/proof.md)。
