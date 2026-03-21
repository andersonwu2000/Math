# 開發路徑

根據 `CLAUDE/doc/Note.tex` 與現有程式碼的差距分析。

---

## 現況總覽

| Note.tex 章節 | 狀態 | 備註 |
|---|---|---|
| §1 Sets | — | 基礎公理，不需形式化 |
| §2 Elementary | ✅ 完成 | Category, Functor, NatTrans, Mono/Epi, Duality |
| §3 Yoneda Lemma | ✅ 完成 | Hom functor, Yoneda embedding, Universal property |
| §4 Adjunctions | ✅ 大致完成 | HomEquiv, Unit/Counit, Equivalence；缺 adjunction 合成 |
| §5 Limits | 🔶 部分完成 | 基本定義 + shapes 完成；缺 preservation, RAPL, AFT |
| §6 Monoidal Category | ❌ 未開始 | |
| §7 Enriched Category | ❌ 未開始 | |
| §8 Higher Algebra | ❌ 未開始 | |

---

## Phase 1：補完 Limits（§5 剩餘部分）

優先級最高——所有後續內容（RAPL、AFT、monoidal via products）都依賴完整的 limit 理論。

### 1.1 修復 `Limits/Instances/`（4 個檔案）

現有 4 個 instance 檔案無法編譯（API 未同步）。

| 檔案 | 問題 |
|---|---|
| `Instances/Types.lean` | `HasInitial`/`HasTerminal` 已重構為 `Initial`/`Terminal` + `InitialData`/`TerminalData` |
| `Instances/Cat.lean` | 同上 |
| `Instances/FunctorCat.lean` | 同上 + import 路徑錯誤 |
| `Instances/ProductCat.lean` | 同上 |

**工作量**：小（API 名稱替換 + import 修正）

### 1.2 Limit preservation / reflection

對應 Note.tex §5.3。需要新增：

| 定義/定理 | 說明 | 建議檔案 |
|---|---|---|
| `Preserve.Limit F H` | `F` 保持 `H` 的 limit | `Limits/Preserve.lean` |
| `Reflect.Limit F H` | `F` 反射 `H` 的 limit | 同上 |
| `Continuous F` | `F` 保持所有 limit | 同上 |
| `Cocontinuous F` | `F` 保持所有 colimit | 同上 |
| hom functor 是 continuous | Note.tex Prop 5.3.2 | 同上 |
| RAPL | right adjoint preserves limit | `Limits/RAPL.lean` 或同上 |
| LAPC | left adjoint preserves colimit | 同上（對偶） |
| fully faithful 反射所有 limit | Note.tex Prop 5.3.4 | 同上 |
| Yoneda embedding create limit | Note.tex Prop 5.3.5 | 同上 |

**依賴**：`Limits/Basic.lean`, `Adjunction/Basic.lean`, `Yoneda.lean`
**工作量**：中

### 1.3 Complete = Products + Equalizers

對應 Note.tex §5.4 的核心定理。需要：

| 定義/定理 | 說明 |
|---|---|
| `lim F ≅ eq(f₁, f₂)` | limit 可用 product + equalizer 表示 |
| `Complete ↔ HasProducts + HasEqualizers` | 等價定理 |

**依賴**：`Limits/Complete.lean`, `Shapes/Product.lean`, `Shapes/Equalizer.lean`
**工作量**：大（需要形式化 dom/cod functor 與 parallel pair 構造）

### 1.4 Adjoint Functor Theorem（選擇性）

對應 Note.tex §5.5。Freyd 的 AFT 需要：
- comma category `Δ X ↓ G`（目前未實作）
- jointly weakly initial set
- joint equalizer

**工作量**：大
**建議**：可延後至 Phase 2，先完成 1.1–1.3

---

## Phase 2：補完 Adjunctions（§4 剩餘部分）

### 2.1 Adjunction 合成

對應 Note.tex §4.2 Prop (1)。

| 定理 | 說明 |
|---|---|
| `(F' ○ F) ⊣ (G ○ G')` | `F ⊣ G` 且 `F' ⊣ G'` 則合成也是 adjunction |
| adjoint uniqueness | `F ⊣ G` 且 `F' ⊣ G` 則 `F ≅ F'` |

**依賴**：`Adjunction/Basic.lean`
**工作量**：中

### 2.2 Diagonal-Limit Adjunction

對應 Note.tex §5.1 定義 (3)。

| 定理 | 說明 |
|---|---|
| `Δ ⊣ lim` | Complete category 中，`Δ ⊣ lim` 和 Limit 間的轉換 |

**依賴**：Phase 1.2（RAPL）+ `Limits/Complete.lean`
**工作量**：中

---

## Phase 3：Monoidal Category（§6）

### 3.1 基礎結構

| 定義 | 說明 | 建議檔案 |
|---|---|---|
| `MonoidalCat` | `(C, ⊗, I, a, l, r)` | `Monoidal/Basic.lean` |
| `BraidedMonoidalCat` | `+ braiding b` | 同上或 `Monoidal/Braided.lean` |
| `SymmetricMonoidalCat` | `+ b ○ b = id` | 同上 |
| `ClosedMonoidalCat` | `⊗ ⊣ [-, -]` | `Monoidal/Closed.lean` |

**依賴**：Core category theory（已完成）
**工作量**：中

### 3.2 Cartesian monoidal structure

| 定理 | 說明 |
|---|---|
| finite product category 是 monoidal | Note.tex §6.3 |
| `Cat` 的 monoidal structure | `(Cat, ×, 1)` |
| `[-, -]` 是 closed monoidal | `×  ⊣ [-, -]` in Cat |

**依賴**：Phase 1（complete limits） + Phase 3.1
**工作量**：中

### 3.3 Coherence（選擇性）

| 定理 | 說明 |
|---|---|
| Pentagon diagram | associator coherence |
| Triangle diagram | unitor coherence |
| Hexagon diagram | braiding coherence |

**工作量**：大（coherence theorem 的形式化具有挑戰性）
**建議**：初期可作為公理（`axiom`），後續補證

---

## Phase 4：Enriched Category（§7）+ Higher Algebra（§8）

### 4.1 Enriched Category

| 定義 | 說明 | 建議檔案 |
|---|---|---|
| `EnrichedCat V` | V-category | `Enriched/Basic.lean` |
| `EnrichedFunctor` | V-functor | 同上 |
| `EnrichedNatTrans` | V-natural transformation | 同上 |
| `V` 是 V-category | Note.tex Prop 7.1 | 同上 |

**依賴**：Phase 3（monoidal category）
**工作量**：中

### 4.2 Monoid Object + Monad

| 定義 | 說明 | 建議檔案 |
|---|---|---|
| `MonoidObj V` | V 中的 monoid object | `Algebra/Monoid.lean` |
| `Mon V` | monoid category | 同上 |
| `Module M` | left module over monoid | 同上 |
| `Monad C` | monad = monoid in `[C, C]` | `Algebra/Monad.lean` |
| adjunction → monad | `GF` is a monad | 同上 |

**依賴**：Phase 4.1
**工作量**：中

---

## 建議優先順序

```
Phase 1.1  修復 Instances（小）
  ↓
Phase 1.2  Limit preservation + RAPL（中）
  ↓
Phase 2.1  Adjunction 合成（中）     ← 可與 1.2 並行
  ↓
Phase 1.3  Complete = Prod + Eq（大）
  ↓
Phase 2.2  Δ ⊣ lim（中）
  ↓
Phase 3.1  Monoidal basic（中）
  ↓
Phase 3.2  Cartesian monoidal（中）
  ↓
Phase 4.1  Enriched（中）
  ↓
Phase 4.2  Monad（中）
  ↓
Phase 1.4  AFT（大，選擇性）
Phase 3.3  Coherence（大，選擇性）
```

Phase 1.1 → 1.2 → 2.1 是即時可開始的工作，不需新增大量基礎設施。