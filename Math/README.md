# MATH

以 **Lean 4** 從頭實作的範疇論函式庫，以範疇論為基礎，逐步建構基本數學結構與定理。

> 本函式庫**不包裝** Mathlib 的範疇論，僅依賴 Mathlib 的策略（`aesop`、`simp`、`grind`）以及與 Lean `Type` 的連接。

---

## 快速開始

**需求：** [Lean 4](https://leanprover.github.io/) 與 [elan](https://github.com/leanprover/elan)（自動管理版本）

---

## 專案結構

```
MATH/
├── Category/
│   ├── Basic.lean              ← Category、Whisker
│   ├── Functor/
│   │   ├── Basic.lean          ← Functor、Cat
│   │   ├── Bifunctor.lean      ← 雙函子工具
│   │   ├── Const.lean          ← 對角/常數函子 Δ
│   │   ├── FullyFaithful.lean  ← 全忠實函子
│   │   ├── Hom.lean            ← Hom 雙函子
│   │   └── Representable.lean  ← 可表函子
│   ├── NatTrans/
│   │   ├── Basic.lean          ← NatTrans ⇒
│   │   ├── Iso.lean            ← NatIso ≅
│   │   └── Horizontal.lean     ← 水平合成
│   ├── Morphism/
│   │   ├── Iso.lean            ← 同構
│   │   ├── EpiMono.lean        ← 滿射/單射態射
│   │   └── PreserveReflect.lean
│   ├── Structure/
│   │   ├── Types.lean          ← Types 範疇
│   │   ├── ProductCat.lean     ← C × D
│   │   ├── FunctorCat.lean     ← ⟦C, D⟧、eval、curry
│   │   └── Shapes.lean
│   ├── Adjunction/
│   │   └── Basic.lean          ← F ⊣ G
│   ├── Limits/
│   │   ├── Basic.lean          ← Complete、lim ⊣ Δ
│   │   └── Cone.lean           ← IsLimit、IscoLimit
│   ├── UniversalProperty.lean  ← Universal、coUniversal
│   └── Yoneda.lean             ← Yoneda 引理
├── Order/                      ← 序理論（規劃中）
├── set/                        ← 集合論（規劃中）
└── tmp/                        ← 實驗性程式碼
```

---

## 主要記號

| 記號 | 意義 |
|---|---|
| `X ⟶ Y` | 態射（hom 集合） |
| `𝟙 X` | X 上的單位態射 |
| `g ○ f` | 合成（g 接在 f 後） |
| `Cᵒᵖ` | 對偶範疇 |
| `C ⥤ D` | 函子型別 |
| `F ⇒ G` | 自然變換 |
| `F ≅ G` | 自然同構 |
| `F ⊣ G` | 伴隨 |
| `⟦C, D⟧` | 函子範疇 |
| `F[f]` | 函子作用於態射 |
| `α·X` | 自然變換在 X 的分量 |
| `Hom[f, g]` | Hom 雙函子作用於態射 |
| `Δ[X]` | 對角/常數函子 |
| `φ♯` / `φ♭` | 伴隨的 sharp / flat 轉置 |

---

## 已實作內容

- **範疇論核心**：範疇、函子、自然變換、自然同構
- **態射性質**：同構、滿射（Epi）、單射（Mono）、全忠實函子
- **重要範疇**：Types、積範疇（C × D）、函子範疇（⟦C, D⟧）
- **泛性質**：Universal / coUniversal、Yoneda 引理
- **Hom 函子**：`Hom : Cᵒᵖ × C ⥤ Types`，保持與反射同構
- **伴隨**：HomEquiv、HomMate、Units 三種建構方式
- **完備範疇**：極限函子、lim ⊣ Δ 伴隨

## 規劃中

- `?HigherCategory`、`?Monad`、`?KanExtension`
- `?Order`（序理論）
- `?Number`（數論）
- `?Algebra`（代數）
- `?Geometry`（幾何，考慮基於 topos 的拓撲）
- `?Analysis`（分析）

---

## 依賴

- [Lean 4](https://leanprover.github.io/) `v4.29.0-rc6`
- [Mathlib4](https://github.com/leanprover-community/mathlib4)（僅策略部分）
