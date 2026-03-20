# 格式規範

模組標頭、行內說明、檔案結構。

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
  - 若兩個 namespace 具有完全相同的屬性結構，允許以 `/` 合併（如 `` ### `Complete` / `ShapeComplete` ``）
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
- 橫線分隔僅用於 `namespace … end` 區塊；`section … end` 區塊不需要橫線分隔
- 性質類似的檔案須具備相同的結構順序

### Universal property 檔案結構

定義 universal property class 及其對偶的檔案（Representable、UniversalProperty、Limits/Basic、各 Shapes 等）遵循統一的區塊順序：

```
頂層定義區：class X, class CoX, structure XData, structure CoXData

── X ──
namespace X
  data, unique, ...
end X
XData.toX

── CoX ──
namespace CoX
  data, unique, ...
end CoX
CoXData.toCoX
```

- `Data.toX` 放在對應 namespace **之後**，不是之前
- 每個原版 / 對偶 pair 的結構必須平行
