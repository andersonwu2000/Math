import Mathlib.Init
import Aesop

/-!
# Tactic/Init.lean

Category theory 自動化證明的基礎策略。

## 定義
- `aesop_cat` — 自動證明 category theory 等式的 tactic macro
-/

-- 宣告 `CategoryTheory` 的 aesop rule set，供 `aesop_cat` 使用
declare_aesop_rule_sets [CategoryTheory]

/--
`aesop_cat`：自動證明 category theory 等式的 tactic macro。

依序嘗試：
1. `intros; apply_rfl`（reflexivity）
2. 以 `CategoryTheory` rule set 執行 `aesop`
3. 退而使用 `simp`

用於 category axiom（`id_comp`、`comp_id`、`assoc`）的預設證明，
以及 functor、natural transformation 的定義中。 -/
macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic| first |
    intros; apply_rfl |
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]) |
      simp)
