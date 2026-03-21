import Lean
import MATH.Category.Basic

/-!
# Tactic/Reassoc.lean

本檔案定義 `@[reassoc]` attribute：

- `@[reassoc]`：從 morphism 等式 `h : lhs = rhs` 自動生成
  associativity 版本 `h_assoc : ∀ {Z} (k : _ ⟶ Z), k ○ lhs = k ○ rhs`。
- 可加上 `(attr := simp)` 等選項，將生成的 lemma 同時標記為其他 attribute。
-/

open Lean Meta

namespace CategoryTheory

syntax (name := reassoc) "reassoc" (" (" &"attr" " := " Lean.Parser.Term.attrInstance,* ")")? : attr

private def mkAssocDecl (declName : Name) : MetaM Name := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs conclusion => do
    let some (_, lhs, rhs) := conclusion.eq? |
      throwError "@[reassoc]: conclusion is not an equality"
    let lhsType ← inferType lhs
    unless lhsType.isAppOf ``Category.hom do
      throwError "@[reassoc]: equality must be between morphisms (Category.hom), got {lhsType}"
    let args := lhsType.getAppArgs
    let C := args[0]!
    let Y := args[2]!
    withLocalDecl `Z .implicit (← mkAppM ``Category.obj #[C]) fun Z => do
      withLocalDecl `k .default (← mkAppM ``Category.hom #[C, Y, Z]) fun k => do
        let mk_comp x := mkAppOptM ``Category.comp #[C, none, none, none, k, x]
        let newConc ← mkEq (← mk_comp lhs) (← mk_comp rhs)
        let origProof := mkAppN (mkConst declName (info.levelParams.map Level.param)) xs
        withLocalDecl `m .default lhsType fun m => do
          let congFn ← mkLambdaFVars #[m] (← mk_comp m)
          let proof ← mkCongrArg congFn origProof
          let allVars := xs ++ #[Z, k]
          let newName := declName ++ `assoc
          addDecl <| .thmDecl {
            name        := newName
            levelParams := info.levelParams
            type        := ← mkForallFVars allVars newConc >>= instantiateMVars
            value       := ← mkLambdaFVars allVars proof >>= instantiateMVars
          }
          return newName

/--
`@[reassoc]` attribute：從等式 `h : lhs = rhs`（morphism 間）自動生成
associativity 版本 `h_assoc : ∀ {Z} (k : _ ⟶ Z), k ○ lhs = k ○ rhs`。

用法：
- `@[reassoc]`：僅生成 `h_assoc`
- `@[reassoc (attr := simp)]`：同時將生成的 lemma 標記為 `simp` -/
initialize registerBuiltinAttribute {
  name  := `reassoc
  descr := "Generates `h_assoc` from `h : lhs = rhs` (morphisms). \
            Accepts `(attr := ...)` to tag the generated lemma with additional attributes."
  add   := fun declName stx _attrKind => do
    let attrs ← match stx with
      | `(attr| reassoc (attr := $attrs,*)) => pure attrs.getElems
      | `(attr| reassoc)                    => pure #[]
      | _                                   => throwError "invalid @[reassoc] syntax"
    let newName ← MetaM.run' <| mkAssocDecl declName
    for attr in attrs do
      let impl ← getAttributeImpl attr.getKind
      impl.add newName attr .global
}

end CategoryTheory
