---
name: Limit dot notation pitfall
description: Writing `Limit Hom[...]` inside namespace CategoryTheory triggers dot notation resolving to Limit.Canonical.Limit instead of the class Limit
type: feedback
---

When writing `Limit Hom[Fᵒᵖ–, X]` inside `namespace CategoryTheory`, Lean parses it as `Limit.Canonical.Limit Hom[Fᵒᵖ–, X]` due to dot notation, producing a function type instead of a class type.

**Why:** The existing `Limit.Canonical.Limit` instance takes `(F : J ⥤ C) (X : C.obj)` as arguments. Dot notation on `Limit <arg>` resolves to this before considering the class `Limit`.

**How to apply:** Use `CategoryTheory.Limit` (fully qualified) when referencing the `Limit` class in positions where the first argument could be matched by `Limit.Canonical.Limit`. Similarly for `@LimitData (Jᵒᵖ)` — the postfix `ᵒᵖ` notation causes `@LimitData J` to be parsed first. Use parentheses: `@LimitData (Jᵒᵖ)`.
