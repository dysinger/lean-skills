---
name: lean
description: Supplements the official `lean4` skill with our own accumulated Lean 4 / Lake learnings (module & namespace layout, lakefile roots, proving ergonomics, partial/coinductive definitions, notation collisions). Use alongside `lean4` — this holds only deltas, never duplicates its content. Trigger when working with Lean 4 or Lake and the official skill is already in play.
license: CC-BY-4.0
---

# Lean 4 — Project Learnings (supplement to `lean4`)

This is **our own accumulating notebook** of Lean 4 / Lake lessons that are *not*
in the official skill. It augments, never replaces, the official skill:

- Official theorem-proving skill: [`lean4`](../lean4-skills/plugins/lean4/skills/lean4/SKILL.md)
- Official mathlib/setup skills: [`leanprover`](../leanprover/)

**Read this file after** the official `lean4` skill. Where they disagree, the
official skill's *proof-engineering* guidance wins; this file adds *project
layout, module-system, and library-authorship* lessons that the proof-focused
skill does not cover.

---

## When to read what

| Question | Read |
|---|---|
| How do I fill a `sorry`, search mathlib, debug a type mismatch? | the official [`lean4`](../lean4-skills/plugins/lean4/skills/lean4/SKILL.md) |
| How do I lay out a *library* package's namespace, `lakefile`, roots? | [§1 Module & namespace layout](#1-module--namespace-layout) |
| `ByteArray` proofs won't reduce / `simp` stalls on a primitive | [§2 Proving over primitives](#2-proving-over-primitives) |
| A `partial def`/recursive combinator won't typecheck | [§3 `partial`, coinduction, nonempty](#3-partial-coinduction-nonempty) |
| Notation collision with a reserved token (`\|`, `*`, `$`, `open`) | [§4 Notation & keyword collisions](#4-notation--keyword-collisions) |

---

## 1. Module & namespace layout

**Package name *is* the namespace boundary.** Unlike Haskell (`Data.*` is a
cross-package global namespace) or F\* (`Data.Codec`), in Lean each Lake package
owns a top-level namespace named after the package. There is **no shared
`Data.`/`Control.` hierarchy** across packages.

- A `lakefile.toml` `[[lean_lib]] name = "codec"` with `roots = ["Codec"]`
  makes `Codec/` the module root: `Codec/Foo.lean` → module `Codec.Foo`,
  and the package's declarations live under `namespace Codec`.
- To get Haskell's `Data.Codec.Foo`, either name the *package* `Codec` and use
  `Codec.Foo`, or (only if you genuinely want the redundant segment) put a
  `Data/` directory at the root. Convention leans to **no redundant segment**:
  the package boundary already plays the role Haskell assigns to `Data.`/`Control.`.

**`roots` is a module-name prefix, not a directory glob.** `roots = ["Codec"]`
includes module `Codec` (a top-level `Codec.lean`) *and* `Codec.*`
(`Codec/Foo.lean`). The default root for `name = "codec"` is the literal
lowercase `codec` — it will look for `codec.lean`. Explicit `roots = ["Codec"]`
is what makes the *capitalized* directory the root.

**Avoid the type-vs-module self-collision.** A module `Codec.Codec` containing
`namespace Codec` declaring `structure/inductive Codec` yields identifiers like
`Codec.Codec.Codec.iso`. Prefer the description type and the module to have
distinct names, or drop the redundant namespace.

**Naming (mathlib conventions).** Files and types UpperCamelCase; theorems and
`Prop`-valued terms snake_case; functions are named like their return type
(lowerCamelCase). The authoritative source:
<https://leanprover-community.github.io/contribute/naming.html>

**`/-! … -/` (module doc) must come *after* `import`, not before.** A `-!` doc
comment above the first `import` fails with "invalid `import` command, it must
be used in the beginning of the file". Put a plain `/- … -/` block (or `--`
lines) before imports, and reserve `-!` docs for *after* them.

---

## 2. Proving over primitives

**`Option.ne_none_iff_exists` gives `some x = o`, not `o = some x`.** After
`rcases … with ⟨x, h⟩`, apply `h.symm` before `simp [encode, …]` to reduce a
`match o with | some x => …`.

**`ByteArray` operations do not reduce.** In Lean ≤ 4.30, `ByteArray.append`,
`get!`, `extract`, and `size` are FFI/`copySlice`-backed and do **not** unfold
under `simp`/`rfl`, so `(a ++ b) ++ c = a ++ (b ++ c)` is *not* provable
mechanically (`ByteArray.ext` reduces to element-wise `Array` goals, not `List`
ones). The `List UInt8`-vs-`ByteArray` split mirrors the paper's `List Char`
model and is the standard escape hatch.

**Rule:** when a law must be *proved* (`rfl`/`simp`/`induction` only), model the
byte/char sequence as `List UInt8`; reserve `ByteArray` for the executable
wrapper you transport onto afterwards. In `Option`/`Except` code, write
interpreters with **explicit `match`, not `do` notation** — `do` desugars to
`Monad.bind` (`[implicit_reducible]`), which `rw`/`simp` will not reduce, so a
goal like `(do let __discr ← .ok (a, r); …) = …` gets stuck. Nested `match`
is definitionally transparent and closes by `rfl`.

**`Except.ok a >>= f` reduces to `f a`** by `rfl` (`Except.bind` is a `match`)
— but only if you are *not* in `do` notation. Use it to keep roundtrip proofs
mechanical.

**`@`-notation makes instance-implicit constructor args explicit in patterns.**
Matching a constructor that stores an instance (e.g. `pure {α} [DecidableEq α]`)
with a bare `| .pure _ => …` can stall on "typeclass instance problem is stuck
(DecidableEq ?m)". Write `| @Codec.pure _ _ _ => …` to match the instance
positionally. Conversely, the stored instance is *recovered* in a `match` branch,
so a decoder/encoder needs no `[DecidableEq α]` in its own signature — the
constructor supplies it.

**`induction` auto-generalizes trailing hypotheses; still pass them as IH args.**
`generalizing x` is flagged "Unnecessary" when `x` already appears in the goal,
but the induction hypothesis then binds them in order (`∀ x (h : P d) …`), so
invoke it as `ih a h hs r` (value first, then hypothesis), never `ih h hs r`.

---

## 3. `partial`, coinduction, nonempty

**`partial def` requires a `Nonempty` witness for the return type.** A recursive
description/configuration value (e.g. `many : Codec α → Codec (List α)`, an
infinite AST) must be `partial`. Lake/Lean will fail with "could not prove that
the type … is nonempty" unless you give an `instance {α} : Inhabited (Codec α)`
(or `deriving Nonempty`) — every such inductive has a base constructor to point at.

**Coinductive `Iso`-level combinators are a different beast.** `iterate`/`foldl`
(paper "fold as a small-step machine") are coinductive *at the `Iso` level*: their
`law` field would itself need a coinduction argument, so a finite `def` with a
proven law is impossible. Defer them; do **not** `sorry` the law (violates the
zero-sorry gate). Combinators that produce `Codec` values (no law field) can be
`partial def` with no proof obligation.

---

## 4. Notation & keyword collisions

Reserved Lean tokens that **cannot** be rebound as notations, and what breaks:

| Token | Collision |
|---|---|
| `\|` | inductive-constructor separator and `rcases` `Or` separator — redefining it as infix destroys all subsequent parsing |
| `*` | multiplication/binder; `infixr "*"` conflicts with `HMul` |
| `$` | risky; free-ish but collides with `$`-consuming macros in scope |
| `open` | reserved keyword — cannot be a binder name (`open close : Codec Unit` is a parse error); use `l r` / `op cl` |

`{α : Type}` implicit binders in an inductive's *index* (e.g.
`inductive Rel : {α : Type} → Codec α → … → Prop`) are fine, but `cases h` on the
resulting indexed inductive fails to eliminate ("Dependent elimination failed")
when the index is a non-variable constructor application. Prefer **structural
recursion defining `Rel` as a `def` over the description** (definitionally
reducible) over a standalone indexed `inductive` for provability.

---

## 5. Library ergonomics (Repr / #eval)

**`deriving Repr` only works when every field type has `Repr`.** A `structure`
with a `ByteArray`/`UInt8`-collection field fails `deriving Repr`; once the field
is `List UInt8` it succeeds. Symmetrically, `#eval` on a term whose result type
lacks `Repr` errors with "Unable to synthesize `MonadEval` instance … to adapt
<type> to `IO`" — derive `Repr` on your error/value types to keep smoke tests
evaluable.

---

## Append new learnings here

Date-stamped, one line each, latest first. Keep entries generic (no project
names/paths); the specific repo lives elsewhere.

## Changelog

- 2026-10-10 — seeded: module/namespace layout, roots semantics, ByteArray vs
  List UInt8, do-vs-match proving, partial/nonempty, notation collisions,
  indexed-inductive vs structural-`def` `Rel`, Repr/`#eval` ergonomics,
  `-!` doc-after-import rule, `@`-notation for instance-implicit patterns,
  stored-instance recovery in `match`, IH argument order under `induction`.
