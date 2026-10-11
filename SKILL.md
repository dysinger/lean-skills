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

**Well-founded recursion over a measure: the `WellFounded.fix` idiom.** To define a
function that recurses on a `measure : α → Nat` rather than a structural argument:

```lean
noncomputable def go (measure : α → Nat) (h : ∀ a a', step a = some a' → measure a' < measure a)
    (a : α) : β :=
  WellFounded.fix (InvImage.wf measure Nat.lt_wfRel.wf) (fun a ih =>
    match ha : step a with
    | none => …base…
    | some a' => …ih a' (h a a' ha)…
  ) a
```

The recursion equation is **not** `rfl` — it is `WellFounded.fix_eq` (`unfold go; rw
[WellFounded.fix_eq]`). The `measure`/`h` pair is the honest replacement for a bare
"it terminates" prose claim, and keeps the result `[propext, Quot.sound]`-only.

**Don't `simp [defWithTerminationBy]` — it loops on the recursion equation.** A `def` with
`termination_by`/`decreasing_by` becomes `@[irreducible]` and `simp [f]` on its recursion
equation loops (the RHS contains the recursive call). Use `rw [f.eq_1]` (the auto-generated
equation) or `unfold f` + `rw [WellFounded.fix_eq]` instead.

**Dependent `match h : e with` won't reduce under `simp`, but `rw [h]` does.** A
`match h : e with | none => … | some (x,y) => …` (the dependent, hypothesis-carrying form)
resists `simp`/`rcases` when `e` is a free term. To reduce it in a hypothesis `hf`:
`rw [propEq] at hf` (rewrite the scrutinee to a constructor literal, e.g. `none`), then the
match reduces. For the proof-carrying `getLast h`-style arguments, prefer the `Option`
variant (`getLast?`) and `List.getLast?_eq_some_iff : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a]`
to avoid a `List ≠ []` proof argument that breaks `rw`'s motive.

**`#print axioms ModuleName` is shadowed by a type of the same name.** If `namespace Codec`
declares a type `Codec`, then `#print axioms Codec` resolves the *type*, reporting
"does not depend on any axioms" (trivially true), and `#print axioms Codec.Foo` fails with
"Unknown constant". Print axioms on **top-level declarations** (`Iso.foldl`, `Codec.roundtrip`)
and pass a bare `import` (not the module path) to `lake env lean`. The trailing
`unknown declaration 'main'` from `lean --run` is the interpreter, not a proof failure.

---

## 3. `partial`, coinduction, nonempty

**`partial def` requires a `Nonempty` witness for the return type.** A recursive
description/configuration value (e.g. `many : Codec α → Codec (List α)`, an
infinite AST) must be `partial`. Lake/Lean will fail with "could not prove that
the type … is nonempty" unless you give an `instance {α} : Inhabited (Codec α)`
(or `deriving Nonempty`) — every such inductive has a base constructor to point at.

**Coinductive `Iso`-level combinators are usually a *termination* problem, not a
"coinduction" one.** The inverse law (`Iso.law`) is a `∀ a b, …` `Prop`; proving it
for an iterated/folding combinator needs the *iteration to terminate*, which is
**well-founded recursion**, not coinduction. Make the well-foundedness witness an
explicit `measure : α → Nat` argument plus a `Prop`-valued condition that each step
decreases it (e.g. `∀ a a' b, i.unapply a = some (a', b) → measure a' < measure a`),
and define the two directions by `WellFounded.fix (InvImage.wf measure Nat.lt_wfRel.wf)`.
The law then closes by `WellFounded.induction` on the measure. **This avoids
`Classical.choice`**: `WellFounded.fix` is constructive, so such combinators depend only
on `[propext, Quot.sound]`.

**Some "obvious" invertible combinators have *no* field law.** A general `iterate
(step : Iso α α) : Iso α α` (apply/unapply `step` until it fails) is **not** a true
`Iso` for arbitrary `step`: the forward fixpoint (`apply a = none`) and backward
fixpoint (`unapply a = none`) need not coincide, since `apply a = some b ↔ unapply b
= some a` does not force `apply a = none ↔ unapply a = none`. Encoding the law would
need a per-element "isolated chain in both directions" precondition — the paper's
own "modulo equivalence classes" glims. Prefer to **define the specific combinator
(`foldl`) directly** and omit the general `iterate`, documenting why, rather than
shipping a subtly-unsound law.

**Don't "fix" a nondeterministic (backtracking) decoder by committing `|`.** A
syntax-description `|` whose denotation is a *union* (`Rel (p | q) = Rel p ∨ Rel q`)
agrees with a *list* decoder `decode (p | q) s = decode p s ++ decode q s` **by
construction** — and that is what makes the bidirectional law unconditional. Attempting
to make the decoder deterministic (single result, committed `|`) forces a prefix-disjointness
gate that is **unprovable for repetition**: `many p = nil | cons $ p * many p` has a `nil`
branch that always succeeds (consumes 0 bytes), and `nil` vs `cons` are never
prefix-disjoint because `[]` is a proper prefix of *every* non-empty string. If you hit
"the empty/non-empty choice can't be made prefix-disjoint", the fix is usually to **restore
backtracking (list-returning `decode`)**, not to pile on more structural predicates
(`NonNull`/`Disjoint`/`Unambiguous`). Keep the codec's *semantics* faithful (backtracking
union); treat efficiency (the paper's own "exponential/space-leak under unlimited
backtracking" caveat) as a *separate* later optimization that preserves the same denotation,
rather than changing the semantics to make it fast.

**A list-returning `decode` proves cleanly via `List.mem_*`, but avoid `.map` insides.**
`(x, r) ∈ decode d s ↔ ∃ s₀, s = s₀ ++ r ∧ Rel d x s₀`. Cases unfold with
`rw [decode, List.mem_append]` (`alt`), `rw [decode, List.mem_filterMap]` (`iso`), and
`rw [decode, List.mem_flatMap]` (`seq`) — note `List.mem_flatMap`, `List.mem_filterMap`,
`List.mem_map`, `List.mem_singleton`, `List.mem_append` are **not** `[simp]`, so `rw` them
explicitly. For `seq`, write the decoder as a *nested `flatMap` into a singleton list*
(`(decode d₁ s).flatMap fun (x,t) => (decode d₂ t).flatMap fun (y,s₂) => [((x,y),s₂)]`),
rather than `flatMap` + `.map`: `List.mem_map` leaves an unresolved metavariable for the
element type ("`x✝ : ?m` is not an inductive datatype") that breaks `rcases`, while
two `mem_flatMap` + `mem_singleton` steps destructure cleanly with `cases` on the pair
equality. `rcases` a pair-equality hypothesis `((a,y),s₂) = ((x₁,x₂),r)` with
`cases h` (then `subst`), not `rcases h with ⟨…, …⟩`.

**`at` is a reserved token — never use it as a binder.** `rcases h with ⟨at, hat, hm⟩`
parses `at` as the tactic keyword and fails with "unexpected token 'at'; expected '⟩'".
Name such binders `ab`/`pair`/`w` instead.

**Recursive syntax descriptions (`many`) are coinductive in the *parser*, inductive in the
*denotation*.** A derived `many p = nil $ pure () | cons $ p * many p` has two readings:
its denotational `Rel` is the **least** `nil`/`cons` fixpoint — a well-founded relation on the
list, total for *every* `p`; its *execution* into a strict `List` is total **iff** `p` consumes
≥1 byte per step (the productive guard), and is genuinely non-total (infinitely many `[]`
results) when `p` can match empty. This is a constructive fact, not a bug: do **not** "fix" it
with a fuel counter + `Productive` predicate (that fabricates wrong results — e.g. a
`many (pure ())` on `[]` returns a non-empty list — and is a classical gate, not purity).
The correct constructive guard is **well-founded recursion on the consumed string**: each
`cons` step recurses on a strictly shorter remaining `s`, so `s.length` *is* the termination
measure, and the totality boundary ("terminates iff `p` is productive") is a **theorem**, not a
precondition in the statement.

**Lean 4 `coinductive` is predicate-only; a strict `List` cannot hold infinite results.**
You cannot define a coinductive *data* type with `coinductive` (it only makes `Prop`
predicates). So a "total decoder for unbounded repetition" changing the result carrier to a
lazy stream must be hand-encoded (e.g. a `Thunk`-guarded `structure`, or `Nat → Option α`);
and note that even then, `decode (p | q) = decode p ++ decode q` over an *infinite* `p` branch
is not a computable `Nat`-indexed function (you cannot compute `q`'s offset without deciding
whether `p` is finite). Decide explicitly whether you keep the strict-list carrier (and make the
totality boundary a theorem) or migrate to a lazy carrier — don't pretend a fuel index is the
lazy carrier.

**A type-changing constructor (`many : C α → C (List α)`) breaks `induction` — use `rec`.**
`induction d` fixes the index type, so a constructor whose *result* type differs from its child's
(`many p : C (List α)` built from `p : C α`) cannot be handled by it. Use `C.rec` (whose motive is
`(α : Type) → C α → Sort`) so each branch gets its recursion at the *child's* type. The `ih` in
such a branch is then already at the element type — call it, don't re-invoke the outer function.

**Cannot `mutual` a `def` with an `inductive`.** Lean mutual blocks are all-definitions or
all-inductives. If a `Rel` (structural `def`) and a companion `RelMany` (the least fixpoint over
`List`) are mutually recursive, encode `RelMany` as a **parameterized higher-order helper**
(`relManyList R xs s := match xs … R x s₁ …`) that takes the step relation `R` as an argument,
then call it with `Rel p` — `Rel` stays a transparent structural `def` (so `Rel_*` lemmas stay
`Iff.rfl`/`by simp [Rel]`), and the recursion is on the finite list, not the description.

**`sizeOf` on a recursive inductive is opaque through its `SizeOf` instance.**
`sizeOf p < sizeOf (many p)` does not close by `simp`/`omega` because `sizeOf` uses
the `[instance_reducible]` `_sizeOf_inst`, and `Codec._sizeOf_1` (the auto-generated size
function) is not itself a `simp` lemma. Unfold explicitly: `unfold sizeOf; simp only
[_sizeOf_inst, Codec._sizeOf_1]; omega`, or define your own transparent structural measure
(`csize (many p) = csize p + 1` by `rfl`) and use `termination_by csize d`. The *transparent*
measure is usually less friction than fighting the built-in `sizeOf` for a type-changing node.

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

- 2026-10-11 — `partial def` generates **no equation and cannot be unfolded**:
  `#check f.eq_1` is unknown and `unfold f` fails, so a denotation built by
  `match` on a `partial` description value (`Rel (many p)`) is irreducibly stuck —
  an equality like `Rel (many p) xs s ↔ relRepeat (Rel p) xs s` is *unprovable*.
  The honest reading of "derived recursive combinator, total as a denotation" is:
  the denotation is a separate total relation (`relRepeat`), never `Rel` applied to
  a `partial` `Codec`.
- 2026-10-11 — `termination_by` wraps the function body in `have f := <arg>` house-
  keeping, so `unfold f; rw [WellFounded.fix_eq]; rfl` leaves a stray `have` and a
  same-goal mismatch. For a `def` whose recursion equation you need to prove by
  `rfl`/`WellFounded.fix_eq`, write it with **explicit `WellFounded.fix`** (mirroring
  a proved `foldUnapply`), not `termination_by`. The computed nested call then stays
  `WellFounded.fix … s₁` (definitionally the `def` again), so `rfl` closes.
- 2026-10-11 — well-founded recursion threads a membership proof via
  `list.attach.flatMap (fun ⟨(x, s₁), _hmem⟩ => …)`, and `decreasing_by` (or the
  inner `fix` call) can `exact h x s₁ s _hmem`; name the proof `_hmem` or the
  "unused variable" linter fires despite its use in the termination obligation.
  `Nat.lt_wfRel` is a bundled `WellFoundedRelation`, not a relation — write the
  measure as `InvImage (· < ·) (fun s => s.length)` with `InvImage.wf (fun s =>
  s.length) Nat.lt_wfRel.wf`; and `WellFounded.induction` fixes the non-measure args,
  so `revert`/`intro` them (e.g. `revert xs r`) to get an IH general over all of them.
- 2026-10-10 — recursive descriptions (`many`) + the total-decoder question: the
  parser reading is coinductive, the denotational `Rel` is an inductive least
  fixpoint (total always); strict-`List` execution is total iff `p` consumes a
  byte/step, and genuinely non-total for empty-matching `p` (infinitely many
  results). A fuel counter + `Productive` prop is *wrong* (fabricates results,
  classical) — the constructive guard is well-founded recursion on `s.length`,
  and the totality boundary is a theorem, not a precondition. Lean 4
  `coinductive` is predicate-only (no coinductive data); `alt`-append over an
  infinite branch isn't `Nat`-computable; type-changing nodes need `C.rec` not
  `induction`; can't `mutual` a `def` with an `inductive` (use a higher-order
  parameterized helper); `sizeOf` is opaque via its `SizeOf` instance (prefer a
  transparent `csize` measure).
- 2026-10-10 — committed-`|` is a wrong turn for syntax descriptions: a
  deterministic single-result decoder forces an *unprovable* prefix-disjointness
  gate on repetition (empty branch always wins; `nil`/`cons` never prefix-disjoint
  since `[]` is a proper prefix of every non-empty string). Restore the paper's
  backtracking-union `|` (list-returning `decode`, `decode (p|q) = decode p ++ decode
  q`) so the bidirectional law is unconditional; treat efficiency as a separate,
  semantics-preserving optimization, not a reason to change semantics.
- 2026-10-10 — list-returning `decode` proofs: `List.mem_flatMap`/`mem_filterMap`/
  `mem_append`/`mem_singleton` are not `[simp]` — `rw` explicitly; write `seq` as
  nested `flatMap`→singleton (not `flatMap`→`.map`, which leaves a metavariable that
  breaks `rcases`); `cases` pair-equalities (`((a,y),s₂) = ((x₁,x₂),r)`) then `subst`;
  `at` is a reserved token — never a binder name.
- 2026-10-10 — `foldl`/`iterate`: well-founded recursion replaces "coinduction" for
  `Iso`-level combinators (`measure` witness + `WellFounded.fix`, `[propext,
  Quot.sound]`-only, no `Classical.choice`); general `iterate` has no field law
  (fixpoint asymmetry); `termination_by` defs are `[irreducible]` so `simp [f]`
  loops — use `f.eq_1`/`WellFounded.fix_eq`; `match h : e` reduces via `rw [h]`,
  not `simp`; `List.getLast?` is proof-free vs `getLast h`; `#print axioms` is
  shadowed by a same-named type — use top-level declarations.
- 2026-10-10 — seeded: module/namespace layout, roots semantics, ByteArray vs
  List UInt8, do-vs-match proving, partial/nonempty, notation collisions,
  indexed-inductive vs structural-`def` `Rel`, Repr/`#eval` ergonomics,
  `-!` doc-after-import rule, `@`-notation for instance-implicit patterns,
  stored-instance recovery in `match`, IH argument order under `induction`.
