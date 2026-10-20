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
| How do I make a parser/codec *fast*; why is it ~20-40x off C? | [§7 Work faster (carrier swap > FFI > compiler)](#7-work-faster-carrier-swap--ffi--compiler-and-lean-on-usize) — and the 2026-10-18 "boxed scalar ceiling" entry in the Append |

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

**A `-` immediately before `/` (`-/`) *closes* the `/-!`/`/--` comment early.**
Write `left- or right-associative`, never `left-/right-associative`, inside a doc
comment: the `-/` byte pair terminates the block at that point and the rest of
that line parses as code.

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

**Name the substrate and the transport differently.** Give the proof substrate a
*reducible alias* (`abbrev Bytes : Type := List UInt8`), so every `List` lemma
applies for free (a *newtype* would block the `simp` reduction the proofs live
on). Give the packed executable surface a *distinct* newtype (`structure Buffer
where byteArray : ByteArray`) — "proof model" and "run model" are different types
with different questions, not two names for one thing. Route the transport
`toBytes`/`ofBytes` through `Buffer.byteArray.data` (the stored `Array`) rather
than `ByteArray.toList` (see changelog).

**A transport *barrier* is not a faster run model — write a native array recursion +
prove it equal (the F* two-tier split).** A `decodeBuffer` defined as `(decode d
b.toBytes).map …` still materializes the whole `List` and runs the list interpreter, so it
keeps the `List` cons-cell cost. The F*/miTLS/EverCrypt move is to (a) keep the pure spec
over `List`/`Bytes`, (b) define the *run model* natively over an `Array` + a `Nat` index —
`decodeArray d a i : List (α × Nat)` reading `a[i]`, remainder an index, never cons-peeling a
byte list — and (c) prove **one** refinement lemma `decodeArray_eq : decodeArray d a i
≡ decode d (a.data.drop i)` by induction on `d` + `Array`↔`List` lemmas. Every spec-level law
then transfers by `rw [decodeArray_eq]`; you never re-prove `roundtrip`/`decode_spec`. Use
**`Array UInt8` (via `ByteArray.data`), never `ByteArray` itself**, as the run-model carrier:
`a.data`/`List.toArray`/`Array.toList` reduce under `simp`/`rfl`, while `ByteArray.get!`/
`.extract` are FFI-opaque and stall every law (the `lean`-skill §2 rule). This is the
"work faster without FFI/compiler" tier; the "fastest possible" (compiler/`@[extern]`) is a
separate, later change.

**The compiler/`@[extern]` tier: two `@[extern]` forms, and prefer the one with an
elaborating body.** To splice trusted, GC-less C into an already-proved run model without
touching the extraction pipeline, `@[extern]` has *two* shapes: (1) `opaque`/`constant`
(no Lean body — pure trust, nothing reduces in proofs), and (2) **`def` with an elaborating
body** — the stdlib `ByteArray` pattern (`@[extern "lean_byte_array_fget",
implicit_reducible] def get … | ⟨bs⟩, i, _ => bs[i]` in `Init/Data/ByteArray/Basic.lean`:
`size → lean_sarray_size`, `get! → lean_byte_array_get`, `copySlice → lean_byte_array_copy_slice`,
`hash → lean_byte_array_hash`). Shape (2) is the right tool for a proven codec: the Lean body
still elaborates and reduces, so refinement lemmas keep closing `[propext, Quot.sound]`-only,
and the C symbol is a *named, isolated trust seam* (the F\*/KaRaMeL `[@@noextract_to "krml"]
// primitive` posture). Verify the emitted `.lake/build/ir/<Module>.c` actually calls the
symbol (not the body).

**"GC-less C" is a type-mapping decision, not a runtime you write.** Lean's one C generator
(`Lean.Compiler.LCNF.EmitC`) emits a boxed/GC'd representation unconditionally (`Nat`→bignum
`lean_object *`, `List`→cons cells + RC, closures→`lean_alloc_closure`), and `EmitLLVM.lean` is
the other backend — there is no stock "unboxed C" target. F\*'s KaRaMeL shows the no-GC shape:
generated C links only `krmllib.h` (macros + typedefs), machine ints → `uint8_t`/`uint32_t`/…,
`Prims_string` → `const char *`, byte slice → `{uint32_t length; const char *data;}`, heap =
libc `malloc`/`free`, stack `push_frame` = plain C stack, **no GC anywhere**. The mechanism is
primitive *type mapping* (`[@@noextract_to "krml"] // primitive`), which is exactly Lean's
`@[extern]` idea applied to types. A real Lean equivalent = a new backend (`EmitNoGC`/`EmitCStar`
+ a representation/boxing pass + a driver flag) at the `EmitC`/`EmitLLVM` seam, i.e. a *compiler
backend*, not a `lake` library; the `@[extern]` fast path (shape 2) is the stopgap that lands
first.

**`WellFounded.fix` + an outer `match` on the input produces an unreducible two-arg
`match s, ih` — and the `ih` argument type fixes `s` to the scrutinee.** A `fix` body
written `(fun s ih => match s with | [] => … | b :: rest => … ih rest …)` elaborates to
`match s, ih with`, and `rw [WellFounded.fix_eq]` then `cases s` leaves `match [], …`
*not* reduced — the `ih`'s relation type mentions the match-scrutinee (`head✝ :: tail✝`), not
the outer `s`, so subsequent `simp`/`change`/`rfl` stall. Fixes that work: (a) avoid the outer
match entirely — write the `[]` base case as the *empty-list* branch of the recursion's own
list argument (as `decodeRepeat` does with ``([], s) :: …``); or (b) if the match is
authentic, pass the *scrutinee term* (`b :: rest`) — not the outer binder `s` — to the helper
so the `ih` type and helper's `s` parameter are syntactically the same term. Test the base
leaf (`some [] ≠ none`) with `unfold …; rw [WellFounded.fix_eq]; change some [] ≠ none; simp`
rather than `rfl`, because the negated/monadic goal does not reduce the `match` on its own.

**`List.mem_attach l a : a ∈ l.attach` takes the whole Subtype, not the proof.** To show
`⟨(x, s₁), hm⟩ ∈ l.attach`, write `List.mem_attach l ⟨(x, s₁), hm⟩` where the argument is the
`{ p // p ∈ l }` element; it is a *theorem* (not a constructor or iff), so do not project
`.2` off it. Conversely `List.mem_flatMap`/`List.mem_map`/`List.mem_filterMap` are **not**
`[simp]` — `rw` them explicitly when destructuring an `attach`-ed `flatMap`.

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

## 6. Lake build customization (`@[extern]` C FFI link, script lakefile)

**Linking hand-written C into a `lean_exe` needs a script `lakefile.lean`, not
TOML.** The TOML `[[lean_lib]]`/`[[lean_exe]]` DSL has no way to *compile* a
`.c` — `extern_lib` needs a custom `getPath` build that TOML cannot express. The
script form can declare a `target` that compiles the C to an object and add it
via `moreLinkObjs`:

```lean
import Lake
open Lake DSL
open System

package codec

target externFastPathO (pkg) : FilePath := do
  let oFile := pkg.buildDir / "ExternFastPath.o"
  let srcFile := pkg.dir / "Codec" / "ExternFastPath.c"
  buildLeanO oFile (Job.pure srcFile)

lean_exe bench where
  root := `Bench
  moreLinkObjs := #[externFastPathO]
```

Key facts, each a non-obvious gotcha:

- **`target x (pkg) : FilePath := …` names the package binder explicitly** — the
  default (no binder) is `_`, so `pkg.dir`/`pkg.buildDir` (the `Package` API, e.g.
  `Package.buildDir = dir / config.buildDir`) need `(pkg)`.
- **`buildLeanO`/`compileO` (in `Lake.Build.Common`/`Lake.Build.Actions`) are the
  compile step**; `buildLeanO` takes `leanIncludeDir?`/`lean.cc`/`ccFlags` from the
  Lean install, i.e. `leanc` with `-I …/include` (so `#include <lean/lean.h>` resolves)
  and the matching flags — reusing it reproduces exactly how Lake compiles its own
  generated `.c`. `buildO` is the raw `cc` variant (you supply `-I`/flags).
- **`Job.pure srcFile` (not a bare path) is the `buildLeanO` source argument**;
  `FilePath`/`String` are `OptDataKind` so `Job.pure` works, and the result of the
  `target` body is a `SpawnM (Job FilePath)` that lifts to `FetchM (Job FilePath)`
  (the `MonadLift SpawnM JobM` + `MonadLift JobM FetchM` chain) — no manual wrapping.
- **`@[default_target]` is how you set the bare-`lake build` target in a `.lean`
  lakefile.** The TOML `defaultTargets = ["x"]` key maps to **`LakefileConfig`**
  (a TOML-only config), *not* `PackageConfig` — so `package codec where defaultTargets
  := …` warns "unknown 'PackageConfig' field" and does nothing. Tag the target
  (`@[default_target] lean_lib codec`). `PackageConfig` does have a `defaultTargets`
  field, but the attribute is the maintained path.
- **`leanc` self-resolves its C compiler.** Running `leanc --print-cflags` / `leanc -c`
  works with a minimal `PATH` (it invokes the clang wrapper baked in from the stdenv that
  built `lean4`, so `cc`/`clang` need not be on `PATH`). This means a Nix `bench`
  derivation's `nativeBuildInputs = [ lean4 ]` suffices to compile the `.c` via
  `buildLeanO` at `lake build bench` time.
- **A flake/`default.nix` `src = ./.` uses the *git tree*, so untracked files are
  absent from the Nix build.** A `lakefile.lean` (or any new module) must be
  git-tracked before `nix build`/`flake` sees it; the failure is `lake` printing
  "no configuration file with a supported extension" for *both* `lakefile.lean` and
  `lakefile.toml`.

---

## 7. "Work faster": carrier swap > FFI > compiler (and lean on `USize`)

**Before authoring a compiler backend or `@[extern]` C, change the *result
carrier* — it is usually the whole lever and it needs no new trust.** The
"speedup" question has a strict cheaper-to-harder order, and the first two steps
are *type-level* moves inside Lean, `[propext, Quot.sound]`-only:

1. **Carrier swap.** The hot loop is almost never the cost; the cost is the
   `List UInt8` of boxed cons cells (and bignum `Nat` boxes) the API *returns*.
   Define a packed, `USize`-indexed, slice/span-returning surface
   (`decode … : … → Option (α × USize)`, full-consumption returning the packed
   buffer) instead of `… → List (α × Nat)`, and prove it equal to the `List`
   spec by the same refinement lemma you already write for the carrier swap.
   This removes the allocation that dominates the profile.
2. **Scalar indices — with the field-position caveat.** `USize` is a scalar in
   Lean's IR *only* in argument/return position of an `@[extern]`; bignum `Nat` is
   always an `lean_object *`, and `UInt64`/`UInt32` arithmetic is **also** boxed
   (`instAddUInt64` → `lean_object*`, no `uint64_t` in the emitted C — see the
   2026-10-18 entry). A function *indexed* by `USize` codegens the *index* to
   `size_t`, and so do `ByteArray.uget`/`uset` (→ `lean_byte_array_uget(..., size_t,
   uint8_t)`). **But** the moment that `USize` is *returned/stored* in a
   `Prod`/`Option` field it re-boxes (`lean_box_usize`), and `USize.toNat` at each
   boundary adds a bignum conversion — so a result-returning interpreter (`Option
   (α × USize)`) does **not** stay unboxed end-to-end. Rewriting a parser to thread
   a `USize` cursor made it *slower* for exactly this reason. **Net:** `USize`
   helps the *index-argument* and the *bit-vector ops in C seams*, not the *pure-Lean
   scalar computation*, which remains boxed regardless of which word type you write.
3. **`@[extern]` FFI** only *if* a stdlib primitive already exists to shim — and
   verify it actually adds anything; stdlib `ByteArray.get`/`size`/`push`/
   `copySlice` are already `@[extern]` C, so a hand-written wrapper over them is a
   no-op. (Measured lesson: a `@[extern]` "fast path" that only re-wraps stdlib
   externs gives no speedup and should be recorded as such, not as a win.)
4. **A compiler backend** is the *last* resort, and its "unboxed C" story is only
   sound for a *source* subset already written in scalars (`USize`/`UInt64`) and
   first order — never "erase `Nat`/`WellFounded.fix`", which is a semantic
   change the IR cannot express (`WellFounded.fix` threads a higher-order `ih`;
   it is backtracking search, not a tail loop).

**The rule:** measure *what actually costs* (usually the result allocation, not
 the byte loop) before choosing a layer; pick the cheapest layer that removes
 *that* cost; record the measured outcome honestly even when it is "no speedup".

---

## Append new learnings here

Date-stamped, one line each, latest first. Keep entries generic (no project
names/paths); the specific repo lives elsewhere.

- 2026-10-20 — **A plain `decide` on a *closed* structural-match equality is `[propext]`-only (definitional),
  `native_decide` leaks a `.native`/IO axiom — never use `native_decide` in a gate theorem.** If the goal
  is `someTailTerminalParser [literal, byte list] = none` where the parser is a `def` of `if`/`match` over
  `Bool`/`Nat` and the literals are concrete, `unfold <parser>; decide` closes it and `#print axioms` reports
  only `[propext]` (better than `[propext, Quot.sound]`). The existing "`decodeFull`/`Rel` have no `Decidable`"
  caveat applies to the *fixpoint* decoder, **not** to a hand-written structural `match` parser over `List
  UInt8`/concrete bytes.

- 2026-10-20 — **`l ++ []` is not `rfl`-equal to `l`; in an induction step that emits `chars ++ []` vs the
  lemma's `chars`, `rw [← List.append_nil chars]` first (it rewrites `chars` to `chars ++ []`).** A total
  char-emitter `chars : B → List UInt8` leaves the `full/tail` case goal as `parse (chars)`, while the helper
  lemma is stated as `parse (chars' ++ rest) = …`; for the `rest = []` base, `simpa`/`rw` do not see the `++ []`,
  so insert `rw [← List.append_nil <chars>]` to align, then `rw [helper … []]`. (`List.append_nil : l ++ [] =
  l`; the `←` direction is `l = l ++ []`.

- 2026-10-20 — **Make an illegal *run-level* shape impossible by replacing a homogeneous list type with a
  terminal-maker inductive.** A "blocks + at most one terminal tail" language whose value type is
  `List (List UInt8)` *admits* "tail-then-full" (`[[b],[b0,b1,b2]]`) by construction; no guard/filter/
  post-condition over that type is "perfect" because they all detect-and-discard an already-built illegal
  value. The fix is a value type whose *tail constructors have no continuation*: `inductive B where | nil
  | full (b0 b1 b2) (rest : B) | tail1 (b0) | tail2 (b0 b1)` — `tail1`/`tail2` are terminal, so "data after a
  tail" has no term, and the only way to write "a 1-byte then a 3-byte block" is `full 0 0 0 (tail1 x)` (the
  *valid* order). The decoder `Bytes/List UInt8 → Option B` is total and returns `none` exactly when no `B`
  term matches; every `some v` *is* canonical. Rejection is the *absence of an inhabitant*, not a filter.
  This is the honest "types dictate impossibility": the compiler rejects the illegal shape.

- 2026-10-20 — **A "flatten" from a two-part sum/product value to a plain list is usually *non-bijective*,
  so there is no flattening `Iso` — don't plan one.** "`full* (tail)?`" as `List Block × Option Tail` →
  `List Block` via `(bs, t) ↦ bs ++ t.toList` is NOT injective (a full-width `t` collides with it being the
  last *full* block of `bs` with `t = none`). If you need both shapes, keep the two-part value (or the
  terminal-tail inductive above) as the *proven* type and drop the flat list from the proven surface; a
  `List`-append that injects an `Option`/tag is a transport, not a law-bearing `Iso`.

- 2026-10-20 — **`open Codec` (or any `open`) makes bare lowercase constructor names parse as *pattern
  variables*, breaking `match`/`induction` arms.** After `open Codec`, `| empty => … | full b0 b1 b2 r => …`
  in a `def/inductive` over your own `inductive B` fails: `empty` resolves to `Codec.empty` (type mismatch)
  and `full`/`nil`/`tail1` are read as lowercase pattern *variables* ("invalid pattern … `B.full` would be
  valid"). Always qualify your own constructors (`B.full …`, `B.nil`) or use leading-dot notation (`.full`,
  `.nil`), and rename `empty` (→ `nil`) to dodge the `Codec.empty` clash entirely.

- 2026-10-20 — **Reuse an existing lenient block-decoder (with its per-shape identities) to build a strict
  structural parser, instead of re-deriving the digit/`if` math.** A strict whole-input parser over a
  terminal-tail inductive needs each block's `List bytes → Option (List bytes)` (1–N byte shape) and the
  per-shape `decode (encode bs) = some bs` facts; if a *lenient* block decoder plus `*_unapply_single/pair/
  triple/…` theorems already exist, write the strict parser as `match lenientDecode [c0..ck] with | some
  [b] => tail1 b | some [b0,b1] => tail2 b0 b1 | some [b0,b1,b2] => full … (recurse) | …`, and prove the
  per-shape lemmas with a single `simp [parser, charEmitters, theUnapplyLemma]` — no `by_cases`/`omega` digit
  re-derivation, no byte-identity reconstruction. The strictness is all in the *value type* + which patterns
  recurse, not in new digit proofs.
- 2026-10-20 — **`Codec.decodeFull` and `Rel d` have **no** `Decidable` instance, so concrete value-check
  vectors cannot close with `decide`/`by_decide` — only `native_decide`, which leaks a `.native` axiom and
  must stay out of gate theorems.** `decodeFull p h n s` recurses via `WellFounded.fix` and `Rel` is a
  structural `Prop` over the `Codec` AST, so `decide` on `decodeFull … = some […]` gets stuck at the
  `WaitFounded.fix`/`fix_eq` stage and `Rel …` fails to synthesize `Decidable`. The gate-clean (`[propext,
  Quot.sound]`-only) route is `decodeFull_spec` + `decodeRepeat_spec` + `relRepeat`/`relRepeat_cons` +
  `encode_rel`, where each *block*-level `Rel elem bs s` fact is obtained **from the encoder**
  (`encode_rel elem bs` gives `encode elem bs = some ⟨k, s⟩ → Rel elem bs s`, and `encode elem bs = some
  ⟨k, literal⟩` closes by `simp` because the block `Iso`'s `unapply` is a plain `match`, not a fixpoint).
  But `encode elem bs` itself does **not** `rfl`-reduce end-to-end: the inner `encode (count k (satisfy p))`
  leaves the `if p (single-bytes) …` conditions unfolded, and closing them needs `decide` on each concrete
  digit arithmetic (`valToX c = i`, `pred b = true`), which **does** `decide`-close (they are closed `Nat`/
  `Bool` equalities). Keep `native_decide` only in a **bench `example`/`#eval`** (not a proved theorem).

- 2026-10-20 — **The forward direction `Rel (count k (satisfy p)) l s` (from `s = byte-image of l` + `∀ b ∈ l, p b`)
  is a genuinely-needed lemma with a `splice`/`cast`/`(k+1)-1` index-cast gotcha: the succ case must walk down
  via `count (k+1) = iso cons (seq (satisfy p) (count k (satisfy p)))`, splitting `s` at `1`, and the tail is
  `Bytes ((k+1)-1)` which is **not** definitionally `Bytes k`** — so rather than `bdrop 1 s` (type-mismatch
  against the IH's `Bytes k`), define `s' : Bytes k := fun i => s ⟨i.val + 1, by omega⟩` and cast it into the
  `splice` suffix (`cast (congrArg Bytes (by omega : k = (k+1)-1)) s'`), proving the head via `Rel_satisfy`
  and the tail via the IH on `s'`.**  The splice equality `s = splice 1 (single b) (cast … s')` closes by
  `Bytes.ext` + `splice_apply` + `by_cases h : i.val < 1` (head) / `simp` + the image hypothesis (tail).  This
  `(k+1)-1 = k` (a `Nat.sub` reduction, **not** definitional) is the recurring gotcha behind every
  length-indexed `Bytes n` recursion step.

- 2026-10-20 — **`count k (satisfy p)` fixes the *consumed byte window* (`k`), NOT the decoded *value*
  length — so a cross-block (run-level) invariant is not expressible as a refinement of the element, it
  needs a run-level guard.**  A block codec `iso blockIso (count k (satisfy pred))` consumes exactly `k` bytes
  per element *regardless* of what the value is; padding/`=`-position affects the *value* (`1` vs `3` bytes),
  not the window. So an intra-block property (e.g. `=` in a non-terminal position *within* a `k`-char block) is
  correctly rejected by the block `Iso`'s backward law, but a *cross-block* property (e.g. "no data after a
  terminal `=`", i.e. a `=`-terminated block must be the *last* block) is **accepted** by `decodeRepeat`
  (grouping input into fixed `k`-wide blocks) and must be enforced by either (a) splitting the run into a
  full-block `decodeRepeat` prefix + an optional terminal **tail** block via `seq`/`alt`/`empty`, or (b) a
  whole-input post-condition theorem on `decodeFull` — **not** by a length argument (`"padded block has value
  length < k so it can't be followed by a full block"`), which is a *false premise*: the window, not the value
  length, is what `count k` fixes.

- 2026-10-20 — **Case-insensitivity is NOT expressible as a `Codec` value over a strict `Iso`.** A
  normalizing map (e.g. hex `A` and `a` → the same nibble) is **not a bijection** (two inputs → one output), so
  it cannot be an `Iso` field and it breaks `Unambiguous` (two distinct inputs relate to one value). If a format
  spec mandates case-insensitive *decoding* (RFC 4648 §8 for hex), that must live in a **separate
  case-normalizing facade** outside the `Codec` value — a `satisfy`+normalizing-`iso` `Codec` is a category
  error. Record a case-insensitive acceptance as a **non-goal** for the `Codec` value, not a test that the
  `Codec` "should" pass.

- 2026-10-20 — **When re-anchoring a plan to a rewritten surface, verify the *ground truth* of every "the code
  does X" claim before stating it as fact — a spec-driven plan that asserts "the decoder accepts lowercase /
  rejects trailing padding" against code that provably does the opposite will be caught by a reviewer and
  must be re-derived.** For `decodeFull`/`decodeRepeat`-based surfaces: the whole-input decoder is
  `decodeFull elem consumesByte n s : Option (List α)` (or `List (List α)` for a block element), **not** a
  bespoke `decode : List UInt8 → Option (List UInt8)` facade; and the block vs fixed-width split is element
  `Codec UInt8` (one byte) vs element `Codec (List UInt8)` (a multi-byte block). Write an explicit
  "ground truth the plan must respect" section with the verified signatures and the deterministic outcome of
  the contested case (`decodeFull … "Zg==AAAA" = some […]`), so reviewers re-check claims, not guess.

- 2026-10-19 — **A `Codec`-value rewrite of a *fixed-width* digit codec (one byte per element) is a
own template; a *block* codec that packs bits across bytes is NOT.**  The fixed-width recipe —
  element `Codec UInt8 := iso blockIso (count k (satisfy digitPred))` plus the repetition triple
  `decodeRepeat`/`encodeRepeat`/`relRepeat` — works because the block `Iso` (`k` digits ↔ one byte) is a
  clean bijection: both `law` directions close with `omega` on a per-digit `≤ bound` plus `Nat.div_add_mod`.
  A base-N codec whose digits *cross* byte boundaries (e.g. 40 bits = 8 five-bit chars → 5 bytes) has element
  `Codec (List UInt8)` and a block `Iso` whose **backward** law (`apply cs = bs → unapply bs = cs`) is
  *encode-injectivity*: recover each char `cᵢ = valToX (σᵢ(bs))` from the bytes.  The old bespoke code only
  proved `decode ∘ encode = id` (`decode (encode bs) = some bs`); it never proved `encode ∘ decode = id` on
  valid input, which is exactly the missing `Iso.law` direction.  Reuse the existing byte-extraction
  identities (`byte0..byte4`) *read in reverse* for the recover step, and a `char_eq_valToX_of_valid`
  lemma (`c = valToX i` when `valid c ∧ toVal c = i`).  Do **not** reach for `by_contra` (it needs
  `Classical.choice` and breaks the `[propext, Quot.sound]` gate): destruct each `char = pad` /
  `valid char` guard with `by_cases`, close the impossible branches with `simp at h` + `omega`.

- 2026-10-19 — **`Unambiguous (iso i d)` only needs `i.apply` to be *functional* (deterministic), not the
  full `Iso.law` — but `encode_rel`/`encodeRepeat_rel`'s `iso` case *does* need the **forward** `law`
  (`unapply x = some a → apply a = some x`).**  So `Unambiguous` of a `Codec.iso` leaf transfers for free from
  the inner `Unambiguous` (`some x = some y`, `Option.some.inj`) with no bijection proof, yet you still must
  construct the `Iso` with its full `law` field (both directions) before you can write the `Codec.iso`.
  The backward direction is the genuinely-new sharp edge for non-bijective-looking block maps.

- 2026-10-19 — **`Productive (count k (satisfy p))` holds only for `k ≥ 1`:** `count 0` relates the empty list
  to the empty string, so it is *not* productive (`Rel (count 0 …) xs s → n = 0`, not `n ≠ 0`).  State the
  generic `ConsumesByte` witness as `consumesByte_count_satisfy_succ p k : ConsumesByte (count (k+1)
  (satisfy p))` (via `Productive_count_satisfy_succ`), never the `k = 0`-inclusive form, and write each base's
  width as `k = m + 1` (`show 8 = 7 + 1 by rfl`) before applying it.

- 2026-10-19 — **Factor the generic per-base proof lemmas into one shared module and `open` it, rather than
  re-deriving them verbatim per base** — when a proof recipe repeats across N sibling modules, the generic
  lemmas (`Productive_iso`/`_seq_left`/`_count_succ`/`_satisfy`, `Unambiguous_satisfy`/`_iso`,
  `Rel_count_satisfy_len`, `count_satisfy_unambiguous`) are parameterized only by a byte predicate `p` and a
  width `k`, so they belong in a `Common` namespace.  A left-nested 8-way `&&` (`(… && d7) = true`) decomposes
  cleanly with `simpa only [Bool.and_eq_true_iff] using hv` into a *left-nested* `∧`, then `.1.1.1.…` /
  `.….2` — do **not** hand-nest `Bool.and_eq_true_iff.mp` (the `.1`/`.2` count is easy to get wrong).

- 2026-10-19 — **Proving a byte-substrate codec's *unambiguity* (`Unambiguous d := ∀ x y n s, Rel d x s →
  Rel d y s → x = y`) is the linchpin that gates the inherited repetition-level roundtrip**
  (`decodeFull_spec` needs `huniq : (x, Suffix.empty n) ∈ decodeRepeat … → (y, …) ∈ … → x = y`). The
  working chain for a fixed-width `iso blockIso (count k (satisfy p))` leaf is: (1) `Rel (count k (satisfy p)) xs s`
  **pins the byte length** `n = k` (prove `Rel_count_len` by induction on `k`: the `satisfy` RHS gives
  `∃ h : m = 1`, `subst` it, then IH on the tail `s₂ : Bytes (n - 1)` gives `n - 1 = k`, close with `omega`);
  (2) `count k (satisfy p)` is unambiguous by induction on `k`, where the succ case peels the head byte via
  `splice_prefix_read` at index `0` and recovers the equal tails via `bdrop_splice`, then the IH on the
  (same-type) tails; (3) `iso` preserves unambiguity (`i.apply a = some x` twice, `a = a'` by the inner
  unambiguity, force `x = y` with `Option.some.inj`).

- 2026-10-19 — **There is **no `norm_num`** in a stdlib-only (no-mathlib) Lean library** — `norm_num` is an
  "unknown tactic" (the AGENTS rule lists it among `ring`/`nlinarith`/`fin_cases`/`interval_cases` as absent).
  Close `Fin`-index arithmetic goals with `omega`/`simp`/`decide` only.

- 2026-10-19 — **`Fin.val` of an anonymous `Fin` literal does **not** reduce for `omega`/`norm_num`/`decide`:**
  the goal `↑⟨0, h0lt⟩ < 1` (from a `splice_prefix_read p … ⟨0, h0lt⟩ hi` call, where `hi : i.val < m` must be
  supplied) sticks — `omega` reports a counterexample on the opaque atom `↑↑⟨0, h0lt⟩`, `decide` rejects the
  free variable, and `norm_num` doesn't exist. The fix is **`by simp`** as the `hi` argument (and for the
  `Fin n` well-formedness use a *named* `have h0lt : 0 < n := by omega` first), because `simp` reduces
  `Fin.val ⟨0, _⟩` to `0` and closes `0 < 1`. Never leave `by norm_num`/`by omega`/`by decide` for such a goal.

- 2026-10-19 — **Use `splice_prefix_read … ⟨0, hlt⟩ hi` to extract the head byte of a `splice`-split prefix,
  and `bdrop_splice …` to recover the tail as the *same type* `Bytes (n - m)`** — when two `Rel`/`relRepeat`
  witnesses both split the same `s` at the (productivity-pinned) length `m`, `s₁x = s₁y` follows by `Bytes.ext`
  (read each `i : Fin m` through `splice_prefix_read` twice and `trans`), and `s₂x = s₂y` by `rw [← bdrop_splice
  … s₁x s₂x, ← bdrop_splice … s₁y s₂y]` then `congr 1` on the `s` equalities. This is the transport that makes
  an IH applicable over the *tails*.

- 2026-10-19 — **`subst` on a length-equal witness (`hm0 : m = 0`) that contradicts an earlier
  `have hlen : m = 3` hits "No goals to be solved"** — don't `subst` a length to a value that
  contradicts another surviving witness. Instead keep both equalities as `have`s and close the
  contradiction with a single final `omega` (`have hlen : m = 3 := …; have hm0 : m = 0 := by omega;
  omega`). This is the relRepeat-`nil`-vs-`cons` productivity asymmetry case.

- 2026-10-19 — **`relRepeat` (the least-fixpoint list relation) is unambiguous for a productive
  `ConsumesByte` step by *list induction with `generalizing b n s`*, cased on `b` inside the cons case** —
  `rw [relRepeat_cons] at hb` does **not** fire when `hb`'s subject is still the variable `b`; you must
  `cases b` (→ `nil` / `cons y ys`) first so `relRepeat_cons` matches the `y :: ys` subject. The `nil`-vs-`cons`
  asymmetry closes by productivity (`Rel octElem _ s₁` forces `m = 3`, but `m ≤ n = 0` forces `m = 0`;
  `omega` on `m = 3` + `m = 0`).

- 2026-10-19 — **The inherited repetition roundtrip law** (`decodeFull (encodeRepeat …) = some bs`) **chains**
  `encodeRepeat_rel` (encoder → `relRepeat` witness) → `decodeRepeat_spec` `.2` (`relRepeat` witness →
  `(bs, Suffix.empty n) ∈ decodeRepeat …`, using `cast (congrArg Bytes (Nat.sub_zero n).symm) s` +
  `prepend_empty_eq` + `relRepeat_cast`) → `decodeFull_spec` `.2` (membership → `some bs`, gated by the
  `huniq` uniqueness fact above). The `huniq` itself is proved via `decodeRepeat_spec` `.1` twice +
  `prepend_prefix_eq` (to pin the two prefix witnesses `s₀x = s₀y` from the shared `t = (Suffix.empty n).prepend s₀`)
  + the list-level unambiguity.

- 2026-10-19 — **Define `Iso` `apply`/`unapply` as *named total functions* and prove `law` as a *separate
  theorem* (`octBlockIso_law : octBlockApply cs = some b ↔ octBlockUnapply b = some cs`), then pack with
  `{ apply := …, unapply := …, law := … }` — do **not** write the `law` field inline.** An inline `law := by
  …` over a `match cs with | [d0,d1,d2] => …` list-literal pattern fights `simp [isoName]`/`dsimp`
  ("invalid argument: variable `isoName` is not a proposition") because the `structure`'s `law` field is not
  a reducible `simp` target, and `split at h` on the list-literal assigns *surprising* variable names
  (`d1 d0 rest` from `[d0,d1,d2]`). Named functions let you `unfold octBlockApply`/`rw [octBlockApply]` on a
  *plain `def`* and `cases cs`-destructure the list yourself with predictable names.

- 2026-10-19 — **`Nat.div_add_mod m n` returns `n * (m / n) + m % n = m` — the *divisor first*.**
  To get the `(m/n) * n + m%n = m` form a digit-sum identity needs, `simpa [Nat.mul_comm] using
  Nat.div_add_mod m n`.  `omega` does *not* commute it for you, and an `omega`-only digit reconstruction
  (`(v/64)*64 + ((v/8)%8)*8 + v%8 = v`) closes with just `have h1 := Nat.div_add_mod v 64; have h2 :=
  Nat.div_add_mod v 8; omega` — but **only** when the divisor-first form is in the local context; `omega`
  alone does not unfold `(v/8) % 8`.

- 2026-10-19 — **`decide` lemmas:** the iff is `decide_eq_true_eq : (decide p = true) = p`; the one-direction
  forward is `of_decide_eq_true : decide p = true → p`; there is **no** `decide_eq_false_eq` (the mirror is
  `decide_eq_false : ¬ p → decide p = false` / `of_decide_eq_false`).  For a *left-associative* `&&` chain
  `(P && Q && R) = true`, decompose with `(Bool.and_eq_true_iff.mp hv).1 : (P && Q) = true` then
  `(Bool.and_eq_true_iff.mp that).1 : P = true` / `.2 : Q = true`, and `(Bool.and_eq_true_iff.mp hv).2 : R =
  true` — `hv.1`/`hv.2.2` on a `Bool` equality is an "invalid projection" (a `Bool` equality has no fields).
  Close a `(true && true && true) = true` residual (the `if (b : Bool)` desugars to `if b = true`) with
  `have hh : (true && true && true) = true := by decide; rw [hh]` — `simp`/`#reduce` do **not** reduce `=
  true` on its own.

- 2026-10-19 — **`by_contra` needs `Classical` (or a `[Decidable]`/`Fintype` instance).**  In a
  stdlib-only, `[propext, Quot.sound]`-only library (`no mathlib`, no `Classical.choice`), `by_contra` is
  **not** available; proving `octToVal e ≤ 7 ⇒ 48 ≤ e` from `octValid e = true` must be done with `by_cases
  hle : e ≤ 55 <;> by_cases hge : 48 ≤ e` and `omega` in each branch (the invalid branches yield
  `octToVal e = 8`, contradicting `≤ 7`).  Do not reach for `by_contra`/`classical` in such a library — it
  breaks the axiom gate.

- 2026-10-19 — **A digit-decomposition *uniqueness* lemma (`d0·64 + d1·8 + d2 = e0·64 + e1·8 + e2`, each ≤ 7
  ⇒ triples equal) closes with `congrArg (fun x => x / 64) h` and `congrArg (fun x => (x % 64) / 8) h`**, not
  raw `omega` on `/`/`%`.  After `have hm := congrArg (fun x => x / 64) h`, give `omega` the *bound*
  `have hbc : b * 8 + c < 64 := by omega` (so the `b*8+c` tail is `< 64`, hence `(a*64 + b*8+c)/64 = a`),
  then `rw [hm', hm''] at hm; exact hm` — `omega` proves `(a*64 + b*8 + c) / 64 = a` **given** the tail
  `< 64` bound, but the `%64 / 8` step additionally needs `c < 8` so that `(b*8+c) % 64 = b*8+c` and
  `(b*8+c)/8 = b`.

- 2026-10-19 — **A recursive inductive AST (`Codec α`) *cannot* carry a constructor whose field is a
  *semantic* predicate over that same AST's own denotation** — `many : (p : Codec α) → Productive p →
  Codec (List α)` with `Productive p := ∀ x n s, Rel p x s → n ≠ 0` forms the definition-order cycle
  `Codec.many → Productive → Rel → Codec`, and Lean rejects both escapes: (a) a mixed `mutual` block
  (`inductive Codec` + `def Rel` + `def Productive`) is illegal — *"invalid mutual block: either all …
  inductive/structure … or all … definitions"*; (b) `mutual inductive Codec + Rel` is illegal on
  *universe* — *"resulting type `Prop` differs from `Type 1`"* — and this is irreparable, because
  `Rel : … → Prop` is pinned at `Sort 0` (`Prop`) while `Codec : Type → Type 1` is pinned at `Sort 1`.
  Consequence: **unbounded `many` must stay a *derived* combinator outside the AST** (its denotation is
  the least-fixpoint `relRepeat`/`decodeRepeat`/`encodeRepeat` triple, each carrying `ConsumesByte p`),
  never a `Codec` constructor — do not propose adding `many` (or any other than `byte`/`satisfy`) to a
  byte-substrate `Codec` and do not budget for converting every `induction d` law to `Codec.rec`.

- 2026-10-19 — **The paper's `many` (Rendel–Ostermann §3.4) is a *derived* combinator
  `many p = nil $ pure () | cons $ p ∗ many p`, and the F* reference has *no* `many` combinator at all —
  its unbounded-run primitive is `satisfy_many0`/`satisfy_many1` (aliases `many0`/`many1`), a
  `let rec satisfy_run_scan f bs` that scans a maximal leading run of the *finite* input byte list, one
  byte per step; no `Productive`/`ConsumesByte` witness is needed because the recursion is over the finite
  input, not over an arbitrary `p`'s denotation.**  So a byte-substrate codec's *variable-width run* is
  `takeWhile p := many (satisfy p)` realized over the productive repetition triple — exactly the landed
  `relTakeWhile`/`decodeTakeWhile`/`encodeTakeWhile` — and fixed-width base-N blocks are `count k (satisfy
  p)` + a grouping `iso`.  This is the authoritative resolution when someone asks "add `many` to the AST".

- 2026-10-19 — **`simp [F, hv] at hdec` *consumes* `hv`** — if `hv : (P && Q && R) = true` is a `simp`
  argument while simplifying `hdec`, the rewrite unfolds `hv`'s `&&` chain and leaves `hv : True`, so a
  later `have hi : P = true := by simp [hv] at *; assumption` fails.  Extract each conjunct **first**
  (`have hP : P = true := …; simp [Bool.and_eq_true] at hv; exact hv.1`, then `.2` for the rest), **before**
  the `simp` that *uses* `hv` as a rewrite.  Same failure mode for `by_cases hv : cond` followed by
  `simp [body, hv] at h`: the `by_cases`-introduced `hv` is the very hypothesis `simp` rewrites away.

- 2026-10-19 — **A partial-`Iso`'s `law` for a fixed-`k` digit↔byte grouping needs *two* directions the
  forward-only `roundtrip` never stated: the converse bijection `valToX (xToVal e) = e` for *valid* `e`,
  and a digit-decomposition *uniqueness* lemma** (`d0·64+d1·8+d2 = b`, each `di ≤ 7`, ⇒ `di = b/…`) —
  proved with plain `omega` once the per-digit bounds are in scope (integers `di ∈ [0,7]` force
  `b % 8`, `(b / 8) % 8`, `b / 64`), but only after `omega` is given the bounds as separate `have`s; the
  nested `%`/`/` in `(b / 8) % 8 * 8 + b % 8 = b` needs `Nat.div_add_mod b 8` and `Nat.div_add_mod (b / 8) 8`
  as hypotheses — `omega` alone does not unfold `(b/8) % 8`.

- 2026-10-19 — **`UInt8.toNat_inj` is an `iff` (`a.toNat = b.toNat ↔ a = b`), not a function — `apply
  UInt8.toNat_inj` fails "function expected" — and `UInt8.ofNat_toNat` is a *closed* proposition
  (`UInt8.ofNat x.toNat = x`) that `exact UInt8.ofNat_toNat c` also rejects ("function expected … applied
  to c").**  To lift `toByte n = b` (`toByte n := UInt8.ofNat n`) to `n = b.toNat`, use
  `have hb' := congrArg UInt8.toNat hb; simpa [toByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt] using hb'`
  with `hlt : n < 256`; to close `toByte x.toNat = x` use `by simp [toByte]` (which folds
  `UInt8.ofNat_toNat` internally) rather than naming the theorem.

- 2026-10-18 — **Adding a predicate-guarded byte token (`satisfy : (A → Bool) → Codec A`, decoding
  "first element iff `p` it") to an inductive AST that is exhaustively `match d`ed in `Rel`/`decode`/
  `decodeFast`/`encode` (and every packed/committed mirror) means *every* match gains a case, and the
  `satisfy` proofs mirror `byte` with one extra conjunct.** Two gotchas: (1) the `¬p` decode branch
  (`by_cases hp : p (s ⟨0, ·⟩)` ) reduces `decode (satisfy p) s` to `[]`, so the `decode_spec`-style
  bidirectional law must prove `¬ Rel (satisfy p) x s₀` by contradiction — `Rel` in the `satisfy` case is
  `p x = true ∧ ∃ h : n = 1, h ▸ s₀ = single x`; extract `p x = true`, then reconstruct `x = s ⟨0, hnpos⟩`
  from the prefix `s = r.prepend s₀` via `prepend_prefix_read r s₀ ⟨0, hnpos⟩ hlt` (not `rw [hs] at hb`,
  which fails because the goal is a *subexpression* equality, not a whole-buffer occurrence), and close with
  `exact False.elim (hp hpx')` — `exact hp hpx` fails when the residual goal is still a membership `(x,r)∈[]`,
  not a bare `False`. (2) when an earlier `rw [decode]` already unfolded the scrutinee in the goal, a later
  `rw [decode]`/`rw [hdec]` does **not** match; instead `have hdec : decode … = [] := by simp [decode, hn, hp]`
  as a *separate* goal, then `rw [hdec]` — the `decode` in `hdec`'s proof is a fresh definition, the one in the
  goal is already unfolded. (3) for the `p x = true` forward half and the packed/`decodeArray`/`decodeOne`
  refinement, the predicate on the first byte is `p a[0 + i]` after `bdrop i (·) ⟨0, ·⟩` unfolds — `simpa`
  bridges `p a[i]` (the packed decoder's spelling) to `p a[0 + i]` (the spec `bdrop` spelling).

- 2026-10-18 — **The extensibility primitive of a byte-substrate codec (an inductive `Codec α` over
  `Bytes n := Fin n → UInt8`) is `satisfy : (UInt8 → Bool) → Codec UInt8` (the byte-token-with-guard),
  and variable-length / multibyte / self-delimiting tokens are a *run* over it (`takeWhile p` = the
  maximal prefix with `p b`), not a lookahead or per-byte-dispatch constructor.** A single-byte
  `satisfy` cannot recognize a varint (LEB128: consume until the high bit clears) or a UTF-8 symbol
  (1–4 contextual bytes) — and it must not try: the run (`many (satisfy p)` / `decRepeat`/
  `encodeRepeat` over `satisfy`) plus a downstream `iso` that folds the run's bytes is what decodes a
  varint (`takeWhile highBitSet` + fold 7-bit groups), a UTF-8 code unit, a base-N alphabet, or a JSON
  string body. Keep the description AST *closed and dumb* (`byte`, `satisfy`, and the combinators `seq`/
  `alt`/`count`/`iso`); express every concrete format as a `Codec α` value so `decode base64` and
  `decode json` are literally the same `Codec.decode` call — only the codec changes. Do NOT add
  BE/LE/fixed-width/`varint`/`text`/tagged-`sum`/lookahead constructors to the core AST: those are
  *derived* compositions (`count k byte` + an endianness `iso`) living in downstream packages.

- 2026-10-18 — **"every format is a `Codec α` value" breaks down for *variable-length* formats:
  a finite `Codec` describes exactly one *fixed-shape* value, and the only `Codec (List α)`
  producers are `count n p` (exactly `n`) and `manyUpTo n p` (at most `n`) — both *bounded*.**
  There is no unbounded-`many` constructor (`Codec` = `iso | seq | alt | empty | pure | byte |
  satisfy`), because `decode` is a **total function** `List (α × Suffix n)`, not the paper's
  relation: a `many : Codec α → Codec (List α)` node is non-total for an empty-matching step
  (`many (pure ())` on `[]`), so repetition was deliberately pushed out of the AST into the
  `decodeRepeat`/`encodeRepeat`/`relRepeat` **triple** (each carrying a `ConsumesByte p`
  productivity witness; `takeWhile p` is the worked example). Consequence: a *whole-list*
  variable-length codec (`base16/base32/base64 : Codec (List UInt8)` over an arbitrary byte list)
  **cannot be a single finite `Codec` value** — `count 2 (satisfy isHex)` ≫ pair-iso gives one
  *byte*, not a list of them. The honest shapes are (a) a `Codec UInt8`/`Codec (List UInt8)` *leaf/block*
  value + a whole-list triple at the repetition layer, or (b) adding an indexed `many`
  constructor carrying `ConsumesByte p` — which means re-deriving every law over a
  productivity-indexed AST (a core change, not a downstream-composition change). Don't
  promise "`decode base64 == decode json == Codec.decode`" for the *whole-list* case until the
  repetition layer can be a named value; for now only the *per-byte / per-block* leaf is a `Codec`.

- 2026-10-18 — **Inject a Lake dependency into a Nix flake as a *local path* dependency so the
  sandboxed `lake build` never `git clone`s it: rewrite `require foo from git "…"` → `require foo from
  "./foo-src"` (path form resolves directly, no git/network) and `cp -r` the dependency source into the
  build dir first — a flake input's `.outPath` is a *read-only* store snapshot, and Lake writes its `.lake`
  into the package dir, so without the copy you hit `permission denied (error code: 13) … .lake`. The
  dependency's own `lake-manifest.json` is gitignored (`No copy is made of local dependencies`), so Lake
  builds the dep from source in place — no pre-built `.olean` needed. (`substituteInPlace` in the buildPhase
  does the `require` rewrite; the source path is relative to the requiring package's dir.)
- 2026-10-18 — **A *private* GitHub repo as a `github:` flake input is fetched *purely* by a token, never
  `--impure`.** Anonymous fetch of a private `github:owner/repo` 404s (GitHub hides private repos from the
  API/archive endpoints), while `git clone https://github.com/owner/repo` succeeds *only* via the macOS
  `osxkeychain` credential helper — that success is a misdirection, not proof the repo is public. The correct
  fix is `access-tokens = github.com=<token>` in `nix.conf` (or `nix --extra-access-tokens
  "github.com=$(gh auth token)" …`): the shorthand fetches the private repo with no `--impure` and no
  `path:` workaround. `git+https://…`/`git+ssh://…` are not the answer — the former still needs the keychain
  (impure), the latter needs an SSH key that may not exist.

- 2026-10-18 — **A *block-structured* encoder/decoder (fixed `k`-element blocks + variable-width
  padding tails, e.g. base32/64 with 5/3-byte blocks and 1/2/3/4-byte pad cases) cannot use plain
  `List` structural induction — its `ih` is on the *immediate* cons tail while the block recursion
  skips `k` elements. Use strong induction on the length: `Nat.strongRecOn bs.length (motive := fun n =>
  ∀ ys, ys.length = n → …roundtrip ys…) (fun n ih ys hlen => …)`, giving `ih : ∀ m < n, motive m`; then after
  `rw [decodeN_block b b₁ … bₖ₋₁ … rest]`, recurse with `ih rest.length hlen' rest rfl` where the length
  shrink `hlen' : rest.length < n` is obtained by `rw [hlen] at (a have that rest.length < (cons…).length
  proved with `simp only [List.length_cons]; omega`)** — `omega` alone cannot unfold `(x :: …).length`.**
  The same shape mirrors at the `UInt8` surface: re-derive the strong induction there (don't transport it).
- 2026-10-18 — **`unfold decodeN` on a block-equal goal unfolds the *RHS* recursive `decodeN` too,
  leaving a non-definitional residual; the fix is a standalone equational lemma `decodeN_consK (c₀ … cₖ₋₁)
  (rest) : decodeN (c₀ :: … :: cₖ₋₁ :: rest) = <the `if`/`match` body>` proved by `rfl`, and `rw
  [decodeN_consK]` to reduce only the LHS `k`-cons scrutinee.**  (Base64 `k=4`, base32 `k=8`.)  The
  `++` in `encodeN [b₀..bₖ₋₁] ++ encodeN rest` must first become a syntactic cons chain via `show … ++ …
  = …` + `simp only [List.cons_append, List.nil_append]` (or `List.append_nil` for the `rest = []` whole-block
  case) before `rw [decodeN_consK]` finds the scrutinee.
- 2026-10-18 — **Order `rw` chains so each byte-extraction fact fires only after the vector it
  reconstructs is fully reduced to its encode-form.** A 5-char-to-byte fact like `((vₐ%r)·s + v/q) % r'·… + … = b₃`
  mentions `v₅`/`v₆` (the last two alphabet values), so you must `rw [valToX_valid v₅ h₅]`, `rw
  [xToVal_valToX v₅ h₅]` (and the same for `v₆`) to turn them into their encode-form *before* `rw
  [hb₃]`; otherwise `rw` reports "did not find an occurrence" because the target still spells those
  sub-terms as the un-reduced alphabet values. Similarly, end each block lemma with a trailing `simp`
  (or `decide`) — not `rfl` — because the decoder's `if` guards leave `decide False || …`/`¬True` `&&`
  residue that `rfl` won't reduce but `simp`'s `Bool.not_true/false`/`Bool.false_and`/`decide_false` will.

- 2026-10-18 — **`UInt8` is `%256`-truncating in *both* directions, and the clean `Nat`↔`UInt8`
  bridge is `UInt8.toNat_lt` (`n.toNat < 2^8`), `UInt8.ofNat_toNat` (`UInt8.ofNat x.toNat = x`),
  and `UInt8.toNat_ofNat'` (`(UInt8.ofNat n).toNat = n % 2^8`) — NOT `UInt8.toNat_ofNat`, which is
  only for the `OfNat.ofNat` spelling.**  When a byte-level codec's alphabet is ASCII `< 256`, make
  the truncation vanish explicitly with `Nat.mod_eq_of_lt` (`rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]`
  where `h : c < 256`), so the `% 256` never leaks into the arithmetic goals.  `UInt8.ofNat` unfolds to
  `{ toBitVec := BitVec.ofNat 8 n }`, not `OfNat.ofNat n`, which is why the `'`-primed lemma is the one
  that matches a `def toByte n := UInt8.ofNat n` surface.
- 2026-10-18 — **`omega` does NOT expand `if`/`ite` branches, and a stdlib-only project (no mathlib)
  has no `norm_num`/`nlinarith`/`ring`/`fin_cases`/`interval_cases` — so finite-alphabet bijections and
  closed-range arithmetic must be proved by `by_cases` on each range + `simp only […, ite_true,
  ite_false]` + `omega`, never by letting `omega`/`simp` reduce a nested `if` chain on its own.**
  Three concrete patterns for a `valToX`/`xToVal` bijection over a 4-range alphabet: (a) per-range
  `by_cases` with the char as a single arithmetic expression (`65 + i`, `71 + i` instead of `97 + i - 26`),
  then `simp only [h, ite_true, ite_false]` + `omega`; (b) a "never the sentinel" fact (`isPad (valToX i)
  = false`) closes with `exact decide_eq_false_iff_not.mpr (by omega)` after the same `by_cases` (the
  `Bool`/`decide` goal is a Prop-negation in disguise); (c) a final finite tail (`i = k ∨ i = k+1` from
  `¬ i ≤ k-1` and `i ≤ 63`) closes with `rcases (show i = k ∨ i = k+1 by omega) with rfl | rfl <;> decide`.
  `decide` is `[propext, Quot.sound]`-safe on closed `Decidable` goals; `native_decide` is NOT (it leaks
  `Lean.ofReduceBool`).
- 2026-10-18 — **A power-of-two bit/quartet-sum identity (`Σ (v / 2^k % r) * 2^k = v` for `v < 256`)
  is `omega`-provable — but only after `simp only [Nat.reducePow, Nat.reduceSub]` turns the symbolic
  `2^(7-i)` into a concrete `128`/`64`/…**  With `bitAt v i := (v / 2^(7-i)) % 2`, `omega` alone leaves
  `2^(7-i)` as exponentiation and fails; `simp only [Nat.reducePow, Nat.reduceSub]` (evaluating `2^(7-0)`,
  `2^(7-1)`, … to literals) then `omega` closes it.  The bound `v < 256` is load-bearing (makes each
  `v/2^k % 2` the actual bit); `omega` needs it stated via `have : v < 256 := …`/`UInt8.toNat_lt`.
  Same pattern for radix-4 (`(v / 4^(3-i)) % 4`).
- 2026-10-18 — **A `roundtrip` proved over a `Nat`-level core (`encodeN`/`decodeN : List Nat → …`)
  lifts to a `UInt8` surface by *re-deriving* the induction with `toNat`/`ofNat` transparency at each
  step, not by a separate transport lemma — and `simp [encode, decode]` on the `UInt8` surface
  over-splits the decoder's `&&`/`if` into `true = true ∧ …` residue that obscures the `rw` target.**
  Write the `UInt8` decoder with a single `if cond₁ && cond₂ then …` (not nested `if cond₁ then if cond₂`),
  and drive the roundtrip with `rw`-chains (`toByte_valTo*`, `valTo*_valid`, `*ToVal_valTo*`, the digit-sum
  equality) rather than a big `simp`, finishing with one `omega`/`simp` on the reduced arithmetic.
  is proved cleanly via the *pointwise* genuine-suffix invariant (`decode_genuine_suffix_pointwise`),
  not the `bdrop`-form: read each side at one `Fin` index, unpack one `bdrop`, `congr 1; apply Fin.ext;
  dsimp; omega`, with `t.consumed = n - t.remaining` making equal `remaining` give equal `consumed`.**
  The tempting `bdrop_consumedAbs_eq` route instead rewrites the consumed count into a lemma whose
  *other* hypothesis (`consumedAbs_remaining`-style, `a.size - consumedAbs = remaining`) is *dependent*
  on that count — `rw [hc] at E` then fails "motive is not type correct" because the count appears both
  in the `bdrop` index and inside the `congrArg Bytes` of the cast. Avoid rewriting a `Nat` into a term
  that mentions a dependent-equality hypothesis over that same `Nat`; reach for the pointwise invariant and
  close the one remaining `Fin`-index equality (a proof-irrelevance + `omega` step) instead.
- 2026-10-18 — **To turn "`t.prepend s₀₁ = t.prepend s₀₂`" into `s₀₁ = s₀₂` (injectivity of a
  length-indexed `splice`/`prepend` in its *prefix*), state and use three lemmas, not `simp`:**
  `splice_prefix_read (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n-m)) (i : Fin n) (hi : i.val < m) :
  splice hm s₁ s₂ i = s₁ ⟨i.val, hi⟩` (unfold `splice_apply` → `concat` → `rw [cast_fin_symm (e := splice_add hm)]`
  → `dsimp` → `simp [hi]`); `prepend_prefix_read` (the same at `Suffix.prepend`, the prefix is `s₀` and `hi :
  i.val < n - t.remaining`); and `prepend_prefix_eq t s₀₁ s₀₂ : t.prepend s₀₁ = t.prepend s₀₂ → s₀₁ = s₀₂`
  (apply `Bytes.ext; intro i`, `congrFun` the equality at `⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n t.remaining)⟩`,
  then two `rw [prepend_prefix_read … i.isLt]`). The *same-type* `prepend_prefix_eq` is the cast-free half:
  first prove `t₁ = t₂` (via `Suffix.ext` + the pointwise invariant) so `subst t₁` makes `s₀₁`/`s₀₂` share one
  type, then this lemma closes with no cross-length cast.
- 2026-10-18 — **An `@[extern]` trust seam whose Lean body is an `Array.extract`+`append` *composition*
  is NOT a window replacement on out-of-range inputs: `extract 0 off ++ src.extract s (s+len) ++
  dst.extract (off+len) n` yields *variable-length* results (appends `src` past `n` when `off > n`, drops
  bytes when `src` is short), while the C `memcpy`-into-full-`dst` returns exactly `n` bytes.** The two match
  only in-range; the body and the C drifted silently because the bench value-check exercised only mid-buffer
  inputs. Fix the *body* to the clamped full-`dst` semantics (`dc := min off n`, `sc := min srcOff slen`,
  `lc := min len (min (n-dc) (slen-sc))`, result `dst[0,dc) ++ src[sc,sc+lc) ++ dst[dc+lc,n)`), which is `rfl`-spec-able
  *and* matches a single-`memcpy` C; make the C's clamps **overflow-stable** (`copyLen > n - dstOff`, not
  `dstOff + copyLen > n`, since the Lean `Nat` never wraps but `size_t` can). Always add an out-of-range
  boundary value-check (empty source, `off` at/past end, `len` past end, `len = 0`) — it is the only check that
  catches a wrong clamp; a mid-buffer lane cannot.
- 2026-10-18 — **Proving a monotonicity/bound law for a definition is *not* interchangeable with the
  "never overruns" bound you might want: an unconditional `decodeArray … → i ≤ c` (cursor never moves
  backward) is provable, but `c ≤ a.size` needs a `i ≤ a.size` precondition, because `pure x` returns
  `(x, i)` for *any* `i` (a cursor already past the end is a legal result).** Before "fixing" a docstring that
  overclaims a bound, check the *base constructors* (`pure`/`empty`) for the counterexample; the honest fix is
  either to reword to the proved fact or to state the bound *with* the precondition and document why it is
  load-bearing (it is not a style choice — the unconditional form is false).

- 2026-10-18 — **Pure-Lean *parsing* (not just bulk codecs) has a hard ~20-40x-off-C ceiling,
  and it is a *toolchain* limit, not a code-quality one: `Nat`/`UInt8`/`UInt64` all box, and
  `USize` only unboxes as an `@[extern]` *argument*, never as a `Prod`/`Option` *field*.**
  Chasing a "very fast" RFC 3339 timestamp parser, three independent confirmations: (a) IR shows
  `acc*10+digit` lowers to `lean_nat_mul`/`lean_nat_add`/`lean_nat_sub` (bignum `lean_object*` calls) and
  byte loads to `lean_uint8_to_nat`; (b) a pure-Lean `sum64` `while` loop over `UInt64` lowers to
  `instAddUInt64`/`instMulUInt64`/`instLTUInt64` (boxed `lean_object*`) with **no** `uint64_t` anywhere;
  (c) rewriting the parser to a `USize` cursor made it *slower* (~206→~440 ns) because `baGetU`'s
  `off.toNat < a.size` does a `USize→Nat` bignum conversion + `get_elem_tactic` proof per read and the
  `USize` field re-boxes (`lean_box_usize`). There is **no** pure-Lean escape: `@[implemented_by]`/
  `@[csimp]` still emit through the same boxed LCNF→EmitC pipeline; `native_decide`/`bv_decide` are
  `Prop`-reflection, not runtime `Nat` arithmetic. **Corrects §7 point 2** — "type it `USize` in source
  and get unboxed indices" is true only for an `@[extern]` *argument*, false once the value is *returned*
  in a product/option; a result-returning interpreter cannot stay unboxed this way. The honest end-state:
  pure-Lean codecs (~20-40x C) are the *spec*; the only C-speed regions are the generic bulk `memcpy`/
  `memchr` seams, and real speed (TLS crypto etc.) is FFI'd, not Lean. Do not chase further pure-Lean
  parsing micro-optimizations hoping to close this gap — it is the compiler backend's boxed scalar,
  not the code shape.
- 2026-10-18 — **Benchmark numbers here are noisy by ±2x with machine load/thermal; cross-check
  against a `calib memcpy`/`memchr` baseline before believing any single `[measured]` figure, and do
  not micro-optimize against an unstable baseline.** A `calib memcpy` lane measured 66↔300 ns across
  runs on the *same* binary (load average ~2.4), and a committed "302→206 ns improvement" was later
  revealed to be largely that noise (the reverted code re-measured 412 ns). Corollaries: (1) take the
  *best-of-N* or check `uptime`/load before comparing two versions; (2) a "regression" vs "win" verdict
  needs the noisy baseline measured in the *same* window, not recalled from an earlier session; (3) record
  the baseline value *in the result line*, never report a bare ns/op that the reader can't sanity-check.
- 2026-10-18 — **A `ByteArray`-vs-C comparison against a semantic parser must be apples-to-apples;
  C `strptime`/`date`-style parsing is ~10 ns/op on a 23-byte record, vs ~200-400 ns for the boxed
  pure-Lean equivalent.** When someone asks "can Lean parse as fast as C", the concrete answer is a
  head-to-head: a hand-written `clang -O2` RFC 3339 parser (uint32 registers, no alloc) is ~10 ns/op,
  and no pure-Lean reshaping gets under ~20x that because the per-digit `acc*10+d` is bignum-boxed.
  The honest framing is a *ratio to the same-machine C baseline*, not an absolute MiB/s number.
- 2026-10-17 — **A `Prod Nat USize` in `@[extern]` C is `lean_alloc_ctor(0, 2, 0)` with two
  *object* fields — `Nat` via `lean_usize_to_nat`, `USize` via `lean_box_usize`; both box as
  objects (a `USize` is NOT a raw scalar once it is a field, only as an argument).** Returning
  `some (n : Nat, k : USize)` (the result of a varint/decimal seam): build the pair with
  `lean_alloc_ctor(0, 2, 0)`, `lean_ctor_set(pair, 0, lean_usize_to_nat(n))` (small-`Nat`
  immediate; `lean_unbox` on a bignum/mpz would be wrong, so document small-`Nat`-only), then
  `lean_ctor_set(pair, 1, lean_box_usize(k))`, then wrap in `some`'s tag-1 ctor
  `lean_alloc_ctor(1, 1, 0); lean_ctor_set(opt, 0, pair)`. The authoritative reference is the
  way the *Lean-generated* C constructs the same type (in `.lake/build/ir/*.c`): the generator's
  `Prod`-of-`Nat`-and-`USize` is `lean_alloc_ctor(0,2,0)` with the `Nat` as `lean_usize_to_nat(…)`,
  not the `lean_alloc_ctor(0,1,sizeof(size_t))`+`lean_ctor_set_usize` you might guess from the
  scalar-argument lowering. (Generalizes the earlier `Option USize` entry: every *field* whose
  runtime rep is an unboxed scalar is still re-boxed via `lean_box_*` when stored in a constructor.)
- 2026-10-17 — **`String` is a `Classical.choice`-leaky substrate for a proof gate: every
  accessor (`String.toList`, `.data`, `.get`, `.length`, `toNat?`) is `@[extern]` UTF-8-backed and
  leaks `Classical.choice`; a clean parser/reference over text must take raw `ByteArray`/`Array
  UInt8` instead.** `#print axioms String.toList`/`String.data`/`String.get`/`String.length` all
  report `[propext, Classical.choice, Quot.sound]`, so a `String`-typed seam's Lean body (a spec
  pinned to `[propext, Quot.sound]`-only) cannot use any of them. `Array.get`/`Array.extract`/
  `ByteArray.mk`/`ByteArray.data`/`UInt8.toNat`/`Char.toNat` are axiom-clean (`[propext,
  Quot.sound]`-only), so write the reference over bytes (e.g. an ASCII-decimal scanner folding
  `acc · 10 + (b.toNat - 48)`). `Char.isDigit`/`Char.ofNat` are also clean, but a `List Char` from
  `String.toList`/`.data` is not. Rule: text-processing seams that must stay in the axiom-clean
  gate take `ByteArray`, never `String`.
- 2026-10-17 — **A "committed" structural decoder (`Option`-threading `orElse` on `Alternative`,
  first-branch `bind` on `seq`) is NOT `= (backtracking decoder).head?` in general — the `seq`
  commitment is strictly stronger than "first result".** If `d₁`'s first result is a dead end for
  `d₂` (its `bind` yields `none`) but a *later* `d₁` result succeeds, the committed `decodeOne (seq …)`
  returns `none` while `(decodeArray (seq …)).head?` skips the dead-end and returns the later
  result's pair. So the "committed result = first backtracking result" identity holds only for the
  `alt` node, not `seq`; the honest uncontradictable facts are (a) **soundness** — every committed
  result is a member of the backtracking list (provable by induction, `[propext, Quot.sound]`), and
  (b) the **gated** completeness — pair-level uniqueness (value+count) makes the committed decoder
  equal to the (unique) backtracking result. Do not assert the naive `head?`-equality; it is false,
  and the gate that makes the fast path sound is "backtracking result is unique", not "commit = first".

- 2026-10-17 — **The boxing of a scalar-payload `Option` (`Option USize`/`Option UInt64`) in
  hand-written `@[extern]` C is a *constructor with a scalar field*, not a small-int box — and
  getting it wrong only *appears* to work, so value-check against the IR, never by reasoning.**
  Returning `some (v : USize)` from a `@[extern]` symbol is **not** `lean_box(v.toNat+1)` (that is the
  small-`Nat`/`Int` encoding) and **not** `lean_box_usize(v)` alone: the `Option` sum type is
  `none = lean_box(0)` (tag 0) and `some v` = a **tag-1 constructor object holding one *scalar*
  field** — allocate `lean_alloc_ctor(1, 1, 0)` (tag 1, `numObjs=0`, `scalarSize=1`) and set the field
  with `lean_ctor_set(r, 0, lean_box_usize(v))`. A `lean_box_usize(v)` returned bare has tag 0 and is
  read back as `none`; a `lean_box(v+1)` is a small-int box with the wrong scalar tag. The
  generated-code reference is authoritative: in the emitted `.c`, `some (off + i)` on a `USize` compiles
  to `lean_alloc_ctor(1,1,0); lean_ctor_set(_, 0, lean_box_usize(usize_add off i))`, and the *consumer*
  reads it as `lean_ctor_get(x,0)` → `lean_unbox_usize(...)`. Grep `.lake/build/ir/*.c` for how the same
  type is *constructed* in Lean's own output and mirror it exactly; a semantically-right `memchr` with a
  wrong return-box ships garbage that only the byte-for-byte value check catches.

- 2026-10-17 — **Generalize a suffix `byteSlice` seam into `blitBytes` (buffer-to-buffer `memcpy`) and
  `findByte` (`memchr`); keep every seam `USize`-indexed and its Lean body the `Array` (not `ByteArray`)
  spelling so the spec law is `rfl`.** A `blitBytes dst dstOff src srcOff len` body is the
  `Array.extract`+`append` composition over `.data` (reducible; `blitBytes_spec` closes with **no axioms**
  at all), while the `findByte` body is `Array.findIdx?` over `Array.extract` of the suffix re-offset by
  `off` (`Array.findIdx?` returns a `Nat` relative to the extract, so add `off` to get the absolute `USize`;
  `findByte_spec` is `[propext]` from the `==`/`Bool` reflection in the predicate). Both C symbols are a
  single `memcpy`/`memchr`, clamps mirroring `Array.extract`'s truncation. The bench value-check compares
  the C result against the Lean body byte-for-byte (constructed from the *same* `Array.extract`+`append`/
  `findIdx?` expression), never a length check, and a mid-buffer window/sentinel (not the prefix/suffix
  edge) is what actually catches a wrong offset/length/byte in the C.
- 2026-10-17 — **"Make the shipped C fast, make the pure spec slow" is the honest end-state, and it
  cuts the whole speed plan to two obligations.** When the *pure* `Bytes`/`List` interpreter is
  accepted as a *specification* (the denotation every law is proved against) rather than the run
  model, the perf question stops being "make the generic interpreter fast" — which is a dead end
  (a pure immutable value can't be built by `memcpy`; unboxed `UInt8` + scalar `USize` cursor +
  committed `|` choice are, respectively, trusted-only, proof-obstacle, and conditional-on-`Unambiguous`
  inside a `[propext, Quot.sound]`/zero-`sorry` gate). The plan reduces to exactly two layers:
  (a) **`@[extern]` C seams** (shape 2, elaborating body) for each irreducible raw-byte op — a
  generalized `blitBytes` (superset of a suffix `byteSlice`), a `memchr`/`findByte` scanner, a
  varint encode/decode-into-buffer, a `strtod`/numeric-parse, a zlib `deflate`/`inflate`; each is
  ~20 lines of C + a reducible Lean `def` whose body is the *spec*, matching the already-shipped
  `byteSlice` template; and (b) **per-format specialized decoders/encoders** (WAV header + one PCM
  `memcpy`, protobuf varint/tag loop + length-delimited blit, PNG zlib seam) each proved *equal to
  the generic spec once* by `decodeArray_eq`-style refinement lemmas. The key realization that
  makes this sound: `@[extern]` only swaps the emitted C, so `#print axioms` sees the pure body
  regardless — the fast C is *invisible to the gate*, and the only new proof work is law-level
  (pure spec = pure seam body), never C-level. "No axiom" stays honest as "spec ≡ seam-body
  proven; seam-C trusted, bench-value-checked."

- 2026-10-17 — **An `@[extern]` trust seam with an elaborating body (shape 2) is *invisible to
  Lean's reduction* — the trusted C is a runtime contract that can never appear in a law.
  `@[extern "sym"]` swaps only the *emitted* C; the Lean `def` body still reduces under
  `simp`/`rfl`, so `#print axioms f` reports the *body's* axioms (`[propext, Quot.sound]`-clean
  or none) **regardless** of what the C does — no Lean proof can even see the C symbol. Two
  consequences, both earned this session: (a) it is a **category error** to call a trust seam
  "the single unproven step of a law"; there is no such proof step — the trust lives in prose
  (F\*-vs-KaRaMeL posture: "declare the primitive, hand-write the C, name the seam"), orthogonal
  to the axiom gate. (b) To *prove* `wrapper_spec` for a `wrapper b i := byteSlice b i`, you do
  **not** need the seam at all — you unfold the body; the only real proof obligation is whatever
  the *web* of `Nat`/`USize` indices forces (see next entry). Preserving this distinction is what
  keeps "no axiom" from being misread as "no trust" and vice versa.

- 2026-10-17 — **The `Nat ↔ USize` roundtrip is the platform-fact leak — give the extern-adjacent
  wrapper a `USize` index, keep `Nat` *only* on the proof/spec side.** Refines the earlier
  "keep the cursor on `Nat`" entry: split the decision in two. The *spec/cursor* stays `Nat` (as
  before). But the *wrapper over an `@[extern]` whose C takes `USize`* must itself be
  `USize`-indexed, or its refinement law inherits `(c.toUSize).toNat = c`, which needs
  `c < 2^System.Platform.numBits` — the exact unproven platform fact the repo refuses.
  Concretely: `f (b : ByteArray) (i : USize) : ByteArray := byteSlice b i` has `f b i =
  ByteArray.mk (b.data.extract i.toNat b.data.size)` as an `rfl` (unfold `byteSlice`'s body;
  `(ByteArray.mk a).data = a` and the `.size` coincidence are `rfl`); a `Nat`-indexed variant
  would instead need `(i.toUSize).toNat = i`. The `Nat → USize` conversion is fine **at the call
  site** (where the caller holds the `Nat` cursor and does `c.toUSize` once); it must not be
  *baked into* the wrapper's own sigma/index, or it poisons every lemma built on it.

- 2026-10-17 — **`USize` in an `@[extern]`'s *argument* lowers to an unboxed `size_t` scalar;
  confirm it in the emitted IR, don't assert it.** `lean_byte_array_uset`'s C is
  `..._uset(lean_obj_arg, size_t, uint8_t)` — i.e. a `USize` parameter compiles to a raw `size_t`
  (`lean_unbox_usize` in the emitted wrapper), while `ByteArray` stays a borrowed `lean_object *`.
  This is the one place the "`USize` is a scalar" claim is *actually* true (the carrier `Nat`
  cursor is NOT — it boxes to bignum, per the task-3.1 IR finding). Verify by grepping
  `.lake/build/ir/<Module>.c` for the symbol's declaration (`lean_object* sym(lean_object*, size_t)`)
  and the call site (`lean_unbox_usize`), never by assertion.

- 2026-10-17 — **How the genuine-suffix invariant actually closes (four exact tactics).**
  (Resolves the previous entry — the blocker is now proved.) (a) Prove the invariant
  **pointwise first** (`t.bytes i = s ⟨i.val + t.consumed, ·⟩` by induction on the description,
  with a shared `i.val + t.consumed < n` bound lemma), then **lift** to the `Bytes`-level
  `bdrop` form by `apply Bytes.ext; intro i; rw [cast_bytes_val' e …]` — the pointwise form
  has a clean `seq` induction (nested consumed counts close by `omega` over `sub_sub_add`),
  the `bdrop`/cast form does not. (b) **`subst e; simp` collapses "interpreter insensitive
  to a length cast"** (`decode d (cast (congrArg Bytes e) s) = (decode d s).map …`): the cast
  is along a `Nat` length equality, so `subst` reduces it to `rfl`; do **not** prove it by
  induction (the membership-bound spelling thrashes). (c) **`List.map_inj_left` threads the
  membership hypothesis** a pointwise-lemma needs: a `flatMap f l = flatMap g l` with the same
  `l` becomes `congrArg (·.flatten) (List.map_inj_left.mpr (fun a ha => …))`, and `ha : a ∈ l`
  is exactly the input a membership-parameterized lemma (`bdrop … = cast … t.bytes` for
  `(x,t) ∈ decode d s`) requires — bare `congr 1; funext` *loses* `ha`. (d) **`rw [cast_cast]`
  closes composed length casts** via proof irrelevance: after bridging `bdrop (i+(n-t)) =
  bdrop t ∘ bdrop i` and `t.bytes = cast … (bdrop t s)`, the remaining `cast e₁ (cast e₂ X)`
  equalities collapse by `rw [cast_cast]` (the `Nat` equality proofs are `Nat.eq_irrel`).

- 2026-10-17 — **A `Suffix`-returning spec vs a cursor-returning fast path refinement is
  blocked by `decode`'s own "genuine suffix" invariant, not by any general `Suffix` fact.**
  To equate `decodeArray d a (consumed c)` with `decode d t.bytes` (where `t : Suffix n` came
  from `decode d s`), the `seq` case needs `t.bytes = bdrop (n - t.remaining) s` — i.e. the
  fact that `decode` *returns genuine suffixes of its input*, `∀ (x, t) ∈ decode d s,
  t.bytes = bdrop (n - t.remaining) s` (proved by induction on the description `d`). The
  tempting `bdrop c s = cast … t.bytes` equality is **false for an arbitrary `Suffix t`** — it
  only holds because `t` was *produced by `decode`*. So a two-level refinement (spec returns
  `Suffix`, fast path threads a consumed count) does **not** close by library-transport alone:
  you first prove the spec function's *own* "suffix is a suffix" invariant, then compose the
  transport lemmas (`bdrop (i+m) = bdrop m ∘ bdrop i`, the cast-insensitive `.remaining`, the
  consumed-count transitivity). Discover the missing invariant and prove it before wiring the
  `seq`/`bind` case — otherwise you thrash on an unprovable arbitrary-`t` lemma.

- 2026-10-17 — **`List.foldl` over `ByteArray.push`/`Array.push` is proved via `.data`/
  `Array` projection, not by `simp` (which *loops* on the recursion equation, and the `ByteArray`
  ops are FFI-opaque).** `ByteArray.push`, `ByteArray.empty`, `ByteArray.mk` do not unfold, but
  `(bs.push b).data = bs.data.push b` is `rfl`, and `ByteArray.ext : x.data = y.data → x = y`
  reduces a `ByteArray` goal to an `Array` goal. The projection lemma
  `(List.foldl (fun a b => a.push b) acc xs).data = List.foldl (fun a b => a.push b) acc.data xs`
  is proved by induction + `bpush_data` (axiom-free); the `Array`-level
  `List.foldl (fun a b => a.push b) acc xs = acc ++ xs.toArray` closes by `Array.ext'` +
  `Array.toList_append`/`toList_push` + `List.append_assoc` (`[propext, Quot.sound]`-only). Use
  `rw [List.foldl_cons, ih (acc.push b)]` (never `simp [foldlDef]`, which loops); `Array.toList_singleton`
  does not exist — `#[b].toList = [b]` is `rfl`/`dsimp`.

- 2026-10-17 — **An `Option`-returning refinement's `bind`/`map`/`orElse` skeleton bridges via a
  "`none`-iff" derived from the `map`-equality, not by `rw` on the bare scrutinee.** Proving
  `(f d x).map toList = (g d x).map ofFn` by induction, the `seq`/`alt` cases need to know
  `f d x = none ↔ g d x = none`; derive it once as `map_none_iff (h : (f d x).map p = (g d x).map q)`
  — `constructor <;> intro hne <;> cases the other option; rw [hne, the-other-cases-lem] at h;
  simp only [Option.map] at h; cases h`. Then `cases ha : f d₁ x₁` and `rw [none_iff.mp/mpr ha]`
  to line up the `bind`/`orElse` structure (use `Option.orElse.eq_def` only via `simp only
  [Option.orElse]` — bare `rw [Option.orElse]` fails). In the `some`/`some` leaf, extract the
  pointwise equalities with `Option.some.inj h` after `simp only [Option.map] at h`, and lift the
  leaf (`ofFn_concat`, `Array.toList_append`) with `congrArg some`.

- 2026-10-17 — **`Array.toList_ofFn`/`List.toArray_ofFn` round-trips leak `Classical.choice`;
  the clean encode readback is the List-level form `(·.toList)` vs `List.ofFn ∘ snd`, and the
  `Fin`-index head/`bdrop` reductions are `omega`- or `simp`-driven, not `rfl`.** `Array.ofFn` can't
  appear on the refinement RHS (`Array.toList_ofFn` is `[Classical.choice]`); instead prove
  `(encodeArray d x).map (fun a : Array UInt8 => a.toList) = (encode d x).map (fun e => List.ofFn e.2)`
  with the `seq` leaf `Array.toList_append` + `ofFn_concat` (both `[propext, Quot.sound]`). For a
  `byte`-style `bdrop i s ⟨0, h⟩ = s ⟨i, ·⟩` value equality, `unfold bdrop; congr 1; apply Fin.ext;
  dsimp; omega` closes the `Fin`-proof-transparent goal (bare `rfl`/`congr` leaves `↑⟨↑⟨0, ⋯⟩+i, ⋯⟩`);
  and a `consumedAbs`-style `.remaining` identity needs `dsimp only [Suffix.drop]` (not `unfold`,
  which also breaks type-correct cast proof terms elsewhere in the goal) before `omega`.

- 2026-10-17 — **`USize` is a *proof* obstacle even when it is the *right* runtime scalar:
  its `+` is `Nat`-addition modulo `2^64` and its size is a platform fact — keep the spec/cursor
  on `Nat`, and treat `USize` as an IR-inspection question, not a refinement invariant.**
  `USize.toNat_add : (a + b).toNat = (a.toNat + b.toNat) % 2^64` and
  `USize.size = 2^64` (which needs the unprovable `System.Platform.numBits = 64`) mean a
  refinement law threading a `USize` cursor (`(x,c) ∈ f a i`) contracts the modulo into every
  step: `c.toNat` of `i+1` is `(i.toNat+1) % 2^64`, not `i.toNat+1`, so no induction closes
  `[propext, Quot.sound]`-only without an extra "the buffer is < 2^64" platform premise. The
  clean split: **`Nat` is the proof/runtime carrier** (same choice a `pushBytesFrom`/bignum-fold
  already makes); "does `USize` lower to `size_t`, no `lean_alloc`/box per node?" is answered
  by *inspecting the emitted `.c`* (`size_t`, `lean_object *`), never by asserting it — if it
  does not, record that and mark the "scalar index" premise false rather than forcing a `USize`
  type that breaks the axiom gate. Decide the cursor's *type* before writing the refinement,
  because it is a proof-budget decision, not a perf-tuning decision you can flip later.

- 2026-10-17 — **RESOLVED the `ofFn`-bridge `Classical.choice` leak: the *plain* `Array`↔`List`
  primitives are axiom-free; only the `ofFn`-*specialized* bridges leak.** Chasing a
  `Fin n → T`-carrier fast-path refinement that refused to close `[propext, Quot.sound]`-only,
  the clean/leaky split turned out to be sharper than "`List` clean, `Array` leaky": `Array.toList`,
  `List.toArray`, `Array.push`, `Array.append`, `Array.foldl`, and `Array.getElem_toList` are **all
  axiom-free** (`#print axioms` ⇒ none), and `List.append_toArray`/`Array.toList_append`/`Array.size_append`/
  `Array.append_assoc` are `[propext, Quot.sound]`; the leak lives **only** in `Array.getElem_ofFn`,
  `List.toArray_ofFn`, `Array.toList_ofFn`, and `List.getElem_ofFn`'s output (all `[Classical.choice]`).
  So a readback `xs[i] = f ⟨i,·⟩` must route through `Array.getElem_toList` (axiom-free) + a hand-proved
  clean `(List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h List.length_ofFn⟩` (induct on `n`; `rfl` after the
  `Fin.succ` `rfl`), and substitute the list-level equality `arr.toList = List.ofFn s` **before** any
  `[i]` via `simpa only [h, List.length_ofFn]` — never `rw [h]` inside the `i < length` dependent motive.
  Also: bare `simp`/`simpa` the *whole* way auto-fire classical lemmas; `simp only [hr, Option.map]` is
  needed even in base `none`/`nil` cases of an `Option`-returning accumulator (unfold `Option.bind`/`Option.map`
  explicitly so `none.bind`/`Option.map _ none` reduce).
- 2026-10-17 — **`Classical.choice` in refinement proofs leaks from *specific* stdlib
  `GetElem` round-trips and from bare `simp` (not `simp only`) — bisect with minimal
  `#print axioms` repros, don't guess.** Proving `fastEncode p xs = encode p xs` over a
  `Fin n → T` carrier, three *surprising* clean/leaky splits were pin-pointed: (1)
  `(List.ofFn s)[i.val]` (a pure `List` read at a `Fin` index) is `[propext]`-clean, but
  `(List.ofFn s).toArray.toList[i.val]` — the **same** term through a
  `List.toArray`/`Array.toList` round-trip — leaks `[Classical.choice]` **even for the
  trivial `x = x` `rfl`**. The `.toArray.toList` `[i.val]` re-enters the classical `GetElem`
  instance during elaboration; `Fin.cast`/`Nat.lt_of_lt_of_eq` transport is *not* the culprit
  (both are `[propext]`/no-axioms). (2) bare `simp [X]` auto-fires other `[simp]` lemmas
  (classical ones included), while `simp only [X]` restricts to `X` — an
  `@[extern]`/`ByteArray`-adjacent equality that leaked as `simp [Array.toList_append, …]`
  closed `[propext, Quot.sound]`-clean as `simp only [Array.toList_append, …]`. (3)
  `rw [htoList]` rewriting a `toList` equality *inside* a `[i.val]` access fails
  "motive is not type correct" — the `GetElem`'s `i < length` bound is a dependent motive on
  the rewritten length, so substitute the list equality *before* applying `[i.val]` (via
  `funext`/`congrArg` on the list), never `rw` through the index. Also: `List.getElem_ofFn`
  is `[propext]`-clean **as a theorem** but its *output* term carries a `by simp_all` index
  proof that leaks `Classical.choice` when `rw`'d — prove your own clean variant
  (`(List.ofFn f)[i] = f ⟨i, Nat.lt_of_lt_of_eq h List.length_ofFn⟩` by `induction n` +
  `Fin.foldr_succ`/`getElem_cons_zero`/`getElem_cons_succ`).

## Changelog

- 2026-10-19 — **Proving a byte-substrate codec's unambiguity is the gate to the inherited
  repetition-level roundtrip.** Added seven entries (see "Append new learnings"): the
  `Rel_count_len` / `count_satisfy_unambiguous` / `Unambiguous_iso` / `relRepeat`-unambiguity
  induction chain; the absence of `norm_num` in stdlib-only; the `Fin.val`-of-`⟨0,·⟩`
  reduction trap (`by simp`, not `by omega`/`by decide`/`by norm_num`); `splice_prefix_read` +
  `bdrop_splice` as the same-type prefix/tail recovery transport; the `subst`-vs-`omega`
  contradiction; `cases b` before `rw [relRepeat_cons] at hb`; and the 5-step inherited
  `decodeFull` roundtrip (`encodeRepeat_rel` → `decodeRepeat_spec` → `decodeFull_spec` with a
  `prepend_prefix_eq`-pinned `huniq`).

- 2026-10-17 — **A length-indexed function (`Fin n → T`) is a scalar *read* substrate and a
  nested-closure *bulk-write* substrate — do not claim "one pure carrier does both reads and
  writes".** Profiling a `bytes n := Fin n → UInt8` carrier showed `decode`/scalar `s ⟨i,·⟩`
  lowers to a single indexed load (the "scalar read" story is real and worth keeping), but a
  *bulk* `encodeRepeat` over the same carrier builds one `concat` closure (5-arity, `Fin`-sum
  dispatch + a `Nat`-add + 2 ctors) *per element*: linear but ~25× slower than an elided
  contiguous `ByteArray`/`Array UInt8` accumulator over `@[extern]` primops, and ~2000× off
  `memcpy`. A pure function cannot be a "flat accumulator" / "pre-sized buffer" — that wording
  describes a mutable contiguous buffer (a *different* carrier). The fix is **not** a pure
  re-staging (unreachable while keeping the denotation byte-identical) and **not** LLVM (the
  `@[extern]` accumulator already hits the memory floor on plain clang): it is a **law-backed
  fast path** — `fastEncode p xs = encode p xs` proved *pointwise* via the carrier's finitary
  equality (`FunExt` over `Fin n`) + `Array.ofFn`/`GetElem` (the `Fin n → T ≃ Array T` bridge),
  never `Array.extract`/`Array.toList` (which leak `Classical.choice` — the historical failure
  of such fast paths). Keep the pure carrier as the *specification* for every law; add the
  contiguous buffer only as a *proved-equal implementation*. (Generic; cf. §7 "carrier swap".)

- 2026-10-17 — **`cases`/`subst` on a dependent `Sigma`-of-functions equality fails
  ("Dependent elimination failed") — use `Sigma.mk.inj` to get `fst = fst' ∧ snd ≍ snd'`,
  then `eq_of_heq`/`heq_of_eq`.** For `h : ⟨n, f⟩ = ⟨m, g⟩` where `f : Fin n → T` and
  `g : Fin m → T` (a `Sigma` whose `snd` is a *function*, e.g. a length-indexed byte
  string `Bytes n := Fin n → UInt8`), `cases h` and `subst h` both raise "Dependent
  elimination failed … failed to solve equation `(fun x => …) = fun i => …`" — Lean cannot
  decompose a function-valued dependent pair. The workable route is `Sigma.mk.inj h`,
  which returns `conj (h₁ : n = m) (h₂ : f ≍ g)`; then `subst h₁` (or `eq_of_heq` when
  the indices become `rfl`) turns the heterogeneous equality into a homogeneous one you
  can `rw`. Only after the *indices* are definitionally equal can `heq_of_eq`/`eq_of_heq`
  apply (they demand a single `Sort`); until then the `≍` is genuinely heterogeneous.

- 2026-10-17 — **To fill `Sigma.ext h' (h'' : a ≍ b)`'s second argument across a length
  cast, prove `a = cast (congrArg F h'.symm) b` and compose `(heq_of_eq that).trans
  (cast_heq (congrArg F h'.symm) b)`.** `heq_of_eq : a = b → a ≍ b` needs `a`/`b` in one
  type; when they differ only by a transport `h' : X = Y`, produce the homogeneous equality
  `a = cast (congrArg Bytes h'.symm) b` (same type after the cast), then bridge back to the
  *uncast* `≍` via `cast_heq` (`cast e x ≍ x`) + `HEq.trans`. This is the one reliable
  recipe for a heterogeneous equality whose two sides are a length-indexed function; avoid
  `Σ`-notation `.inj`/`▸` (the `▸`/`Eq.ndrec` notation demands an `=` LHS, not a `≍`).

- 2026-10-17 — **`congr 1`/`simpa` and even `rw` can *loop* (maxRecDepth) on a `def` of
  shape `fun i => if h : i.val < … then … else …` (a `Fin`-indexed `concat`); `set_option
  maxRecDepth` and drive the two components with `rw` + `congrArg`/`congrArg single`.**
  A pointwise `concat (single x) rest := fun i => if i.val < 1 then x else rest ⟨i.val-1, ·⟩`
  is a term whose unfold `congr`/`simp` recurse into without making progress. For a goal
  `concat (single a) xs = concat (single b) ys`, do `rw [h₁ : xs = ys]` then `congr 1` then
  `exact congrArg single h₂`; for a `cast (congrArg Bytes h) (concat …)` transport, `rw
  [concat_law]` (one step) instead of `simpa` which can re-enter the `concat` unfold.

- 2026-10-17 — **`bs 0` (via `OfNat (Fin n)`) and `bs ⟨0, proof⟩` are *different* `Fin`
  proofs, so a decoder's `if`-unfolded head byte won't unify with a `let b := bs ⟨0, p⟩`;
  bind the head as `let b := bs 0` (the `OfNat` spelling) to match the decode's own
  reduction.** When a structural decoder reads `bs ⟨0, Nat.pos_of_ne_zero h⟩` and a proof
  then splits on `b.toNat`, the elaborator keeps `b` distinct from the decoder's inline
  `bs 0` unless `b` is defined *as* `bs 0`. `dsimp [b]`/`simp [b]` unfold the `let` in the
  goal but leave `hypotheses` mentioning `b` stale — so `simp [hov] at h` (where `hov : b …`)
  "makes no progress". Define the head with the `OfNat` numeral and drop the explicit proof.

- 2026-10-17 — **`simp [hov]` with `hov : ¬ (P ∧ Q)` does *not* reduce a dite
  `if P ∧ Q then none else some …`; `by_cases` the disjunction, or let `simp [P<…]` alone
  produce the `(P → ¬Q) ∧ R` conjunction and `rcases` it directly.** A hypothesis that is a
  negation of a conjunction is not a rewrite for the positive conjunct; `simp [hov]` leaves
  the `if` untouched (reports "no progress"). Either `by_cases hc : P ∧ Q` and get the
  `some`/`none` branch explicitly, or observe that `simp [Hpos] at h` already normalizes
  `some (…) = some (…) ∧ hov`-gated to `(P → ¬Q) ∧ (acc + v·mult = m) ∧ (k = 0) ∧ (rest ≍ …)`,
  which you then `rcases ⟨_, hm, hk0, _⟩` (discarding the `P → ¬Q` conjunct).

- 2026-10-16 — **`Classical.choice` leaks from `simp [defThatUnfoldsToAMatch]`, not from
  `omega` or the *named* `def`-unfold lemmas — use `Rel_pure`/`Rel_empty` (iff lemmas), reject
  bare `simp [Rel]`.** Chasing "why does `#print axioms F` report `Classical.choice`" over a
  length-indexed carrier (`Bytes n := Fin n → UInt8`), the culprit was **not** the `cast`/
  `omega`/`by_cases` machinery (all `[propext, Quot.sound]`), and **not** `set_option`-visible
  `classical` — it was `simp [Rel]` in *base cases* (`empty`/`pure`), where `Rel` is an
  `inductive`/`def` whose `empty`/`pure` constructors are terms in an arbitrary `Type α`:
  unfolding `Rel` directly (rather than via its `Rel_empty : Rel (empty) x s ↔ False` /
  `Rel_pure : Rel (pure x₀) x s ↔ x = x₀ ∧ n = 0` iff lemmas) makes `simp` intro a `Decidable`/
  `of_decide`/`dite` path that pulls `Classical.choice`. The same base case proved with the
  **named iff lemma** (`simp [decode, Rel_pure]`, then `constructor`) stays `[propext, Quot.sound]`.
  Symmetrically `Nat.sub_lt_iff_lt_add` (used to turn `a - b < c` into `a < c + b`) is one of the
  stdlib `Nat` lemmas that *does* carry `Classical.choice` — replace it with `omega`, which is
  constructive. **Diagnostic workflow:** when `#print axioms Foo` shows `Classical.choice`,
  bisect by `#print axioms` on each *named* lemma Foo calls (not on `Foo` itself — huge), and test
  a minimal repro of each base case's `simp […]` (a `simp [decode, Rel]` in an `empty`/`pure`/
  `byte` branch is the usual first suspect).
- 2026-10-16 — **A structure-`ext` lemma with a `cast`-indexed second hypothesis must be
  applied with explicit `t₁ :=`/`t₂ :=` — bare `apply Foo.ext` mis-infers the operands.** For a
  `Suffix n`-style record with fields `remaining`/`hle`/`bytes : Bytes remaining`, the ext lemma
  `Suffix.ext {t₁ t₂} (hrem : t₁.remaining = t₂.remaining) (hbytes : cast (congrArg Bytes hrem)
  t₁.bytes = t₂.bytes) : t₁ = t₂` cannot be applied by `apply Suffix.ext` on a goal
  `drop … = r`: Lean infers `t₁`/`t₂` the *wrong way round* (the two sides of the goal are both
  `Suffix`-typed projections, so unification picks an arbitrary order), then the *first* subgoal
  it emits is `hbytes` (not `hrem`), and every `·` bullet is off by one. Write
  `refine Suffix.ext (t₁ := …) (t₂ := …) ?_ ?_` (named, in order). The `hbytes` proof itself is a
  `cast e (cast e.symm x) = x` cancellation (`change` to name both casts, then `simp` / `subst e`).
  The field-equality `hrem` direction matters: `Nat.sub_self n : n - n = 0` needs `.symm` when the
  goal asks for `0 = n - (Suffix.id n s).remaining` (the `.remaining` projection is `n` only after
  `dsimp [Suffix.id]`).
- 2026-10-16 — **A `let`-bound carrier value is not unfolded by `rw`/`simp` — `dsimp [x]`
  (zeta) it in position first, and `rw [List.mem_cons]` before `right` on a `::`-membership goal.**
  With `let r' : Suffix (n - m) := Suffix.drop L (bdrop m s)`, a later goal `bdrop m s =
  r'.prepend (cast … s₂)` will **not** match a lemma stated in terms of
  `Suffix.drop L (bdrop m …)` until you `dsimp [r']` (reduces the `let`). In a `decr …` proof
  where the recurrence is over a `Suffix`/`drop`, unfold the `let` *before* rewriting the outer
  `s = r.prepend …` hypothesis, else the `.prepend`/`.trans` projections stay stuck. Also:
  membership over a cons in the *goal* (`x ∈ b :: l`) must be normalized with
  `rw [List.mem_cons]` **then** `right` — bare `right` on the raw `List.Mem` does not split the
  `∨` (`right` only fires on the already-rewritten `Or`). And `List.mem_attach l a : a ∈ l.attach`
  is a bare theorem (not an iff) — pass the *whole* Subtype, and fill the `∃ a, a ∈ l ∧ P a` (from
  `List.mem_flatMap` in the *goal*) with a **three-slot** `refine ⟨a, List.mem_attach l a, ?_⟩`,
  not `⟨a, ?_⟩`.
- 2026-10-16 — **A list/`decodeRepeat` bidirectional law is proved by `Nat.strongRecOn` (not
  `induction`), with the productivity witness discharging the `< n` guard, and the cons-case**
  recursion mirrors the `seq`-case factorization. For `(xs, r) ∈ decodeRepeat p h n s ↔ ∃ s₀, …`
  over a productive step (`h : ConsumesByte p`), the recursion is **well-founded on `n`**, so use
  `Nat.strongRecOn n` with the motive carrying the whole `∀ xs s r` (introduce `xs`, then `revert
  xs` so it sits under the `∀` the IH quantifies over), and the IH is applied at `t.remaining < n`
  where that `<` comes **from `h x s t hmem₁`** (the productivity theorem), not from an unstated
  `n - m < n`. The `(∃ a, a ∈ l ∧ P a)` back-direction (from `List.mem_flatMap`/`mem_map` in a goal)
  is a **three-slot** `refine ⟨a, mem, ?_⟩` (the third is the `f a = b` map equation, closed by
  `congrArg (fun y => (x :: rest, y)) htrans`).
- 2026-10-16 — **A length-indexed `Bytes n := Fin n → UInt8` carrier needs a family of
  *cast-commutation* lemmas — each is a pointwise `Bytes.ext` + `splice_apply` + one
  `cast_fin_symm` rewrite, then a `n - …`-region case split closed by `omega`; the cost is a
  recurring `(Suffix.drop k s).remaining` vs `n − k` transparency mismatch.** The laws (`decode_spec`
  `pure`/`byte`/`seq`, `decodeRepeat_spec`, `encode_of_decode`) turn on **three** transport shapes, all
  `[propext, Quot.sound]`-only, and each is a *named lemma* you prove once:
  - *`splice` associativity is a three-way re-parenthesization lemma, not a `simp`.*
    `splice hm (splice hk s₁ s₂) s₃ = splice (Nat.le_trans hk hm) s₁ (cast … (concat s₂ s₃))`
    (`splice_splice_assoc`) — the `BitVec`-free `concat_assoc` bundled with the `n − m` sub
    arithmetic — closes only by *explicit* `cast_fin_symm` rewrites on **both** the outer and the
    inner `splice` index casts, in the correct order (`rw [splice_apply]` for the outer two splices,
    `unfold concat`, `rw [cast_fin_symm (e := splice_add hm)]` for each, `dsimp`, then the three-region
    `by_cases`). The trap that eats a session: `simp [splice]` first produces `cast ⋯ (concat (cast ⋯
    (concat s₁ s₂)) s₃)` whose inner `cast` is applied to a `concat` *value* (a `Bytes`-typed lambda),
    and `cast_bytes_val'` will not fire because the index is not a bare `Fin` variable — hence
    hand-steering with `splice_apply` (which keeps the index as `cast (congrArg Fin …).symm i`) is the
    reliable route, not `simp`.
  - *`cast` commutes past a `splice` prefix:* `cast (congrArg Bytes e) (splice hm s₁ s₂) =
    splice (…) s₁ (cast … s₂)` (`splice_cast_commute`) is `subst e; simp`-trivial in the `e : n = n'
    = rfl` case — but only if you `subst e` *first* (then both sides are literally `splice hm s₁ s₂`
    up to proof-irrelevant `m ≤ n` witnesses); without the `subst`, `simp` stalls. This is the
    one-line bridge for `Rel_seq` witnesses whose suffix length is `n − t₂.remaining` vs the encoder's
    `(n−t₁)+(t₁−t₂)`.
  - *Empty- and identity-suffix reconstruction:* `(Suffix.empty n).prepend (cast … s) = s`
    (`prepend_empty_eq`) and `(Suffix.id n s).prepend (cast … emptyBytes) = s` (`prepend_id`) — both
    are `Bytes.ext` + one `splice_apply` + `cast_fin_symm`, and the `n − 0`/`n − n` region is closed
    by `Nat.sub_zero n`/`Nat.sub_self n` (a *named* `have`, not inline) so `omega` can fire.
  - *The recurring blocker:* a `Suffix`'s accessor (`(Suffix.drop 1 s).remaining`, `(Suffix.id n s).remaining`)
    does **not** reduce to `n − 1`/`n` under `rw`/`simp` unless you `dsimp [Suffix.drop]`/`unfold Suffix.id`
    *in the right position* (before the `cast` whose `e` proof must unify). The `by omega` / `by simp`
    *proofs* that `cast_fin_symm`/`cast_bytes_val*` emit are opaque, so a nested `↑⟨↑i, by omega⟩.val`
    will not reduce — `fin_cases`-style `Fin.mk`/`.val` cancellations need the proof to be `rfl`-clean
    (hence the named `have` for the arithmetic).
  - *`Functional`/`unambiguous` converse laws over the length-indexed carrier compare `Sigma` pairs,*
    and `encode_of_decode` closes by `hd x s s' hrels hrel' : ⟨n, s⟩ = ⟨n', s'⟩` (then `.symm`), with
    `hrels : Rel d x s` recovered from the decode premise via `(bidir d x n s).2` — avoid `Sigma.mk.inj`
    and its `HEq` (heterogeneous equality) fallout entirely; restate the witness so a plain `Rel d x s`
    is available.

- 2026-10-15 — **Re-derived `Rel`/`decode`/`encode` laws over a length-indexed `Bytes n := Fin n → UInt8`
  carrier need a small set of *transport* lemmas, each `subst`- or `omega`-trivial, not new proof
  techniques.** The concrete gaps hit this session (all `[propext, Quot.sound]`-only):
  - *`Rel` is insensitive to a length cast — prove by `subst`, not induction.*
    `Rel_cast {n m} (e : n = m) (s : Bytes n) : Rel d x (cast (congrArg Bytes e) s) ↔ Rel d x s`
    closes by `subst m; rfl` (the cast reduces to `rfl` and `Rel` is definitionally the same
    relation). Needed for `encode_rel`'s `seq` case, where `splice`'s suffix has type
    `Bytes (n₁ + n₂ - n₁)` (not definitionally `Bytes n₂`) and `Rel_cast` reconciles it with the
    inferred `Rel d₂ x₂ b₂`.
  - *The suffix/prefix extraction of a `splice` is `bdrop_splice`/`prepend_eq_of_eq_splice`.*
    `bdrop m (splice hm s₁ s₂) = s₂` closes by `unfold bdrop; rw [splice_apply]; unfold concat;
    rw [cast_fin_symm]; by_cases (i.val + m < m) <;> omega/simp`. `prepend_eq_of_eq_splice`
    (`s = splice hm s₁ s₂ → s = (Suffix.drop m s).prepend (cast … s₁)`) is the `decode_spec`
    `seq`-completeness reassociation; the `s₁` needs a `Nat.sub_sub_self hm` length-cast because
    `Suffix.prepend`'s prefix type is `Bytes (n - (n - m))`, not `Bytes m`.
  - *`(k+1)-1` reduces but `(k+1)-k` does not* (`Nat.sub` recurses on its first argument, so a
    bare `succ k` left of a variable `k` is stuck). Use `omega` for the `(k+1)-k = 1` cast proof
    (`Nat.sub_sub_self`/`Nat.succ_sub_one`/`Nat.add_sub_cancel_left n₁ n₂` are the named forms);
    the `Fin` single-byte index is `⟨0, Nat.zero_lt_succ k⟩`.
  - *`induction d` on a `Codec`/AST whose `iso` constructor changes the value type `α → β`
    generalizes the value `x` into the induction motive.* The IH then takes the value as an
    *explicit* first argument: `ih a hs`, `ih₁ x₁ h₁`, `ih₂ x₂ h₂` (NOT `ih hs` — that gives
    "expected α✝" because `x` is a generalized binder). This bites even the non-recursive-looking
    `iso`/`alt` cases, not just genuinely type-changing nodes like `many`.
  - *`⟨n, s⟩` dependent-pair (`Sigma`) notation is ambiguous in equality statements.* Comparing two
    `⟨n, s⟩` terms (`have hs : ⟨0, emptyBytes⟩ = ⟨n, s⟩`) fails "Invalid ⟨⟩ notation: expected type
    could not be determined" — annotate the RHS `(⟨n, s⟩ : Sigma fun k => Bytes k)` (or use
    `Sigma.mk n s`). The `encode : … → Option (Sigma fun n => Bytes n)` result needs this in every
    `encode_rel` case.
  - *An `ast`-shaped bidirectional law's `seq`-forward case needs the split reassociation `prepend_assoc`
    with a reconstruction hypothesis.* `(trans t₁ t₂).prepend (concat s₁ s₂) = t₁.prepend s₁` is
    **false** without `h : t₂.prepend s₂ = t₁.bytes` (the two sides read `t₂.bytes` vs `t₁.bytes` in
    the deep-suffix region); the `Rel`-`seq` witness also needs `cast_bytes_irrel` to commute two
    different `Nat`-sub proofs of the same length equality (`splice_add hm` vs `sub_sub_add`).

- 2026-10-15 — **The REAL cast-reduction trap with length-indexed carriers: the *inline*
  `show … by rw …; exact …` proof inside a `cast (congrArg F e)` is un-matchable — name it first.
  (Corrects the 2026-10-14 entry below, which misdiagnosed the cause as "opaque `omega` terms";
  `omega` itself is fine and constructive.) When a length-indexed `Bytes n := Fin n → UInt8`
  defines `splice`/`prepend` via `cast (congrArg Bytes <Nat-eq>)`, writing `<Nat-eq>` as an
  *inline* `show m + (n-m) = n by rw [Nat.add_comm]; exact Nat.sub_add_cancel hm` produces a
  `have`-wrapped proof term (`Eq.mpr`/`let`-bound) that **no** `rw`/`simp` can structurally unify
  against a cast-reduction lemma's `e : n = m` binder — `simp only [cast_bytes_val']` reports
  "made no progress", even with the bare-`Fin` LHS form. The fix is **not** a different lemma
  shape or proof-irrelevance gymnastics; it is to **hoist the proof into a named constant**:
  `theorem splice_add {n m} (hm : m ≤ n) : m + (n-m) = n := by rw [Nat.add_comm]; exact Nat.sub_add_cancel hm`
  and write `cast (congrArg Bytes (splice_add hm))`. A named `e` unifies cleanly; then the
  `.symm`-aware cast lemmas below fire. Corollaries for the same carrier:
  - *The `decode`/`encode` laws need a `.symm`-aware cast lemma for BOTH `Fin` and `Bytes`.*
    `splice`/`prepend` produce `cast (Eq.symm (congrArg Fin e)) i` and
    `cast (Eq.symm (congrArg Bytes e)) f`, but the stock lemmas match only the positive form
    `cast (congrArg Fin e) i`. Add `cast_fin_symm {n m} (e : m = n) (i : Fin n) :
    cast (Eq.symm (congrArg Fin e)) i = ⟨i.val, ·⟩` and the analogous `cast_bytes_val_symm`;
    both are `rfl` after `cases e` (a `Nat` equality `cases` cleanly — it is *not* the
    "`cases (Fin n = Fin m)` dependent-elimination failure" trap).
  - *Prove the clean `+`-associativity first, then transport.* A `concat`-associativity law
    `concat s₁ (concat s₂ s₃) = cast (congrArg Bytes (Nat.add_assoc a b c)) (concat (concat s₁ s₂) s₃)`
    closes directly by `apply Bytes.ext; intro i; unfold concat; rw [cast_bytes_val' (e := Nat.add_assoc a b c)];
    simp; by_cases; omega` (no `Nat.sub` at all). State the *derived* `prepend`/`splice` law in
    terms of this primitive rather than re-expanding `Nat.sub` casts.
  - *A `concat`/`prepend` associativity law over a `Suffix` (prefix+remainder) carrier needs a
    hypothesis linking the two remains.* `(trans t₁ t₂).prepend (concat s₁ s₂) = t₁.prepend s₁`
    is **false** without `h : t₂.prepend s₂ = t₁.bytes` — the suffix region reads `t₂.bytes` on
    one side and `t₁.bytes` on the other. If a composition law looks "obviously" true pointwise
    but won't close, check whether a reconstruction-of-the-middle hypothesis is missing (the
    analogue of an induction hypothesis leaking out of a `seq` decode); without it the two sides
    genuinely differ.

- 2026-10-14 — **The cast-argument matching trap: `rw`/`simp` cannot match a cast-reduction
  lemma's `e : n = m` binder against an opaque `omega`-generated proof, so normalize the
  proof first via proof irrelevance.** When a length-indexed carrier (`Bytes n := Fin n → UInt8`)
  makes `splice`/`concat`/`prepend` cast at `congrArg Bytes e` for arithmetic `e` (e.g.
  `Nat.sub_sub_self h`, `(n−m₁)+(m₁−m₂)=n−m₂`), the cast-reduction lemmas
  (`cast (congrArg Bytes e) f i = f ⟨i.val, ·⟩`) will **not** fire through `rw`/`simp` —
  `rw [cast_bytes_val']` leaves a `case e ⊢ n = m` side goal even when `e` is *in scope as a
  variable*, and `simp` reports "made no progress", because the lemma's `e` binder must be
  *structurally* unified with a proof term that `omega`/`by` made opaque. Two consequences:
  - *The bare-`Fin`-variable form is the right LHS, not the `⟨k, hk⟩` form.*
    `cast_bytes_val' {n m} (e : n = m) (f : Bytes n) (i : Fin m)` (a variable projection LHS)
    fires where `cast_bytes_val (… ⟨k, hk⟩)` cannot, because a compound index
    `⟨(cast … i).val − m, ·⟩` will not unify with `⟨k, hk⟩`. But it still needs `e` *named* —
    `rw [cast_bytes_val' (e := e)]` works only when `e` is a local variable.
  - *The real fix is to normalize the proof first, then reduce.* Use proof irrelevance for
    `Nat` equality (`Nat.eq_irrel {n m} (e₁ e₂ : n = m) : e₁ = e₂ := Subsingleton.elim e₁ e₂`,
    `[propext]`-only) to replace the opaque proof with a named one *in place*:
    `congr 2; exact Nat.eq_irrel e₁ e₂`, then `simp only [cast_bytes_val']`, then `omega`.
  This is the one general move that makes an entire family of cast-heavy length-indexed laws
  close mechanically — do not switch the representation to move the cast elsewhere (that
  trades a proof-side cost for a hot-path cost), and do not hand-`rcases` each `Nat` (unscalable).

- 2026-10-14 — **Length-indexed byte strings (`Fin n → UInt8`) as the single carrier: base-case
  type incoherence, the `splice`=cast-of-`concat` trick, and well-founded recursion on the
  type index.** When a `List α` spec becomes a length-indexed `Bytes n := Fin n → UInt8`, three
  non-obvious moves show up (all `[propext, Quot.sound]`-only):
  - *Base cases go type-incoherent.* `Rel (pure x₀) x s = (x = x₀ ∧ s = emptyBytes)` does not
    typecheck, because `s : Bytes n` vs `emptyBytes : Bytes 0` forces `n = 0`. Restate the base
    case as the *length predicate* (`pure ↦ x = x₀ ∧ n = 0`; `relRepeat [] ↦ n = 0`) or carry the
    cast (`byte ↦ ∃ h : n = 1, h ▸ s = single b`), and expose an `emptyBytes_unique`/
    `eq_empty_of_remaining_zero` transport lemma for the one place you need `s = emptyBytes`.
  - *The `seq` split should be defined as the cast of `concat`.*
    `splice {n m} (hm : m ≤ n) (s₁ : Bytes m) (s₂ : Bytes (n - m)) : Bytes n :=
    cast (congrArg Bytes (by rw [Nat.add_comm]; exact Nat.sub_add_cancel hm)) (concat s₁ s₂)`.
    Defining it *as the cast of `concat`* (not a bespoke `if i.val < m …`) makes `splice hm s₁ s₂
    = concat s₁ s₂` a one-line `splice_eq_concat`, so `encode_rel`'s `seq` case closes by
    definition. Note `cast` wants a *type* equality `Bytes … = Bytes …`, so wrap the `Nat` proof
    in `congrArg Bytes` (and its witness is `Nat.sub_add_cancel`, not `omega` over `m + (n-m) = n`).
  - *Well-founded recursion moves to the type index `n`.* `decodeRepeat`/`decodeFull` recurse on
    `n` (the length of `s : Bytes n`), so the `fix` runs over `Sigma fun n => Bytes n` with measure
    `.1`, and the *proof* uses `Nat.strongRecOn n` (stdlib strong induction — `Nat.strong_induction_on`
    does **not** exist) after `revert xs s` so `s : Bytes n` stays under the `∀` in a type-correct
    motive. `dsimp` often turns a named `dite` into a plain `ite`; `split_ifs` no longer exists in
    Lean 4.34 and `if_neg` is deprecated (`ite_eq_right` is the replacement), and `rw [ite_eq_right hn]`
    can still split into a spurious `inl.refl` — prefer `cases n` on the `Nat` when the goal's `n` must
    rewrite hypotheses too.

- 2026-10-13 — **"Work faster" = carrier swap, not a compiler or more FFI; `USize` is the
  scalar you already have.** The dominant cost in a `List`-returning decoder is the `List`
  cons cells + bignum `Nat` boxes at the *API edge*, not the byte loop (which stdlib
  `@[extern]`s already make `memcpy`-fast). Two failed moves confirm it: (1) a
  `@[extern]` C "fast path" that only re-wrapped stdlib externs gave no speedup (the loop
  was already C); (2) a "new GC-less backend" plan (`Nat→size_t`, `WellFounded.fix`→loop)
  was architected-wrong — bignum `Nat` is an `lean_object *` not a scalar, and
  `WellFounded.fix` threads a higher-order `ih` (backtracking search, not a tail loop), so
  erasing them is a *semantic* change the IR cannot express. The fix is a **packed,
  `USize`-indexed, slice/`ByteArray`-span-returning surface** — because `USize` *is* a
  scalar, the existing `EmitC` already emits a `size_t` loop, so you get near-C with **no
  backend and no new trust**, and the refinement to the `List` spec is the same
  `[propext, Quot.sound]`-only lemma you already write for a carrier swap. (Generic; see
  §7.)

- 2026-10-12 — **Choose the `@[extern]` *body* so the contract law is `rfl`-provable
  `[propext, Quot.sound]`-only; don't route it through a stdlib lemma that pulls in
  `Classical.choice`.** When an `@[extern]` primitive's *executed* C is a tight loop but its
  Lean body must still elaborate (so refinement lemmas hold), the body can be a *different,
  simpler, `rfl`-reducible* term with the same meaning — the C (code-generated) and the body
  (proof-only) need only *agree*. Concretely: `byteSlice a i := a.extract i a.size` forces the
  contract lemma `(byteSlice a i).data.toList = a.data.toList.drop i` through stdlib
  `Array.toList_extract`/`List.toArray_drop`, which depend on `[propext, Classical.choice,
  Quot.sound]` (`omega` over `Nat.min`/`sub`). Writing the body `ByteArray.mk
  ((a.data.toList.drop i).toArray)` makes the same contract `rfl` (over the reducible
  `Array`/`List` pair) — `[propext, Quot.sound]`-only, no `Classical.choice`. Corollary:
  `omega` itself is constructive and does *not* add `Classical.choice` (the existing
  `DecodeByteArray` laws use it and stay `[propext, Quot.sound]`) — it is specific stdlib
  `Array`↔`List` `extract` lemmas that do. Also: `ByteArray.size` is `| ⟨bs⟩ => bs.size`
  (a pattern match), so `(ByteArray.mk x).size` does not `simp`-reduce — use
  `unfold ByteArray.size` (or `ByteArray.size_data : a.data.size = a.size`).

- 2026-10-12 — **Linking hand-written `@[extern]` C into a `lean_exe`: script
  `lakefile.lean`, a `target + buildLeanO` object, and `moreLinkObjs`.** The TOML
  lakefile cannot express a custom C *compile* step (`extern_lib` needs a Lean-side
  `getPath`); a script lakefile can declare `target x (pkg) : FilePath := do buildLeanO
  oFile (Job.pure srcFile)` and attach it via `lean_exe … where moreLinkObjs := #[x]`.
  Non-obvious: the `target` package binder defaults to `_` (name it `(pkg)` to use
  `pkg.dir`/`pkg.buildDir`); the TOML `defaultTargets` maps to `LakefileConfig`, *not*
  `PackageConfig` — in a `.lean` lakefile use `@[default_target]` on the lib instead;
  `buildLeanO` compiles with `leanc` (gives `-I …/include` for `lean.h` + flags), and
  `leanc` self-resolves its clang without `cc` on `PATH`; `Job.pure` (not a bare path) is
  the src arg, and the `SpawnM (Job FilePath)` body lifts to `FetchM` via the `MonadLift`
  chain. A flake/`default.nix` `src = ./.` uses the *git tree*, so a new `lakefile.lean`
  must be tracked before `nix build` sees it. (Generic; see also the `@[extern]` entry
  below.)
  library; and "GC-less C" = a type-mapping/compiler-backend decision, not a runtime.**
  Lean's only C generator (`Lean.Compiler.LCNF.EmitC`) boxes *everything* — `Nat`→bignum
  `lean_object *` (`lean_nat_add`/`lean_nat_dec_lt`), `List`→cons cells with
  `lean_inc_ref`/`lean_dec_ref`, closures→`lean_alloc_closure`; `IR/EmitLLVM.lean` is the
  other backend, and there is no stock unboxed-C target. Two `@[extern]` shapes exist:
  (1) `opaque`/`constant` (no body, pure trust), (2) `def` with an *elaborating* body
  (stdlib `ByteArray.get` pattern — body reduces for proofs, codegen calls the C symbol).
  Shape (2) keeps refinement lemmas `[propext, Quot.sound]`-only and the C is a *named trust
  seam* (F\*/KaRaMeL `// primitive` posture). "No GC / no runtime C" is what KaRaMeL emits:
  `krmllib.h` (macros+typedefs only), machine ints→`uint8_t`/`uint32_t`, `Prims_string`→
  `const char *`, byte slice→`{uint32_t length; const char *data;}`, heap=libc `malloc`/`free`,
  **no GC anywhere** — the mechanism is primitive *type mapping*, which is `@[extern]` applied
  to types. A real Lean equivalent = a new backend (`EmitNoGC`/`EmitCStar` + boxing pass +
  driver flag) at the `EmitC`/`EmitLLVM` seam (a compiler backend, not a `lake` lib); the
  `@[extern]` fast path (shape 2) is the cheaper stopgap that lands first and validates the
  `memchr` baseline + `(ptr,len)` slice representation before the full backend is built.
  (Source studied: `../fstar` `v2026.09.20` Pulse C lib `Pulse.C.Types.*`; `../karamel`
  `DESIGN.md`/`include/krmllib/*`/`src/AstToCStar.ml`.)
- 2026-10-11 — **A `lean_exe` only generates a C `main` when its `main` is at the
  top level (root namespace), not inside a `namespace`.** Lake's executable target
  links the C `main`/`_lean_main` entry from a `main : IO Unit` bound in the module's
  *root* namespace; a `main` declared inside `namespace Foo` compiles to
  `lp_Foo_main___boxed` with no `_lean_main` symbol, and the link fails `entry point
  (_main) undefined`. Put the `main` at top level and qualify the helpers it calls
  (`Foo.doIt`), or `open Foo in`. This is distinct from the library build, which
  links no entry point and never surfaces the issue.
- 2026-10-11 — **An "efficient decoder" can be planned in provability tiers.** When a
  backtracking/list decoder must become faster *without* changing its denotation,
  split the work by proof cost: **Tier A** = list-fusion + a full-consumption
  `Option` specialization of the repetition decoder, whose equality to the spec
  closes by `List` equations + `WellFounded.fix_eq` (the same machinery the naïeve
  spec already uses); **Tier B** = a memoizing/chart (DP over positions), which needs
  a numbering of `(sub-description, position)` and an equality proof likely beyond
  `rfl`/`simp`. Ship Tier A (provable, `[propext, Quot.sound]`) first; keep Tier B a
  separate change rather than stalling the practical win on the hard proof. A
  `HashMap`-keyed memoization is the wrong first move: `Codec` is a structural value
  (no cheap nominal identity) and `Std.HashMap` brings `BEq`/`Hashable`/FFI
  obligations that break the `rfl`/`simp` style.
- 2026-10-11 — **Prefer an explicit `match` over `Option.map` for a transport
  definition whose law you must `simp`/`rfl`; there is no `Option.map_eq_some` in
  core.** `Option.map f o = some b ↔ ∃ a, o = some a ∧ b = f a` has no named lemma
  and does not `rfl` (the `some` case leaves `f a = b ↔ b = f a`); write
  `match o with | none => none | some a => some (f a)` instead, so the transport
  law (`o.map f = some b ↔ …`) closes by `cases o <;> simp` + `rw [eq_comm]`.
- 2026-10-11 — **`ByteArray.toList` is opacity, but `ByteArray.data` (an `Array`)
  reduces; route the transport through `.data.toList`, never `.toList`.** When
  transporting a `List`-proved core onto a `ByteArray`, `(ByteArray.mk a).toList`
  does **not** reduce to `a.toList` (FFI), but `(ByteArray.mk a).data.toList` is
  `rfl` (because `ByteArray.data` is the stored `Array`, and `Array.toList` is
  `self.1`). Writing `toBytes b := b.byteArray.data.toList` makes the round-trip
  `toBytes (ofBytes l) = l` close by `rfl`. Prefer wrapping the *reducible* `Array`
  over the `ByteArray` for any law you must `simp`/`rfl`.
- 2026-10-11 — **A `structure` newtype auto-generates no `ext` in one-field form;
  use `congrArg Mk` + the field's own extensionality.** `structure Foo where a : Nat`
  yields no `Foo.ext` constant; prove `x = y` as `congrArg Foo.mk (…)` (or `cases`
  both sides). And `abbrev X := List UInt8` without an explicit `: Type` can fail
  to infer — write `abbrev X : Type := List UInt8`.

- 2026-10-11 — **`/-!`/`/--` block comments are *terminated* by the byte pair
  `-/`, even nested inline.** The text `left-/right-associative` (a `-` immediately
  before `/`) closes the enclosing doc comment at that point, so the rest of the
  line parses as code (`unexpected identifier` at the `/`). Avoid a `-` directly
  before `/` in doc/`-!` text — write `left- or right-associative`, `left/right`,
  `a and b`, etc. This is the same lexer rule as closing a `/-` comment; doc
  comments are not special-cased.
- 2026-10-11 — **`subst` eliminates the variable on the *right* of the equality,
  even when both sides are locals.** For `h : ax = x₀` (both introduced by
  `cases`/`rcases`), `subst h` substitutes `x₀ := ax` (kills `x₀`), surprising you
  when `x₀` is a case-analysis variable you wanted to keep. To control direction
  deterministically, derive the projections with `congrArg` and `cases` them:
  `have h1 : ax = x₀ := congrArg Prod.fst h; cases h1` substitutes `ax := x₀` and
  keeps `x₀`. For a cons/cons equality `ax :: rest' = x₀ :: rest`, `cases h1`
  substitutes *both* `ax := x₀` and `rest' := rest` in one step (via `noConfusion`),
  unlike `subst` which would require two `injection` + `subst` rounds and still get
  the direction wrong.
- 2026-10-11 — **`rw` does *not* beta-reduce a `match`, so rewriting a scrutinee
  leaves the arm's pattern binders shadowing yours; use `simp` to reduce.** After
  `cases h : (foldl …).unapply a` and `rw [h] at he`, a goal
  `(match some (a₀, ops) with | some (a₀, ops) => …endcode arg a₀… ) = some s`
  keeps the *arm's* `a₀`/`ops` (shadowing your `rcases`-bound ones), so a later
  `rw [ha : encode arg a₀ = …] at he` finds "no occurrence". `simp [h] at he`
  (not `rw`) additionally reduces the `match` on the constructor literal, which
  beta-substitutes the scrutinee into the arm and unshadowes the binders. In
  `cases <h> : e`, the `h` records `e = constructor` but does **not** rewrite `e`
  anywhere (not in hypotheses, not in the goal) — rewrite/simp it yourself.
- 2026-10-11 — `partial def` generates **no equation and cannot be unfolded**:
  `#check f.eq_1` is unknown and `unfold f` fails, so a denotation built by
  `match` on a `partial` description value (`Rel (many p)`) is irreducibly stuck —
  an equality like `Rel (many p) xs s ↔ relRepeat (Rel p) xs s` is *unprovable*.
  The honest reading of "derived recursive combinator, total as a denotation" is:
  the denotation is a separate total relation (`relRepeat`), never `Rel` applied to
  a `partial` `Codec`. (Follow-up: the remedy that actually ships is to delete the
  `partial` value and expose *three* total functions — a relation, a well-founded
  decoder, and a structural encoder — rather than any `Codec`-typed value.)
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
