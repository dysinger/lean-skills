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
2. **Scalar indices.** `USize` (and `UInt64`/`UInt8`/…) **is** a scalar in Lean's
   IR; bignum `Nat` is an `lean_object *`. A function indexed by `USize` already
   codegens to a `size_t`/`ulong` loop under the *existing* `EmitC` — near-C with
   no representation fiction. This is the decisive fact the "erase `Nat → size_t`"
   compiler plan misses: you get unboxed indices by *typing them `USize` in source*,
   not by asking a backend to erase a bignum.
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

## Changelog

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
