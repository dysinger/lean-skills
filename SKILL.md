---
name: lean
description: Supplements the official `lean4` skill with our own accumulated *generic* Lean 4 / Lake learnings — module & namespace layout, lakefile roots, the `Classical.choice` leak catalogue, `if`/`ite`/`Bool`-goal and "motive is not type correct" recipes, `partial`/coinductive definitions, notation collisions, and performance-measurement discipline. Use alongside `lean4`. Holds only deltas, never duplicates its content, and only the reusable half — each project keeps its domain-specific notes in its own repository.
license: CC-BY-4.0
---

# Lean 4 — Project Learnings (supplement to `lean4`)

This is **our own accumulating notebook** of Lean 4 / Lake lessons that are *not*
in the official skill. It augments, never replaces, the official skill:

- Official theorem-proving skill: [`lean4`](../lean4-skills/plugins/lean4/skills/lean4/SKILL.md)
- Official mathlib/setup skills: [`leanprover`](../leanprover/)

**Read this file after** the official `lean4` skill.

## Precedence (read this before the rest)

The two files disagree about one thing, and it is not negotiable in either
direction, so the order is stated explicitly:

1. **This file's axiom gate wins over everything**, including the official skill.
   The official `lean4` *Quality Gate* defines a complete proof as using "only
   standard axioms (`propext`, `Classical.choice`, `Quot.sound`)". **This project
   does not permit `Classical.choice` anywhere.** Where the two conflict, this
   file wins — the axiom discipline is the stricter, project-specific rule, and it
   is the reason this file exists.
2. **The official skill wins on proof engineering, search, and the build ladder** —
   how to fill a `sorry`, how to search mathlib, `lean_goal`/LSP usage, the
   `lake env lean` → `lake build` verification order. Follow it there; this file
   only adds deltas.
3. **This file's layout / module-system / library-authorship / performance notes
   apply as written** where the official skill is silent.

Earlier revisions of this file said only "the official skill's proof-engineering
guidance wins", which silently made the axiom gate overridable — the exact failure
mode the gate exists to prevent. If you find a third kind of conflict, resolve it
in that order and record the ruling here.

---

## When to read what

| Question | Read |
|---|---|
| How do I fill a `sorry`, search mathlib, debug a type mismatch? | the official [`lean4`](../lean4-skills/plugins/lean4/skills/lean4/SKILL.md) |
| **An `if`/`ite`/`Bool`-match goal won't close (`split_ifs` is gone; `if_pos`/`if_neg` deprecated)** | [§2a `if` / `ite` / `Bool` goals](#2a-if--ite--bool-goals-stdlib-only--no-mathlib) |
| **`#print axioms` shows `Classical.choice` and I do not know which spelling caused it** | [§2b the leak catalogue](#2b-classicalchoice-leak-catalogue-one-table) — one table, source → probe → clean spelling. Consult this before any dated Append entry. |
| **`rw` fails with "motive is not type correct"** | [§2c change the statement, not the tactic](#2c-motive-is-not-type-correct--change-the-statement-not-the-tactic) |
| How do I lay out a *library* package's namespace, `lakefile`, roots? | [§1 Module & namespace layout](#1-module--namespace-layout) |
| `ByteArray` proofs won't reduce / `simp` stalls on a primitive | [§2 Proving over primitives](#2-proving-over-primitives) — and note the version qualifier on the `ByteArray` claim |
| A `partial def`/recursive combinator won't typecheck | [§3 `partial`, coinduction, nonempty](#3-partial-coinduction-nonempty) |
| Notation collision with a reserved token (`\|`, `*`, `$`, `open`) | [§4 Notation & keyword collisions](#4-notation--keyword-collisions) |
| `deriving Repr` fails / `#eval` says "unable to synthesize `MonadEval`" | [§5 Library ergonomics (Repr / #eval)](#5-library-ergonomics-repr--eval) |
| Linking hand-written C into a `lean_exe`; script `lakefile` gotchas; making `-DwarningAsError` stick | [§6 Lake build customization](#6-lake-build-customization-extern-c-ffi-link-script-lakefile) |
| How do I make a parser/codec *fast*? | [§7 Work faster (carrier swap > FFI > compiler)](#7-work-faster-carrier-swap--ffi--compiler-and-lean-on-usize). Quote **ns/element against a measured pure-Lean floor**, never a `×` against `memcpy` — that is a category error for a per-element parser. |
| `rw` fails with "motive is not type correct" on a `Fin`-indexed definition | you are rewriting at the wrong index — see [§2c](#2c-motive-is-not-type-correct--change-the-statement-not-the-tactic); prove a `…_cast` / pointwise lemma instead |
| A theorem needs two inductions that each depend on the other at a smaller measure | Append: "state them as one conjunction and induct once" |
| `decreasing_by` won't close / `rename_i` gives "too many variable names" | Append: "mirror the working sibling" — copy the file's existing mutual pair, thread the `if` guard as an explicit hypothesis |
| Two `List.attach` lists should correspond and `rw` on `.attach` fails | Append: "read both positionally through `List.getElem?_attach`" |
| How do I time Lean code and trust the number? | Append: the timing entries — a pure call in a loop gets hoisted, folds get deleted; one fresh call per sample, median, data-dependent sink |

The **Append** is a reverse-chronological pile of measured lessons (topic index: axiom
hygiene · `omega` · `simp`/`rw` · cast/`Fin` · carriers & performance · proof process).
Its **one authoritative summary is §2b's leak table** — the dated entries are the
raw record, not the place to start.

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

**Block comments *nest*, so an unmatched `/-` or a `-/` inside a doc comment cuts
it short or swallows the rest of the file.** The `-/` half is the one that bites
when writing prose: `left-/right-associative` inside a doc closes the comment at
the `-/`, and the remainder of the line parses as code. The `/-` half is just as
fatal in the other direction — writing `x/-y` to *avoid* the first problem opens
a nested comment that never closes.

Write `left- or right-associative`, never `left-/right` or `x/-y`. A space
separates them safely (`- /` is fine); only the adjacent pair is the trap. Same
rule inside `/-! … -/` module docs.

---

## 2. Proving over primitives

### 2a. `if` / `ite` / `Bool` goals (stdlib only — no mathlib)

These four spellings account for most of the avoidable debugging time on an
`if`-heavy goal. None of the mathlib-era recipes transfer to a stdlib-only build.

**`split_ifs` does not exist on stdlib 4.34** (`unknown tactic`). Every recipe
copied from a mathlib-era codebase that says `split_ifs with hp` will fail. Use,
by preference:

1. `by_cases h : P` (or `cases h : P` when the equation itself is wanted), then
   `simp only [h, ite_true]` / `ite_false`;
2. `exact ite_eq_left h` / `ite_eq_right h` when you already hold the fact (see
   the next bullet — these are *applied*, not rewrites);
3. `cases h : P <;> simp_all` when both branches are cheap.

**`if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right`, and the
replacements are *applied*.** Both halves are deprecated (not just `if_neg`), so
a repo-wide habit emits warnings that a `-DwarningAsError` gate turns into build
failures. The shapes are
`ite_eq_left : c → (if c then t else e) = t` and
`ite_eq_right : ¬c → (if c then t else e) = e` — functions of a proof argument.
Write `exact ite_eq_left h`, or
`rw [show (if P then a else b) = a from ite_eq_left h]`. Bare
`rw [ite_eq_left]` and `.mpr` **do not work**: there is no `Iff` to project, so
`.mpr` fails with `Invalid field 'mpr'` on an expression of function type.

**A `match`/`if` on a `Bool` in the goal is a dependent match** A `match`/`if` on a `Bool` *in the goal*, with `h : b = true` in context, is a
*dependent* match — and the two obvious fixes both fail.

```lean
theorem tl (b : Bool) (h : b = true) :
    (match b with | true => (1:Nat) = 1 | false => (0:Nat) = 0) = True := by
  subst h; rfl
-- error: Tactic `rfl` failed: The left-hand side
--   match true, ⋯ with | true, h => 1 = 1 | false, h => 0 = 0
-- is not definitionally equal to the right-hand side  True

theorem td (b : Bool) (h : b = true) : (match b with | true => True | false => True) := by
  cases b
-- error: Dependent elimination failed: Type mismatch when solving this alternative:
--   motive (true = true) but is expected to have type  motive x✝
```

`cases b <;> simp_all` closes both. The alternatives: restate so the match is not
dependent (move the discriminee into a hypothesis), split the claim into a
`_true`/`_false` lemma pair, or write `if h : p then …` so the fact is in the
branch. **Note the failure mode is *not* a `Classical.choice` leak** — it is
dependent elimination, so `#print axioms` will not hint at it. Do not go looking
for a leak here.

### 2b. `Classical.choice` leak catalogue (one table)

The material below is the whole of what this project has learned about
`Classical.choice` appearing in a law that should be `[propext, Quot.sound]`-only.
It used to be scattered across seven dated entries; consult **this table first**, and
add a row (not a new scattered entry) when you find a new shape.

| leak source | how it looks | clean spelling |
|---|---|---|
| **`decide_eq_true (by omega)` on a *disjunction*** | `decide (A ∨ B) = true` closed by `decide_eq_true (by omega)`; `omega` case-splits the disjunction, pulling in choice. Reports `[propext, Classical.choice, Quot.sound]`. | Build the disjunct: `decide_eq_true (Or.inl ⟨a, b⟩)` / `Or.inr h`, and let `omega` close only the arithmetic leaf. Probe: `theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) : decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true := decide_eq_true (by omega)` — dirty. Same theorem with `decide_eq_true (Or.inr h)` is clean. |
| **Dependent `cases`/`match` on a term whose length *equation* is in context** (`bs.length = 1 ∨ bs.length = 2`, `ds.length = k`) | leaks even when every cited lemma is clean | Restate the hypothesis numerically (`1 ≤ bs.length`, `bs.length ≤ 2`) or derive the index from the term, so the match stays non-dependent. **Bisection is goal-shaped:** shrinking the body to `⟨_, rfl⟩` works only when the goal is a sigma/`∃`; on a `decide … = true` goal it does not even typecheck, so prefer rewriting the *proof shape*. |
| **`split` on a `match`-with-a-named-equation**, and **an anonymous `by <tactic>` proof inside a `match` arm** | the unfolding lemma is dirty while its statement and every lemma it cites are clean | Make the bound an **ordinary parameter** rather than something derived by a tactic inside the arm (a subtype's `≤` field passed straight through), after which the `conv => lhs; rw [f.eq_def]; dsimp only; rw [h]` recipe works. Diagnostic: `#print axioms` each cited lemma in turn; if all are clean, the arm or `split` itself is the source. |
| **`simp`/`rw` reaching a classical lemmas' route** — e.g. `simp [f]` that passes through `List.length_ofFn` | looks like an innocent simp-set choice | Replace with the direct lemma: `show (List.ofFn s).length = n; exact List.length_ofFn` reports `[propext]` where `simp [f]` reported `[propext, Classical.choice, Quot.sound]`. Common at a **transport lemma**, which is exactly where it recurs. |
| **`omega` on a `Nat`-subtraction trichotomy**, or **`omega` asked to derive a modulo *existential*** | `omega` picks a branch classically | Case-split on `Nat.le_total` first, and state the *equational* form: `n = 4 * k → n % 4 = 0` **is** in `omega`'s fragment and closes clean; `∃ k, n = 4 * k` from `n % 4 = 0` is not, and `omega` cannot *use* a modulo hypothesis. |
| **`Array.extract`'s readback** (`Array.toList_extract`, `Array.getElem_extract`) | both report `[propext, Classical.choice, Quot.sound]` on 4.34, so *every* route that reads an `Array.extract` back as a list inherits it | There is no clean route: design around it. `Array.ext'` is innocent — check the individual lemma, not just the tactic. Honest fallback when the fast transport is worth having is a recorded decision plus a measurement, never a weakened statement and never a `sorry`. |

**Two rules that keep this table honest.**

- **An *isolated* probe is often clean while the in-context use leaks.** The leak
  needs the surrounding generated context (a `_proof_*`, a `match` arm, a
  recursor's motive). So a clean `#print axioms` on a hand-written minimal
  restatement does **not** refute an entry here — reproduce it in place. The
  converse also holds: a dirty result on an isolated probe (the first row) is a
  genuine leak.

**`Option.ne_none_iff_exists` gives `some x = o`, not `o = some x`.** After
`rcases … with ⟨x, h⟩`, apply `h.symm` before `simp [encode, …]` to reduce a
`match o with | some x => …`.

**`ByteArray` operations: which ones reduce depends on the version — check before
reaching for `List UInt8`.** On **Lean 4.32+** (including 4.34, the version this
file is written against): `ByteArray.append_assoc` exists
(`a ++ b ++ c = a ++ (b ++ c)`), and `(a.push b).data = a.data.push b` is `rfl`
(that is the `data_push`-family projection, not a claim that `.push` itself is
transparent). On **Lean ≤ 4.30** this was *not* so: `ByteArray.append`, `get!`,
`extract` and `size` were FFI/`copySlice`-backed and did **not** unfold under
`simp`/`rfl`, so `(a ++ b) ++ c = a ++ (b ++ c)` had no mechanical proof, because
`ByteArray.ext` reduces to element-wise `Array` goals rather than `List` ones.

Do not generalise the ≤ 4.30 limitation forward. Before you model a sequence as
`List UInt8` "because `ByteArray` won't reduce", run `#check` on the specific
lemma you need (`ByteArray.append_assoc`, `ByteArray.data_*`, `Array.extract`
lemmas) — on a current toolchain most of them are there, and only the genuinely
opaque ones (notably the `extract` readback, which pulls in `Classical.choice`;
see the leak catalogue) force the `List` detour.

**Rule:** when a law must be *proved* (`rfl`/`simp`/`induction` only), check for
the `Array`/`ByteArray` lemma **first** and fall back to a `List UInt8` model only
for the operations that are genuinely opaque. In `Option`/`Except` code, write
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

### 2c. "Motive is not type correct" — change the *statement*, not the tactic

A rewrite fails when it must abstract over a term that other hypotheses or the
goal's own type depend on. The three shapes below account for nearly all of it,
and the fix is always structural.

1. **Rewriting under a `List.attach`.** `l.attach` carries a `Membership` proof
   per element, so any term mentioning `x ∈ l` depends on `l`; `rw [h]` on `l`
   then fails. Fix: take the list as a **parameter** and `cases`/`induction` on
   it — never rewrite it. (`cases d` then
   `simp only [List.attach_cons, List.cons.injEq, Subtype.mk.injEq]` reduces both
   sides, and the pair is then proved by transitivity.)
2. **Rewriting an index that a dependent type packs.** `rw [hk]` inside
   `f ⟨n, s⟩` cannot abstract because `s : Bytes n` mentions `n`. Fix: state the
   lemma with the index **abstract and the equality as a hypothesis**
   (`∀ k t, k = 0 → f k t = …`), so the caller supplies the arithmetic and no
   in-place rewrite is needed.
3. **Rewriting a length inside an indexed type.** `T (n - m)` and `T k` with
   `k = n - m` are numerically equal but **not definitionally equal in the
   `T (·)` position**, so an induction hypothesis at one cannot be used at the
   other. Fix: write the *lemma's statement* using the form the recursor actually
   produces; the mismatch then never arises. Do not try to transport it.
4. **A `simp only` goal containing a dependent `if`/`dite`.** `simp only [f, g]`
   unfolds `f`/`g` **inside the scrutinee's type**: `if h : i.val < f n then a else b`
   becomes `if h : i.val < 0 then a else b`. Verified minimal reproducer — with
   `def mylen (n : Nat) : Nat := 0`, the goal `(if h : i.val < mylen n then i.val
   else 0) = i.val` shows `i.val < 0` after `simp only [mylen]`. A lemma stated at
   the `f n`-spelling still has the right *term*, but the goal no longer resembles
   it, so `rw` reports "did not find the pattern" while the hypothesis you hold is
   literally the right equation. Fix: prefer `unfold` + targeted `rw` (or `conv`)
   over `simp only` in such a goal, or state the helper **at the variable length**
   (`∀ k, …`, with `k := f n` supplied by the caller) so nothing gets rewritten
   inside a scrutinee's type.

**Diagnose with a failing `example`, not with a remembered error message.** When a
rewrite is stuck, the first thing to write is a two-line `example` isolating the
mechanism you think is responsible, asserted with `fail_if_success`, and check
that it *does* fail. A plausible root cause is a hypothesis with a cheap test;
"the eliminator rejects a projection" or "`cases` cannot see through a
hypothesis" sound authoritative and are frequently false. Two sessions of a
stuck proof were spent building on a diagnosis that one `example` refuted.

**Corollary: rewrite one side at a time.** `conv => rhs; rw [eq]` reaches the
conclusion without touching a hypothesis whose type depends on the term, and is
often the difference between a five-line proof and an unfinishable one.

**For an indexed carrier, state equalities *pointwise*.** A carrier-level lemma
(`t.bytes = drop …`) forces a cast at the index and that cast is opaque to `rw`;
stating the same fact as `t.bytes i = s ⟨i.val + …, _⟩` for `i : Fin t.remaining`
has **no cast anywhere**, so every downstream `rw` fires.

**Do not develop proofs outside the repo.** A working directory is not a version
control system, a build gate, or a handoff: a `/tmp` scratch file is invisible to
`git`, identical-looking whether finished or not, and one reboot loses it. Write
new theorems into the real source and let the unfinished one carry a `sorry` that
**fails the build** — the failing gate is the honest, durable marker of exactly
what is left. Use a scratch file only when the library genuinely does not build
and you must iterate against a *built* dependency; delete it the moment the real
build is green.

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

**A `many` constructor carrying a *denotational* productivity witness is un-implementable —
derive `many`, don't construct it.** Trying `many {α} (p : Codec α) (h : Productive p) :
Codec (List α)` with `Productive p := ∀ x n s, Rel p x s → n ≠ 0` (or `ConsumesByte`, which
mentions `decode`) creates the definition-order cycle `Codec → (witness) → Rel/decode → Codec`:
the constructor field mentions `Rel`/`decode`, both of which structurally recurse on `Codec`.
Lean rejects the two escapes: mixing a `def` with an `inductive` in a `mutual` block is forbidden,
and a `mutual inductive Codec (Type → Type 1) + Rel (… → Prop)` is rejected by the universe
check ("All inductive types declared in the same `mutual` block must belong to the same type
universe"). A *syntactic* productivity `def` recursing on `Codec` has the identical
`Codec → productive → Codec` cycle. **Resolution (paper §3.4 + F\* `satisfy_many0`):** `many`
is a *derived* recursive combinator (`many p = nil $ pure () | cons $ p ∗ many p`), never an AST
node; realize it as the **parameterized `relRepeat R` / `decodeRepeat p h` / `encodeRepeat p`
triple**, and surface a concrete format as a **first-class run value** (a `structure` bundling
`elem : Codec α` + `step : ConsumesByte elem`, with `decode`/`encode`/`rel` inherited from the
proved repetition) rather than a bespoke per-format function. Do **not** re-fight this: a
`many`-as-constructor is not a Lean expressibility gap to overcome, it is the wrong shape, which
the paper and the F\* reference both avoid by deriving repetition.

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
- **`-DwarningAsError=true` cannot be passed on the `lake build` command line —
  put it in `moreLeanArgs` on the `lean_lib`.** `lake build -DwarningAsError=true`
  fails with `unknown short option '-D'`, and `lake build -- -D…` treats the flag as
  a *target*. Neither `LEAN_OPTS` nor `-K` is forwarded to the compiler invocation
  (verify with `lake build -v` and read the `trace: .> LEAN_PATH=… lean …` line).

  ```lean
  @[default_target]
  lean_lib foo where
    roots := #[`Foo]
    moreLeanArgs := #["-DwarningAsError=true"]
  ```

  This is also the *better* place for a proof gate than a Nix derivation flag: the
  setting rides on the **library**, so every consumer that compiles it (an `exe`,
  a sandboxed `nix build` check) inherits it and there is no way to build
  unguarded. Confirm it took effect from the `trace:` line showing
  `lean -DwarningAsError=true …`.
- **`lake build` only *warns* on `sorry`; it does not fail.** `declaration uses
  'sorry'` is a warning, so a CI "proof gate" that is a plain `lake build` goes
  green with an incomplete proof. The `warningAsError` setting above is what makes
  the compiler the authority — and it also catches `admit` and tactic-generated
  `sorryAx`, which a `grep`-based gate would miss. Prove the gate is load-bearing:
  stub one theorem to `sorry`, confirm the build fails *and* names the declaration,
  then restore.

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
2. **Scalar indices — with the field-position caveat.** Bignum `Nat` is always an
   `lean_object *`. **`UInt64`/`UInt32` arithmetic does *not* box**: a function
   typed in `UInt64` gets a `uint64_t` C prototype and
   `lean_uint64_add`/`_mul`/`_lt`, and Lean emits a *separate* `…___boxed`
   wrapper for the polymorphic boundary. Verified on 4.34.1 with
   `def sum64 (n : UInt64) : UInt64 := n + 1`, whose C is
   `LEAN_EXPORT uint64_t l_sum64(uint64_t);` …
   `v___x_3_ = lean_uint64_add(v_n_1_, v___x_2_);` plus
   `l_sum64___boxed(lean_object*)`. So `UInt64` is the *one* fixed-width type that
   stays scalar through arithmetic — it re-boxes only when a value crosses a
   polymorphic/`Option`/`Prod` boundary.

   `USize` is a scalar in *argument* position (and as an index into
   `ByteArray.uget`/`uset` → `lean_byte_array_uget(..., size_t, uint8_t)`), but
   the moment it is *returned/stored* in a `Prod`/`Option` field it re-boxes
   (`lean_box_usize`), and `USize.toNat` at each boundary adds a bignum
   conversion — so a result-returning interpreter (`Option (α × USize)`) does
   **not** stay unboxed end-to-end. Rewriting a parser to thread a `USize` cursor
   made it *slower* for exactly this reason. **Net:** `USize`
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

**Step 0 — before any of the above: decompose, then ask whether the *control
flow* or the *result type* is the cost.** Measured hierarchy of the same work
(one array read per element, against a `memcpy` floor of 1×): plain `Array.get` loop
~**200×** → accumulating cursor loop ~**250×** → per-step `List` **47×** → per-step
**chained lazy closures** **~10^5×**. So single-digit multiples of C are normal in
pure Lean, and anything far above that is a design choice you can name. That
"single-digit multiples of C" claim is now **measured against a real C parser**, not
inferred from a `memcpy` ratio: for a per-element decode (one value per byte, `n` =
4096, burst medians) a hand-written C parser doing the same job — including
materialising the `n`-element result array — ran at **7.0 / 6.9 ns/step** against the
pure-Lean decoder's **28.6 / 27.0 ns/step**, i.e. **~4x** across two runs. Two things
that measurement settles and one it corrects: a `memcpy` ratio is a **category error**
here (a copy moves a byte, a parser does per-element work), so no "x off C" figure may
be derived from one; most of *both* sides' time is **result materialisation**, not
parsing, which is why the carrier swap in step 1 is the biggest single lever; and the
same run showed the *bare cursor loop* (2.5 ns/step, no output array) running **faster
than the C reference** — a floor is not a C ratio, and a floor below the reference is
expected whenever the reference is allocating and the loop is not. **Re-measure
these before quoting them** — an earlier revision of this paragraph carried 8.5×/6.2×
that no lane ever printed (see the entry on measurement integrity in the Append).
Time the components in isolation before rearchitecting anything: a super-linear
composite whose *parts* are linear means the cost is in how they are **composed**,
not in any one of them. Two shapes account for most of it, and they look nothing
alike — (a) a **lazy carrier fed its own output**, where `drop k s` returns a
closure over `s` and passing it back composes closures so a read at depth `k`
costs `k` (measured 92,876 µs chained vs 139 µs re-rooted at n=4096, **668×**);
(b) a **`List` allocated per step** (47×). Naming which one it is matters: (a) is
fixed by keeping the root fixed and carrying a consumed-count cursor, (b) by
changing the result type. Decomposition tells you it is *composition*; only an A/B
that differs in exactly one dimension tells you *which* composition.

Do **not** start from "the recursion scheme must be it". Re-expressing a
`WellFounded.fix` definition with `termination_by` is a **no-op** — Lean
elaborates both to the same well-founded recursion (measured: 0.5% difference).
That rewrite changes no codegen and no specification, so it is never the answer to
a performance question. Only after decomposition rules out the parts should you
reach for the carrier swap in step 1.

**The rule:** measure *what actually costs* (the recursion scheme, then the result
 allocation, and only then the byte loop) before choosing a layer; pick the
 cheapest layer that removes *that* cost; record the measured outcome honestly
 even when it is "no speedup".

---

## Append new learnings here

Reverse-chronological (latest first), one **entry** per lesson — entries are
paragraphs, not one-liners; keep each one focused on a single transferable fact.

- 2026-11-04 — **`lean --run` is the interpreter; the compiled exe is not.** The same call measured **~850–1050 ns/call under `lean --run`** and **86 ns/call** compiled into a `lean_exe` by `lake build` — a **10x** gap, in the direction that makes the *interpreter* look like a finding. Two rules follow. (1) Never paste a `lean --run` figure next to a compiled one, and never quote one as "the cost" when the other is what ships; `#eval`/`lean --run` are for *value* checks and quick reduction, `lake build` + running the binary is for timing. (2) A `probe.lean` compiled ad hoc still links the toolchain's optimized runtime, so "it's just a probe" does not excuse an unlabelled number. This bit hard: a session nearly published "the lane is 10x wrong" on the strength of an interpreter reading, when the lane was right.

- 2026-11-04 — **A sink that is a constant measures nothing: check it varies.** A benchmark whose result is folded into a sink like `(…).length` is *folded away entirely* when that length is constant — for a fixed-arity decoder the candidate count is always `1`, so the optimiser keeps only the fold and reports **3 ns/call for a call that really costs 86**. The failure is silent and it survives a coarse "is the sink zero?" guard, because a nonzero constant passes. **The check is invariance, not non-zero-ness:** evaluate the lane's function over several *distinct inputs* and assert the sink actually differs (`List.eraseDups`, or compare two calls); if it does not, the closure is loop-invariant and the number is not a measurement. Corollary specific to the other facet: varying only the *seed* of the sink while keeping the data argument fixed is **not** enough — the optimiser keeps the computation and only the seed moves. Vary the data. (Companion to the interleaved/burst and per-call-vs-per-byte entries above: all three are ways the harness, not the code, produces the number.)

- 2026-11-04 — **A `simp only` list must be re-minimised after you change the goal's shape, and the linter tells you the answer.** Moving a proof from a probe into the library — where `-DwarningAsError=true` holds — turned ten `linter.unusedSimpArgs` *warnings* into ten build *errors*, and the honest fix took five rounds: delete the flagged arg, rebuild, read the new hint, repeat, because **each removed argument changes which of the remaining ones fire**. `Lean` prints the exact corrected list in its hint (`[apply] simp only [Bool.or_eq_true, Bool.and_eq_true]`), so the fastest correct loop is literally: copy the hint into the file, rebuild. Resist the alternative of setting `set_option linter.unusedSimpArgs false` — a file-wide switch that hides the *next* one too, which is how a `simpa` set silently grows to 90 arguments. Worth naming because the error text ("This simp argument is unused") points at a *stylistic* problem while the consequence is a non-zero exit, so it reads like a spurious gate failure when it is the gate working.

- 2026-11-04 — **Spike both approaches before choosing one, and let the compiler rank them.** Asked to pick the "most correct" of two proof strategies, and having argued confidently for the more general one, the spike reversed the answer: the *generic* lemma needed characterising an `if`-ladder decoder for arbitrary valid inputs (six attempts, one goal still open), while the *per-vector* one at the lower definition closed in four because that definition's body **is** the property being asserted (`if reencode bs = some cs then some bs else none`), so `split` on the guard is a direct reading. Two transferable rules. (1) **Prefer the lemma whose statement matches a definition's own shape.** If a `def` is written as a guarded equality, the law you want is a `split` on that guard plus `decide` per branch — near-free. If the law must be stated at a *higher* level, you are first obliged to characterise the lower level in general, and that characterisation, not the statement, is where the cost lives. (2) **Generality argued on the whiteboard is a hypothesis; measure it.** "The general version is more correct" is often true *and* irrelevant when the specific fact is already derivable by composing two existing lemmas — check whether the generic statement is *reachable* before proving it anew. Corollary on consistency: if every sibling law in the file is per-vector, a lone generic one is a uniformity cost that a reviewer will (rightly) flag; the repo's own conventions are evidence about which shape earns its place.

- 2026-11-04 — **Well-founded recursion does not reduce under `decide`.** A `def` carrying `termination_by`/`decreasing_by` is opaque to the kernel's evaluator, so `example : decode … = some x := by decide` (or `rfl`) **fails** even for a tiny literal input — while the same definition evaluates fine under `#eval`. The tempting fix, `native_decide`, is **not** available in an axiom-gated project: it closes goals via `Lean.ofReduceBool`, which `#print axioms` reports as an axiom and which breaks a `[propext, Quot.sound]`-only discipline. So the split is forced: **proofs** state the law abstractly (no evaluation), and **executable value checks** go in a runtime lane or `#eval`, never into the kernel-checked statement. Decide which you need *before* writing the example, and if the file is axiom-gated, label the runtime check as a value check rather than letting it look like a proof.

- 2026-11-04 — **`obtain ⟨-, rfl⟩` silently eliminates the name you need.** Destructuring a pair equality `(y, t) = (x, tr)` with `rfl` for the second component makes Lean *substitute one side away*, so a later `exact h a s tr …` fails with the confusing `unknown identifier 'tr'` — the hypothesis you meant to rewrite now has no name. Fix: keep it as an equality and transport explicitly — `obtain ⟨-, htr⟩ := hf` then `exact h a s t (htr ▸ hmem')` — and if you need the original spelling, say so in a `have`. Same family as the `cases`-substitutes-vs-rewrites confusion, but this one is caused by *success* (the destructuring worked) rather than by a refusal, which is why the error text points at the wrong place.

- 2026-11-04 — **`Nat.add_mul_div_left` divides by the *multiplier*.** Its statement is `(x + y * z) / y = x / y + z`, so to prove `(lo + 256 * hi) / 256 = hi` the `256` must already sit **second** in the product — applying `Nat.mul_comm` first (a natural reflex) turns the goal into `(lo + hi * 256) / 256`, after which the lemma no longer matches and the error is a pattern-not-found at an apparently identical-looking goal. Sibling shape traps in the same family: `Nat.mod_add_div m k : m % k + k * (m / k) = m` versus `Nat.div_add_mod m n : n * (m / n) + m % n = m` — the *mod* comes first in one and second in the other, and picking the wrong one silently fails on an argument order, not on substance. Also note `UInt16.toNat_ofNat` is stated at `OfNat.ofNat` while `UInt16.toNat_ofNat'` is stated at `UInt16.ofNat`; a `rw` against the unprimed one does not fire on `UInt16.ofNat` and the goal prints identically.

- 2026-11-03 — **Interleaved benchmarks are cold; a "floor" needs a burst lane.** A harness that interleaves a reference operation (a same-size `memcpy`) with each measured call is *correct* for a ratio to that reference — both sides see the same cache state — and it also **evicts the input between calls**, so what it prints is memory-bound cost. Measured on the identical loop: `arr.getD k` + a `Nat` cursor over 4 KiB is **6 ns/step in a burst** (200 back-to-back calls, input varied per call so nothing hoists) vs **15–16 ns/step interleaved**, a ~2.5× gap that is entirely cache state. A doc had been calling the interleaved figure "the achievable pure-Lean floor" and dividing a cold decode by it, which turned an ~11× gap into a claimed ~3×. **Rule:** a *floor* is a compute claim, so quote it from a burst (input L1-resident, span ≫ the clock's ~41 ns granularity); a *throughput* figure comes from the interleaved lane; report both, label which question each answers, and never divide one by the other. Two corollaries: (a) a single small-buffer call inside an interleaved lane is timing noise, not a measurement — always batch; (b) adding a burst lane will move a previously-quoted floor, and that movement is a finding about the *old* number, not a regression in the code.

- 2026-11-02 — **A benchmark number is sourced because the lane prints it.** A benchmark number is sourced because the lane, run, prints it — not because a lane exists. Three performance rows in a doc were each labelled with the name of a `benchRatio` lane and none of them matched what that lane printed; the rows had been written from an earlier ad-hoc probe and the lanes added later. Worse, two of the lanes were *themselves* wrong, in ways that are generalisable: (a) a "floor" lane that `Array.push`-ed every element into a fresh output array measured the floor **plus n elements of growth** and then quoted the total as "the achievable floor" — it read ~15 ns/step with the push and ~15 without it only once the push was replaced by a `Nat` sink, so the allocation was most of the number; (b) a "per-step" term that built its list **once over the whole input** and let the harness divide by `n` reported ~12 ns/"step" — *below* the 48 ns/step decode it was a component of, an arithmetic impossibility that was visible for several revisions to anyone who compared two rows. **Three checks catch both, and they are cheap:** (i) after adding a lane, paste its literal output next to the quoted figure in the same session — if they differ, the doc is wrong, not the number; (ii) sanity-check every per-step term against the whole it composes — a component cannot exceed its composite unless the composite amortises it, and if it does, it is not a per-step quantity; (iii) read the lane's own body for allocation and for a divisor that does not match what one call does. `benchRatio`'s per-byte division is a footgun for anything that is naturally per-*call*: report those through a plain `ns/op` print instead of manufacturing a denominator.

**Scope, stated once so it can be checked:** everything here is **stdlib-only**
(no mathlib — so no `split_ifs`, no `omega` extensions, and `exact?`/`apply?` are
weak) and **pinned to Lean 4.34** where a fact is version-dependent. Cite the
version when an entry names one.

**This file holds only the *generic* half.** The domain-specific entries — the ones
that only make sense knowing a particular byte-codec/substrate library (`Bytes n`,
`relRepeat`, `Suffix`, `Iso.law`, `@[extern]` seams, block/padding encodings) —
live in that project's own repository, not here. The project this file was grown
in keeps its half in `openspec/lean-notes.md` in the `lean-codec` repository; if
you are working there, **read that file too** — it is the raw measured record
behind §2b's table and the source of most entries here. **The two files are not
mirrored, and the split is measured rather than asserted:** on a 2026-11-02 count
the repo file held 178 entries and this one 59, with 8 (not 57) appearing word-for-word
in both. Do not reason from an entry-count identity; if you need a specific lesson,
grep both. **The authoritative summary of the axiom-hygiene
family is §2b's table, not these entries** — add a row there when you learn a new
leak shape.

**Convention for entries:** open with a bold lead-in of **at most ~70 characters**
so the entry is greppable, then the detail. Every entry now complies — all 60 were
brought under the cap on 2026-11-02 by shortening the *title* and moving the
original long phrasing into the entry's first sentence, so nothing a reader would
quote was lost (verified: line count and bullet count unchanged, zero original
titles dropped). If you add an entry, keep the cap; if you must exceed it, shorten
the title rather than truncating the body.

---

- 2026-11-03 — **Two `Classical.choice` leaks: `omega` `Nat`-sub; `cases <;> simp_all`.** Two more `Classical.choice` leak shapes, both found by bisecting a proof that looked clean: `omega` on a `Nat`-subtraction bound, and `cases … <;> simp_all` over two lists. (a) `omega` proving `n - m < n` from `m ≠ 0` and `m ≤ n` leaks (it goes through the subtraction trichotomy). Fix: `Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hne) hm) (Nat.pos_of_ne_zero hne)` — axiom-free. This is the same family as the known `Nat`-subtraction-trichotomy entry and is the *most likely* place a well-founded recursion's `decreasing_by`-style bound gets written by hand. (b) `cases xs <;> cases ys <;> simp_all`, used to dispose of `[]`-vs-`cons` list cases, leaks — the leak is `simp_all` doing case analysis, not the `cases`. Fix: state the length facts explicitly (`simp only [List.length_nil, List.length_cons] at h` then `omega`) or use `Nat.succ_inj`. **The bisection recipe that actually isolates these:** extract the proof's hardest sub-argument as a standalone `theorem` taking the induction hypothesis as an ordinary *parameter*, then `#print axioms` that theorem alone. If the standalone version is clean and the enclosing lemma is not, the leak is in the *wiring* (recursor motive, `subst` chain, list cases), not the mathematics — which halves the search space immediately. Do not bisect by inserting `sorry`; `sorryAx` masks the footprint you are trying to read.

- 2026-11-03 — **`Array.toList_extract`/`getElem_extract` carry `Classical.choice`.** `Array.toList_extract` and `Array.getElem_extract` both carry `Classical.choice` in Lean 4.34 — so *every* proof route through `Array.extract` leaves an axiom-clean-only gate, and the readback is where it enters, not `Array.ext'`. Trying to prove the two spellings of a suffix copy equal, i.e. `a.extract i a.size = (List.drop i a.toList).toArray`, a proof that went through `apply Array.ext'` *compiled* and then reported `[propext, Classical.choice, Quot.sound]`. Bisecting the footprint (`#print axioms` on each cited lemma in turn) found it is not `Array.ext'`: `#print axioms Array.toList_extract` and `#print axioms Array.getElem_extract` **both report `Classical.choice`**, so any route that reads an `Array.extract` back as a list inherits it. Consequences worth planning around: (a) if you are writing a refinement between an `Array.extract`-shaped body and a `List`-shaped spec, **check the footprint before believing the proof** — the statement looks clean and elaborates fine; (b) the honest fallback is a *measurement plus a recorded decision* (the fast transport is real and N× faster; it also cannot be connected inside the gate), not a weakened statement and not a `sorry`; (c) check the individual lemma, not just the tactic — `Array.ext'` was the obvious suspect and was innocent.


- 2026-11-03 — **A per-call micro-benchmark of a pure function is CSE'd.** A per-call micro-benchmark of a *pure* function is CSE'd by default: `timeBatch reps (fun _ => f a)` measures the optimiser, not `f`, when `f a` does not change between reps. Two implementations of the same pure transport, timed with `timeBatch 30 (fun _ => impl a)` on the same buffer, reported a **2×** ratio; the same comparison with a *different* input per sample (`pool.getD (i % 4)`) reported **42–44×** — the true figure. The loop-invariant call is common-subexpression-eliminated (or hoisted entirely), so the timed window contains the *first* evaluation only and the rest is a register read. Mitigations, in order: (a) give each sample a different input from a pre-built pool, never a shared closure; (b) never divide a single-call span by `reps` (a real bug — `timeBatch 1 f` divided by `reps` scales a correct measurement down by `reps`); (c) a wall clock with ~40 ns granularity cannot resolve a ~20 µs call from one sample, so take a **median of interleaved samples** rather than one shot; (d) assert a **data-dependent, non-zero sink** of the result, because a constant-folded or dead result collapses the window to `0 ns` (seen as literally `0 ns/op`). The tell that you have been fooled: a number that is *impossibly* good for the work described (`0 ns` for a megabyte, or a backend-shaped `41 ns` flat across sizes).


- 2026-11-02 — **`split` on a `match`-with-a-named-equation leaks `Classical.choice`.** `split` on a `match`-with-a-named-equation is itself a `Classical.choice` source, and an *anonymous `by <tactic>` proof inside a `match` arm* is the other half of the same leak — the two make an unfolding lemma leaky while its statement (and every lemma it cites) looks clean. A recursive `def` whose body is `match _hm : n - m with | 0 => … | _ + 1 => f … (by omega) …` compiles its successor arm's bound as a tactic proof over facts only the arm knows. Proving the unfolders by `rw [f.eq_def]; split` then reports `[propext, Classical.choice, Quot.sound]`, and so does the same proof of the *zero* case — even though the surrounding file's other unfolders are clean. Bisection that names it fast: `#print axioms` on each lemma in turn and on the definition; if all are clean but the theorem is not, stub the theorem's body in halves (each `<;> sorry`) and see which half reintroduces `Classical.choice` — here one `rw [fast_succ …]` did, and `#print axioms` on *that* lemma showed the leak was already in it. **The durable fix is structural, not tactical:** make the bound an ordinary parameter of both the function and its search sibling (the candidate subtype already carries the `≤` field, so it is passed through rather than invented), after which `conv => lhs; rw [f.eq_def]; dsimp only; rw [h]` — the *other* recipe, which a previous entry says "does not transfer" — works cleanly. So the earlier entry's conclusion was a symptom of this leak, not an independent fact: **when `split` "works but `dsimp only` makes no progress", check the axiom footprint before adopting `split` as the recipe.**


- 2026-11-02 — **Two `List.attach` lists, same provenance: don't rewrite `attach`.** To relate two `List.attach` lists of the *same* provenance, do not rewrite `attach` — read both positionally through `List.getElem?_attach` and prove the correspondence at an index. Two attached candidate lists (one `{pr // pr ∈ decodeArray …}`, one `{pr // pr ∈ decode …}`) are element-for-element the same sequence, but stating that as `(a).attach = (b).attach.map f` and `rw`-ing the underlying list dies with "motive is not type correct": the `Membership` proof in each element mentions the list. The proof that does go through states the fact **at an index**: `∀ i c s, xs.attach[i]? = some c → ys.attach[i]? = some s → c.val.1 = s.val.1 ∧ …`, and opens both sides with `rw [List.getElem?_attach]` (which turns the read into `Option.pmap Subtype.mk xs[i]? _`), then `cases xs[i]?` and `Option.some.inj`. Two useful corollaries: `simp only [h] at hc` works where `rw [h] at hc` fails when the hypothesis is under an `Option.pmap`'s proof argument; and `List.length_attach`/`List.getElem?_attach`/`List.mem_of_getElem?` are the three lemmas the whole route needs. Pair this with an *alignment* record (`same length ∧ ∀ i, aligned`), which is what makes an induction over one list usable against the other.


- 2026-11-02 — **`decode_cast`-shaped transport lemmas are needed for a `dite`.** `decode_cast`-shaped transport lemmas are needed for *any* `B`-indexed function, and the cheapest one is `subst` + `rfl` — but it must be proved as its own lemma, because inlining the transport hits the index's dependent motive. Wanting `decodeFull n s = decodeFull m (cast (congrArg Bytes e) s)` from `e : n = m`, every attempt to `rw [e]` or `subst` at a use site failed on "motive is not type correct" (the `Bytes` argument's index). Proving `theorem decodeFull_cast (e : n = m) (s : Bytes n) : decodeFull n s = decodeFull m (cast … s) := by subst e; rfl` took one line, and every later `rw [decodeFull_cast … e …]` then fired. Same pattern as the pointwise-equality rule for indexed carriers: **state the transport as a lemma at the type the consumer's motive wants, then rewrite with it** — do not try to make the consumer's goal reduce. Also: when the equation is `Nat.sub_zero`-shaped (`n - 0 = n`), `rw` on it in a `B`-indexed goal is blocked exactly the same way, and the cast lemma is again the way through.


- 2026-11-02 — **`mutual` is a command: no doc comment or `set_option` can attach.** `mutual` is a *command*, so a `/-- … -/` doc comment cannot attach to it — and a `set_option … in` placed between the doc and `mutual` is a parse error, not an option. Writing a documented mutual block, the doc comment above `mutual` fails with "unexpected token 'mutual'; expected … 'def' … 'theorem' …". The cause is that `mutual` is a command form with no declaration to attach a doc to, so the doc comment has nothing to bind and the parser expects a real declaration next. Two spellings work: use a **plain `/- … -/` block comment** (which is what the file's existing, compiling mutual pair already does — check before "fixing" it), or move the doc onto the first `def` inside the block. A `set_option foo in` must go *inside* the block or *before* the doc comment, never between the doc and `mutual`. Cheap to fix, but the error text points at `mutual` and reads like a syntax catastrophe when the real problem is the doc comment.


- 2026-11-02 — **A bound is often one-sided for a reason: `≤ n`, not `< n`.** A bound you want is often one-sided for a real reason: `≤ n`, not `< n`, because a zero-consumption step exists. A natural-looking candidate invariant ("every decoder result consumes strictly fewer than the remaining bytes") is **false**, not merely awkward: a `pure`-like leaf returns the *same* cursor (`c = i`), so the honest statement is `c ≤ n`. `lt` there fails with a goal that looks like an arithmetic difficulty but is a false theorem. The general lesson: when an arithmetic goal in a well-foundedness proof "will not close" despite plausible hypotheses, first ask whether the bound is *actually* what you wrote — check an exhaustively-`#eval`'d statement of it, or find the degenerate constructor (`pure`, `empty`, identity suffix) that refutes it. Correcting `<<` to `≤` in both the subtype *and* the lemma took one edit; raising the priority of the exhaustiveness check is the durable fix.


- 2026-11-02 — **An unfold recipe is not transferable to a sibling definition.** An "unfold recipe" that worked for one definition is not transferable to a sibling that differs only in *what its body mentions*, and the failure looks like "motive is not type correct". A recursive definition's unfolding lemma was proved with `conv => lhs; rw [f.eq_def]; dsimp only; rw [h]`. The sibling definition — same recursion scheme, same `match _ : n - m with` shape — fails this recipe twice over: `dsimp only` reports "made no progress", and without it `rw [h]` reports "motive is not type correct" because the discriminee has been generalized to a fresh binder (the body mentions an extra parameter, so `.eq_def` abstracts it). The fix is `rw [f.eq_def]; split` with the branches closed directly (and, for a `match`-in-`match` body, `simp only` to force the inner one, then `split`, then `injection` on the discriminant equation to realign `split`'s freshly-named binders with the ones in the statement). **The diagnostic:** when a copied recipe fails with "motive is not type correct", do not hunt for the right lemma — print the *unfolded* goal (`trace_state` after `rw [f.eq_def]`) and look for a `⟨x✝, c✝⟩`-style generalized binder; then choose `split` over `rw`.


- 2026-11-02 — **`filterMap` lists need a length bound: `List.length_filterMap_le`.** `filterMap`-based candidate lists need a *length* bound lemma, and `List.length_filterMap_le` already exists with its arguments in `(f, l)` order. An auxiliary list built by `(l).attach.filterMap (fun p => …)` is the right shape for "keep the membership witness while dropping the ones that fail a decidable test", but a well-foundedness measure that counts its length then needs `(filterMap f l).length ≤ l.length`. Writing that by hand (`induction`, `List.filterMap_cons`, `split`, `omega`) works but is unnecessary: `List.length_filterMap_le` is in the stdlib and takes **`f` first, then `l`** (`List.length_filterMap_le f l`), unlike most `List.*` lemmas — a `_ le _`-style argument order is the trap. Compose with `List.length_attach` (a lemma, not a function: use `List.length_attach` bare, not `List.length_attach _`) for `attach`-based lists.

- 2026-11-02 — **A "discharge for a concrete case" task is a test of the definition.** A "discharge this hypothesis for a concrete case" task is a *test* of the definition, so make the test able to fail. Adding `instance`-style base facts (`unambiguous (byte)`, `functional (byte)`) for predicates that had only ever been *hypotheses* is worth doing even when the proof is trivial, because it is the only thing that can catch a typo in the definition — but only if you **verify load-bearingness by mutation**: temporarily weaken or re-spell the definition (e.g. quantify over two independent byte strings instead of one) and confirm the instance's proof then *fails*. If the mutated version still proves, the instance is vacuous and tests nothing. This is the same discipline as proving a `sorry`-gate is real by stubbing a theorem and watching the build fail — the check is cheap and it is the difference between "we have a test" and "we have a ceremony".


- 2026-11-02 — **`USize`/`Array` proof obligations: verify by exhaustive `#eval`.** A proof obligation stated at `USize`/`Array`-level arithmetic must be *verified by exhaustive `#eval`* the same way a `Nat` identity is, and the answer is often "equal because `min` is AC, not because the code matches". Two implementations of the same clamped-window update were documented as agreeing "term-for-term"; they do not — one computes `min len (min (n-dc) (slen-sc))` and the other clamps sequentially (`len` against `n-dc`, then the result against `slen-sc`). They agree **value-for-value** by associativity and commutativity of `min`. That distinction is the whole content of a trust-seam argument: a reader who compares the two line by line will "fix" a difference that is not a bug, and a reviewer who is told "identical" will not look for the real invariant. Write the *reason* (AC) and the *order actually used*, and check it exhaustively over small values (`n, slen < 6`, offsets/`len < 9` is 2.3M tuples and runs instantly). Same entry point as the `Nat`-identity rule: one `#eval` line, before writing the prose.


- 2026-11-02 — **`rw [f.eq_def]` failing: unfold, don't hunt for a lemma.** When `rw [f.eq_def]` fails with "did not find an occurrence of the pattern `n - m`" on a `match`-defined function whose scrutinee is *plainly* present, the missing step is a bare `dsimp only` between the two rewrites — not a `cases`, not a `split`, not a restatement. A structurally recursive `def` compiled from `match n - m with …` elaborates to `match n, s, m, acc with | n, s, m, acc => match _hm : n - m with …`, i.e. an outer **tuple-of-all-arguments** match. `conv => lhs; rw [f.eq_def]` produces that wrapper; the inner `n - m` is then not syntactically reachable, so `rw [hk]` reports the pattern as absent and the error reads like a wrong-lemma or wrong-type problem. The working recipe is exactly three steps: `conv => lhs; rw [f.eq_def]`, then `dsimp only`, then `rw [hk]`. Same shape at a *successor* scrutinee and at a *zero* one. **Package it as a named lemma the moment it works** (one for each constructor form of the scrutinee) rather than re-deriving the recipe at every call site — this is a proof-engineering step that took several failed sessions to name, precisely because every failure mode looks like a type error. Corollary: if `split` keeps producing case tags that do not match (`h_1` alone, or a binder named `heq`), and `cases n - m` renames the equation out of the hypotheses, you are in this situation — reach for `dsimp only` first.


- 2026-11-02 — **A typeclass argument can make a lemma un-rewritable.** A typeclass argument (`Membership`, `DecidableEq`, `LE`) is selected on the *syntactic head* of a type, so two definitionally-equal spellings of the same list type get *different* instances — and the error looks like a wrong-type error, not an instance error. With two aliases whose element subtype is spelled `decode p (drop m s).bytes` in one place and `decode p (drop 0 (drop m s).bytes)` in another (`rfl`-equal, verified), passing a list of one to a function expecting the other fails with `Application type mismatch: The argument List.instMembership has type Membership (α × S (drop 0 (…)).rem) (List (…)) but is expected to have type Membership (α × S (drop m s).rem) (List (…))` — the complaint names `List.instMembership`, not your term, which is why it reads as nonsense. **Rule: when two spellings of a list/scalar type are only *definitionally* equal, do not mix them** — pick the spelling the consuming function's own signature produces, and state any helper lemma at that spelling. This is a distinct trap from rewriting under `List.attach`: nothing here is a `rw` motive problem, it is instance resolution, so `cases`/`rfl`-per-branch does not help and the fix is purely to unify the spelling.


- 2026-11-02 — **`#eval` a `Nat`-subtraction identity exhaustively first.** `#eval` a `Nat`-subtraction identity *exhaustively over small values* before writing a lemma for it, and treat any `omega` counterexample report as evidence that the identity is false rather than that `omega` is weak. Two sessions were lost to identities like `n - (m + (n - m - r)) = n - m - r` that "looked right" and are **false** (`r = 0, m = 0, n = 1` refutes it), while the true statement was `… = r`. The check costs one line and settles it:

  `#eval (List.range 8).all (fun n => (List.range 8).all (fun m => (List.range 8).all (fun r => if r ≤ n - m then decide (<candidate identity>) else true)))`

  A `false` tells you to re-derive the identity; a `true` tells you the statement is right and only the proof is missing. Relatedly, `omega` cannot derive `m ≤ n` from a hypothesis mentioning `n - m`: truncated subtraction collapses both `n ≤ m` and `m > n` to `0`, so **any lemma about `n - m` must be case-split on `Nat.le_total m n` first**, with the degenerate branch closed by `n - m = 0 → r = 0`.


- 2026-11-02 — **`conv_lhs`/`conv_rhs` don't exist in Lean 4.34.1.** `conv_lhs`/`conv_rhs` do not exist in Lean 4.34.1 — use `calc`, `nth_rewrite`, or a named `have` — and there is no `List.bind` (it is `flatMap`) nor `List.filter` returning `Option` (it is `filterMap`). A tactic block written from memory with `conv_lhs => rw […]` fails with a bare `unknown tactic`, which reads like a missing import; likewise `l.bind` fails with `Invalid field 'bind': the environment does not contain 'List.bind'`. Neither is recoverable by `open`, so grep the toolchain rather than assuming the mathlib-era spelling. `conv => lhs; rw […]` (the non-suffixed form) is also unavailable here, so prefer `calc` chains — they are clearer anyway when the goal is a multi-step `Nat` identity.


- 2026-11-01 — **A diagnosis of why a proof won't close is itself a claim to test.** A *diagnosis* of why a proof will not close is itself a claim to test with a counterexample — a plausible-sounding missing hypothesis can be false, and re-recording it as "the fix" costs the next session a duplicated refutation. A task was recorded as "the derivation needs hypothesis H alongside the ones we have"; a later session built a two-line counterexample showing the original hypothesis set **already satisfies H** and still fails, so the recorded diagnosis was wrong and had to be overturned in place. **Rule:** when you conclude "we just need H", prove `¬ (existing → goal)` *and* `existing ∧ H` is satisfiable-without-goal — i.e. exhibit a witness that has `H` and still refutes. Otherwise you have replaced one false statement with another. Corollary for handoffs: a refutation written as a theorem in the source is durable; the *same* refutation written as prose in a notes file drifts, so amend the prose entry in the same commit that lands the theorem.

- 2026-11-01 — **A `Prod.Lex` ranking that elaborates can still break proofs.** A `termination_by` `Prod.Lex` ranking that "works" for the definition can still make the theorems unprovable — check the *proof* shape before committing to the measure. A `mutual` pair where the caller is ranked `(·, n + 1)` and the callee `(·, n)` type-checks fine, but `Prod.Lex` then has **no reflexive case**, so when you want to prove *both* members' congruences at the same state, neither can call the other at an equal key: the induction hypothesis is only available *strictly below* the current key. Symptom: the base cases and all the unfolding go through, and the only failure is the hand-off ("expected `Prod.Lex … (state) key`, got `Prod.Lex … (a, b) (a, b.succ)`"). Fixes, in order of preference: (a) state the two facts so that the one that needs the other is ranked *lower*; (b) prove the pair at one key in a single statement whose induction hypothesis is the *conjunction* (the recursor then hands you the sibling at the same key); (c) re-rank the definition so the *descending* direction is the one that carries the `+1` tick. Do not try to discharge an equal-key edge — there is nothing to discharge it with. **Follow-up (2026-11-02), because this entry's framing sent a later session down the wrong path for hours: prefer (b) *first*, and treat it as the intended route rather than a last resort.** When you are proving *two* facts about a `mutual` pair, put **both** in the caller's motive (`motive1` = `fast ∧ search`) and let the recursor's own callee-hypothesis (`motive2`, which the `mutual_induct` already hands you at a strictly shorter sub-measure) supply the sibling. That works with **no** re-ranking, **no** change to the `termination_by`, and **no** change to any declaration's shape — so fixes (a) and (c), which both mean editing the definition, are usually unnecessary. The tell that (b) is available: `#check @f.induct` shows two motives, one per member; if so, the pair is already reachable and the "ranking obstacle" is not real.


- 2026-11-01 — **`rw [f.eq_def]` misses an applied occurrence under a nested `match`.** `rw [f.eq_def]` does not fire on an applied occurrence when `f`'s body is a `match` nested inside another `match`; `cases` the scrutinee first. For a function written `| args => match x with | … => match y with | …`, `rw [f.eq_def]` on `f a b c` fails with "did not find an occurrence of the pattern" even though the term is plainly there. Two working routes: `cases` the outer scrutinee (so the application reduces structurally), or state the unfolding as an explicit `have h : f a b c = (match …) := by rw [f.eq_def]` (this form *does* elaborate when the goal is the bare equation) and then `rw [h]`. Related: a `def` compiled from a `match` with a `_hm :` proof binder produces a *dependent* `match`, and `generalize`/`rw` on its scrutinee then fails with "motive is not type correct" — reduce it with `cases`/`rfl` per branch rather than rewriting.


- 2026-11-01 — **In a `mutual` block the first item must be a `def`/`ind`-family.** In a `mutual` block the first item must be a `def`/`inductive` — a `/-- … -/` docstring immediately after `mutual` is a parse error ("unexpected token '/--'"), and putting the docstring *before* `mutual` attaches it to the block, not to the definition. Write the documentation as a plain `/- … -/` or `--` comment above `mutual`, and leave the per-definition docstring out (or `add_decl_doc` it afterwards). The error message is unhelpful because it lists *every* command head as "expected", which reads like a missing keyword rather than a misplaced comment.


- 2026-11-01 — **After 3-4 failed rewrites, question the *statement.** * When a proof keeps failing on rewrite shapes after 3-4 attempts, stop and question the *statement*, not the tactics. A bridge lemma `fastRoot = spec` was pursued for dozens of tactic iterations ("did not find an occurrence", "motive is not type correct") before it was tested empirically — and turned out to be **false**: the fast path committed to the first candidate while the spec backtracked. The tell is that the failures are *all about index alignment and match-shape*, never about mathematics; that pattern means the two sides of the equation are not the same function. **Cheap falsification test for any "these two decoders/parsers/evaluators agree" lemma: build a tiny input where they differ structurally, `#eval` both, and compare.** Do it *before* the proof, not after; a `#eval` line costs seconds and can save a session. This is the same class as the earlier "refuted diagnosis" entries, but the lesson is sharper: a *statement* can be wrong in a way no amount of tactic work reveals.


- 2026-10-31 — **For an indexed carrier, state equalities pointwise.** For a `Bytes`-like indexed carrier, state equalities *pointwise* (as reads at indices) to avoid a length cast that then blocks everything. The natural `Bytes`-level lemma (`t.bytes = drop …`) forces a cast at the index (`drop o s : Bytes (n - o)`, not `Bytes t.remaining`), and that cast is opaque to `rw`: every downstream rewrite fails with "motive is not type correct". Stating the *same* fact as `t.bytes i = s ⟨i.val + …, _⟩` for `i : Fin t.remaining` has **no cast anywhere**, and the downstream proof becomes `Fin.ext` + `omega`. This was the single decision that unblocked a month-long stuck proof; the cast form was a dead end attempted many times.


- 2026-10-31 — **`omega` can't use a hypothesis containing an unreduced projection.** `omega` will not use a hypothesis whose type contains a projection that hasn't reduced. `t.hle : t.remaining ≤ (drop m s).remaining` looks usable, but `omega` sees the `drop` and gives up. Fix: **restate it numerically first** — `have h : t.remaining ≤ n - m := t.hle` — then `omega` closes immediately. Same class as the modulo rule: `omega` wants a plain numeric hypothesis, not one wrapped in a definition.


- 2026-10-31 — **`congr 2` can be the whole proof of a recursion equation.** `congr 2` can be the entire proof of a `WellFounded.fix` recursion equation, and is load-bearing when it is. To unfold a `WellFounded.fix`-defined recursive function at a `Nat.succ` index: `rw [f, WellFounded.fix_eq]` then `simp only [Nat.add_one]` then `congr 2`. The last step discharges the residual comparison of the fix's `ih` against the function itself — which *is* the fix point, definitionally — so the goal does not close without it. Do not delete it as "redundant"; a `congr` that seems to do nothing may be doing the only step that matters.


- 2026-10-31 — **A `match`-based recursion's `.eq_def` rewrite is often complete.** A `match`-based recursion's `.eq_def` rewrite is often a complete proof, so follow it with nothing. `rw [f.eq_def]` on a `match`-defined function whose scrutinee is already a known constructor form reduces the goal entirely; appending `cases`/`simp` to be safe then errors with **"No goals to be solved"**. If a tactic line errors that way, the fix is to *delete the following lines*, not to add `try`.


- 2026-10-28 — **A lazily-composed *input* is the same trap as a lazy result.** A lazily-composed *input* is the same trap as a lazily-composed result: feeding a "dropped prefix" function its own output builds a closure chain, and reading through it is Θ(depth). A decoder returned its remainder as a function (`drop k s` is a *closure over `s`*, cheap and non-copying) — which is the right design for memory, and the wrong one for iteration. Passing that remainder back in as the next step's input **composes** the closures, so reading byte 0 at depth `k` applies `k` closures: O(1) per step becomes O(k), O(n) becomes Θ(n²). Measured on otherwise identical work (n `decode` calls, same helpers): **chained remainder 92,876 µs vs re-derived from the root 139 µs at n=4096 — 668×**. Fix: keep the **original** input fixed and carry a consumed-count cursor, re-deriving each step as `drop m root`; the composition lemma (`drop m (drop k s) = drop (k+m) s`, up to the length cast the type index forces) is what licenses it. Effect: 24.9 s → 2.75 ms at n=65536, and the walk goes linear. **Diagnostic**: if a "fast" lazy carrier is O(1) per step yet the whole run is super-linear, time `chained` vs `flat` over the same helpers — a large gap is the chain, not the algorithm. Corollary: this is invisible to `#print axioms` and to any per-operation profile; only an end-to-end A/B that differs in *exactly* this one dimension finds it.

- 2026-10-28 — **The result type decides the order of magnitude.** The *result type* decides the order of magnitude, and the gap between a `List`-returning and a cursor-returning step is ~5× on the same reads. Same data, same machine, same run, one process — measured against a `memcpy`-class bulk op as the C reference:

  | path | MiB/s | vs `memcpy` |
  | --- | --- | --- |
  | `memcpy`-class bulk op | 1,891 | 1× |
  | **bulk cursor decode** (read a byte, `Array.push`) | **222** | **8.5×** |
  | plain `Array.get` loop | 307 | 6.2× |
  | per-step `List` decode (`[(a[i], i+1)]` per byte) | 40 | 47× |
  | backtracking *search* decoder | ~0.01 | ~10^5× |

  **Rule: a small single-digit multiple of C is reachable in pure Lean** (`Array UInt8` + an integer cursor + an `Id.run do` accumulating loop, ~8.5×), so "Lean is 20-40× off C" is an *architecture* statement, not a language one. A path that is 47× is returning a `List` per step (a cons cell + `Prod` + boxed `Nat` for what is one array read); a path that is 10^5× is doing a **search** where a single pass would do. Diagnose by measuring one step in isolation: 6,100 µs for n steps of "one array read" vs 767 µs for the same reads in a plain loop is a 8× that no scalar-type change can touch. Corollary: assert the **ratio to a same-run `memcpy`**, never an absolute MiB/s floor — an absolute floor is machine-dependent and gets tuned down the first time CI is slow, while the ratio is the property you actually mean. Corollary 2: when the requirement is "within N× of C", make the *result type* the first design question, before any FFI or backend work.

- 2026-10-28 — **Measuring Lean performance: three traps that report `0 us`.** Measuring Lean performance has three traps that all report `0 us` or a plausible-but-wrong number; force the value or you measured nothing. (1) **`lake env lean file.lean` *interprets*** — it does not compile, and a `main` defined there **does not run at all**, so timings from it (or from `#eval` on a large computation) are meaningless; you need a real `lean_exe` (`lakefile.lean`: `lean_exe foo where root := \`Foo`) and run the built binary. (2) **Dead-code elimination**: if you time `(f x).length` or `(g x).1`, the compiler can compute only the length/index and elide the payload — a function that *should* take seconds reports `0 us` while printing a correct-looking answer. Force the whole value through a returned tuple, e.g. `let (out, dt) ← timeBatch 1 fun _ => f x` where `timeBatch` returns `(α × Nat)`, exactly the shape a bench harness should have. (3) **A warm-cache first call is not a measurement**, and neither is one run — batch `reps` and divide, and sanity-check by scaling `n` (a clean 4× time for 2× size means Θ(n²), which is usually a bug, not a constant factor). **Acceptance test: if any of your lanes reports `0 us`, treat it as "not measured" and fix the forcing — never as "instant".** Corollary: an A/B must differ in *exactly one* dimension; hold the types, the helpers, and the input identical, so the delta is attributable.

- 2026-10-27 — **`decide_eq_true (by omega)` on a *disjunction* leaks.** `decide_eq_true (by omega)` on a *disjunction* leaks `Classical.choice` — `omega` closes a `∨` by case analysis (trichotomy), so building the disjunct explicitly is the fix. `Classical.choice` — `omega` closes a `∨` by case analysis (trichotomy), so building the disjunct explicitly is the fix. `#print axioms` on `theorem t (n : Nat) (h : 65 ≤ n ∧ n ≤ 70) : decide ((48 ≤ n ∧ n ≤ 57) ∨ (65 ≤ n ∧ n ≤ 70)) = true := decide_eq_true (by omega)` reports `[propext, Classical.choice, Quot.sound]`, while `decide_eq_true (Or.inr h)` on the same goal is clean. `decide` is not the problem — the *disjunctive* proof handed to it is. This is the same `Nat.lt_or_gt_of_ne`/trichotomy family as the earlier `omega`-disjunction entry, but the composition trap is far more common and is easy to miss because the goal looks like plain arithmetic: **rule — in a `Classical.choice`-gated law, never hand `omega`/`by_contra`/`decide_eq_true` a disjunctive goal; build the disjunct with `Or.inl`/`Or.inr` and let `omega` close only the conjunctive/arithmetic leaf.**

- 2026-10-27 — **A `match`/`if` on a `Bool` in the goal is a dependent match.** A `match`/`if` on a `Bool` *in the goal* (with `h : b = true` in context) is a dependent match: `subst h; rfl` and `cases b` both fail. The symptoms are "`rfl` failed: the left-hand side `match true, ⋯` is not definitionally equal to …" and, for `cases`, "Dependent elimination failed". Neither is a `Classical.choice` leak — it is the motive mentioning the discriminee. Fix: `cases b <;> simp_all`, or restate so the match is not dependent (move the discriminee into a hypothesis), or prefer `if h : p then` to keep the fact in the branch. Recorded separately from the leak catalogue because the *fix* is different: no axiom problem, just a motive problem.

- 2026-10-27 — **`if_pos`/`if_neg` deprecated: use `ite_eq_left`/`ite_eq_right`.** `if_pos`/`if_neg` are deprecated in favour of `ite_eq_left`/`ite_eq_right` — and the replacements are *applied*, not `rw`-able and not `Iff`s. Both halves are deprecated (not just `if_neg`), so a repo-wide `if_pos`/`if_neg` habit emits warnings that a `-DwarningAsError` gate turns into build failures. The shapes are `ite_eq_left : c → (if c then t else e) = t` and `ite_eq_right : ¬c → … = e` — functions of a proof argument. Write `exact ite_eq_left h` or `rw [show (if P then a else b) = a from ite_eq_left h]`; `rw [ite_eq_left]` bare and `.mpr` **do not work** (no `Iff` projection to take).

- 2026-10-26 — **Bisecting a proof: extract the sub-argument, don't insert `sorry`.** When a proof refuses to compile and you want a clean slate, never `git stash`/`git reset`/`git checkout --` the file — move the broken *theorem* to a `sorry` instead, so the library still builds and you can iterate in a scratch file. Debugging a hard lemma, the library is unbuildable, so `lake env lean` on a scratch probe fails too ("olean does not exist") — which tempts a "revert and start over". Reverting broadly destroys verified sibling work (it did, mid-session). The cheap, safe move is to stub the one declaration (`:= by sorry`), let `lake build` go green, then iterate the real proof in `/tmp/probe.lean` against the built library — with `sorry` you also get the *goal state* printed, which is usually the fastest way out. Commit incrementally (one base / one law family per commit) so a revert is never tempting.

- 2026-10-26 — **`simp [f] at h` needs `f`'s match depth to match `h`'s.** `simp [f] at h` where `f` matches on a list *nested one level deeper* than `h` shows will leave an unreduced `match` — `rcases` the list down to a concrete length first. `b32TailUnapply (v0 :: w :: r2) = some a` reduces only after `r2` is known to be `[]`/`[_]`/`[_,_]`, because the `def`'s match covers 1–4-element lists; `simp only [unapply, blockUnapply, Option.some.injEq] at h` then `subst h; rfl` per arm is the reliable pattern, and the *impossible* arms (5+ elements) reduce to `none = some a` and close by `simp [unapply] at h` alone. Also: a `simp` argument reported "unused" in one arm is usually needed in the *other* arms — don't delete it globally, delete per-arm, or you trade a warning for a compile error.

- 2026-10-26 — **`dsimp only []` is not always a no-op.** `dsimp only []` is NOT always a no-op; "remove the no-op" can break the proof.
  A cleanup ticket called `dsimp only []` a no-op, but deleting it made a later `rw` fail
  "did not find an occurrence of the pattern". `dsimp only` with an empty list still performs
  beta/iota/zeta reduction — here it unfolded the `Option`/`Sigma` wrapper so the goal was
  stated in the `(n - t.remaining) + t.remaining` / `concat s₀ t.bytes` form the next step
  matched. Before "cleaning up" any `dsimp`/`simp only []`, delete it and recompile; if a
  later step stops matching, it was load-bearing — then replace it with an explicit
  `dsimp only` plus a comment saying why, rather than restoring an opaque `[]`.


- 2026-10-25 — **A *dependent* `cases`/`match` on a list whose .** equation** (not a bound) sits in the context is itself a `Classical.choice` leak — restate the hypothesis by *number* (`≤`/`<`) before matching.** Proving `exists cs, unapply bs = some cs` with the hypothesis `bs.length = 1 ∨ bs.length = 2` in scope and `match bs with | [v0] => … | [] => simp at h`, the proof term goes through `Eq.ndrec`/`noConfusion` (the `match`'s motive mentions `bs`), and `#print axioms` reports `Classical.choice` **even though every lemma you cite is `[propext]`-clean and the same proof with no hypothesis at all is clean**. Swapping the disjunctive equation for numeric bounds — `(hlen : 1 ≤ bs.length) (hlen2 : bs.length ≤ 2)`, then `match bs, hlen, hlen2 with` — makes the elimination non-dependent and the law `[propext, Quot.sound]`-only again. Diagnostic shape to remember: `#print axioms` says `Classical.choice`; bisect the *skeleton* (drop the body to `⟨_, rfl⟩`) and it still leaks ⇒ the leak is in the `match`/`cases`, not the arithmetic. Corollary: the same trap hits `Partial`-style length hypotheses `ds.length = k`, so **derive** the index from the term (`count ds.length …`, not `count k …` plus `ds.length = k`) rather than threading an abstract `k`. The general rule unifying all the `Classical.choice` entries in this file: a hypothesis whose *type mentions* the variable you are about to eliminate makes that elimination dependent, and dependent elimination reaches `Decidable`/`noConfusion` machinery that is not axiom-free.

- 2026-10-25 — **`simp at h` cannot close a list-length contradiction.** `simp at h` on a hypothesis `h : (a :: t).length = k` (or any list-length contradiction) can pull in `Classical.choice` (it reaches `List.length_eq_zero`/`Nat`-`Decidable` instances in the full context) — same family as the `omega`/`decide` leaks. In a `Classical.choice`-gated law, replace `simp at h` with an explicit `simp only [List.length_cons] at h; omega` (or `simp only [List.length_nil] at h; omega` for the `[]` case), where `omega` stays constructive on the resulting `Nat` arithmetic. Diagnose exactly as usual: `#print axioms <your theorem>` is the only authoritative gate; each cited lemma being clean is necessary but not sufficient, because the leak lands in a generated `_proof_*`.

- 2026-10-25 — **Proving two `Sigma`s equal across a length rewrite.** To prove `⟨n - k + k, concat x y⟩ = ⟨n, z⟩` (two `Sigma`s at *definitionally different but equal* lengths) you cannot `apply Sigma.ext` then `apply heq_of_eq` — `heq_of_eq` demands both sides in the *same* type, so it fails on `n - k + k` vs `n`. Three working shapes, in order of preference: (1) `have hlen : n - k + k = n := Nat.sub_add_cancel hle` and assemble `hsig : (⟨n-k+k, concat x y⟩ : Sigma fun m => Bytes m) = ⟨n, z⟩ := Sigma.ext hlen (by have h1 : HEq (concat x y) (cast (congrArg Bytes hlen.symm) z) := heq_of_eq hbytes; exact h1.trans (cast_heq (congrArg Bytes hlen.symm) z))`, where `hbytes : concat x y = cast (congrArg Bytes hlen.symm) z` is the pointwise byte equality — `cast_heq` supplies the `HEq` across the differing lengths; (2) better, `subst` the length away first (`st`/`t.bytes` at the same index) so no `Sigma.ext` on unequal lengths arises; (3) `cases hlen` **fails** with "dependent elimination" when `n` is also the `Bytes` index — do not reach for it. A residual `cast ⋯ t.bytes` in the goal after rewriting means the two `fst`s are not syntactically equal, and you are fighting the wrong shape.

- 2026-10-25 — **`omega`'s disjunction search leaks `Classical.choice`.** `omega`'s *disjunction* search (`k < n ⊢ k = 0 ∨ k = 1 ∨ … ∨ k = n-1`) leaks `Classical.choice` via `Nat.lt_or_gt_of_ne` (trichotomy); the clean fix is nested `cases k` + `omega` only** for the `False` contradiction.** The rejection/`hall`-style byte case commonly wants `k = 0 ∨ k = 1 ∨ … ∨ k = n-1` from `hk : k < n` for a free `k`. `omega` discharges it, but `#print axioms <.theorem>` reports `Classical.choice` because the generated proof turns `Nat.lt_or_gt_of_ne` / `Nat.lt_trichotomy` (both `Classical.choice`-dependent) — even though `#print axioms` on an *isolated* `theorem t (k) (hk : k < 4) : k = 0 ∨ … := by omega` is clean (context-dependent). The `#print axioms` gate is the *only* authoritative check; each named dependency being clean is necessary but **not** sufficient (the `_proof_*` subproofs like `YourThm._proof_1_4` are where the leak lands, visible via `#print axioms YourThm._proof_1_4`). Fix: `cases k with | zero => simp | succ k1 => cases k1 …` down to `n-1`, then the final `| succ k₍ₙ₋₁₎ => exfalso; omega` (a `False` goal, where `omega` stays constructive). Spell this once per width as a reusable `nat_lt_four` / `nat_lt_eight` in `Common` rather than inlining.


- 2026-10-25 — **`List.ofFn` head extraction: `List.ofFn_succ` + `List.head!`.** The clean `List.ofFn` head extraction is `List.ofFn_succ` + `List.head!`, *not* `List.getElem_ofFn` on a `Fin` index. To prove `s ⟨0, ·⟩ = c0` from `htail : List.ofFn s = [c0, c1, c2, c3]`: `have hsucc : List.ofFn s = s ⟨0, by decide⟩ :: List.ofFn (fun i : Fin 3 => s i.succ) := List.ofFn_succ; have hcons := … (rw [← hsucc, htail])…; have hhead := congrArg (fun l : List UInt8 => l.head!) hcons; simp [List.head!] at hhead` — `rfl` then closes `s ⟨0,·⟩ = c0`. The `List.getElem_ofFn` route fails because `(List.ofFn s).length` is **not** definitionally `n` (`List.length_ofFn` is a theorem, not `rfl`), so `by decide` on `0 < (List.ofFn s).length` reports "Expected type must not contain free variables"; `List.ofFn_succ` exposes the head as a raw `cons` and `head!` projects it with no `Fin`-length proof.


- 2026-10-24 — **`decide`/`omega` on a goal whose `Decidable` must be synthesised.** `decide`/`omega` on a goal whose `Decidable` must synthesize `∀ i : Fin n, P i` leaks `Classical.choice`; close the *free-`Fin`* byte case with `rcases i with ⟨k, hk⟩; rcases (k = 0 ∨ … ∨ k = n-1) with rfl | … <;> rfl`, never `decide`. When a rejection/roundtrip proof needs "byte `k` of this literal list is `b`" for `i : Fin n` with `i` a free variable, the naive `rw [hi]; decide` (with `hi : i = ⟨0⟩` via `Fin.eq_of_val_eq`) forces instance search for `Decidable (∀ i : Fin n, s₀ ⟨i…⟩.toNat = b)`, whose candidate list starts with `Classical.propDecidable` — the synthesized proof carries `Classical.choice` even though *every named lemma* you cited is `[propext, Quot.sound]`-clean (`#print axioms` on each will agree, while `#print axioms` on your theorem reports `Classical.choice`, and `Expr.getUsedConstants` shows no culprit — the leak is in an auto-generated `_proof_*`/`Decidable` instance, invisible to theme-pretty-printer). The clean spelling is `rcases i with ⟨k, hk⟩; have hk4 : k = 0 ∨ k = 1 ∨ … ∨ k = n-1 := by omega; rcases hk4 with rfl | rfl | … <;> rfl` — `rfl` reduces the `List.getElem` of the literal list at the now-concrete index with **no** `Decidable` search, and `#print axioms` is then `[propext, Quot.sound]`. (The proof of "`[65,65,65,65][i] = 65` for `i : Fin 4`" thus closes by `rfl`, not `decide` — and `simp [theByteList]` first `drop`s the literal prefix down to `[65,65,65,65][…]`.)


- 2026-10-24 — **`omega` on a `Nat`-subtraction trichotomy (`n - t.remaining = 0 →.** `omega` on a `Nat`-subtraction trichotomy (`n - t.remaining = 0 → t.remaining = n`) leaks `Classical.choice`; use `Nat.sub_eq_zero_iff_le.mp` + `Nat.le_antisymm` instead. t.remaining = n`) leaks `Classical.choice`; use `Nat.sub_eq_zero_iff_le.mp` + `Nat.le_antisymm` instead. To pin `t.remaining = n` from `n - t.remaining = 0` given `t.remaining ≤ n`: `have hle : n ≤ t.remaining := Nat.sub_eq_zero_iff_le.mp hz; exact Nat.le_antisymm htle hle` (`Nat.sub_eq_zero_iff_le` is `[propext]`, `Nat.le_antisymm` is axiom-free). Similarly a `4 ≤ n - t.remaining` over a `hm : m ≤ n - t.remaining` + `hm₄ : m = 4` is `simpa [hm₄] using hm`, not `by omega`; and a `4 ≤ 2` contradiction is `Nat.le_trans h4 h2` → `False.elim ((by decide : ¬ (4:Nat) ≤ 2) h42)` or `cases h42`. The rule generalizes the skill's earlier "`Nat.mul_lt_mul_left` is `Classical.choice`-dependent" note to **sub-trichotomy**: `omega`/``decide`` on `Nat` `n-m` triggers `ofNat_sub_dichotomy`→`Classical.propDecidable` in the full dependent context even though an isolated `#print axioms` of the *same* `omega`/`decide` goal reports clean. The `#print axioms <your theorem>` is the only authoritative gate check; `#print axioms <each lemma>` being clean is necessary but **not** sufficient.


- 2026-10-24 — **Stdlib `Nat` `<`-cancellation lemmas are `Classical.choice`-dependent; the `≤`/`=` forms
  are clean.** `Nat.lt_of_mul_lt_mul_left`, `Nat.mul_lt_mul_left`, `Nat.lt_of_mul_lt_mul_right` all
  `#print axioms` to `[propext, Classical.choice, Quot.sound]` (they route through `Decidable`-`by_cases`),
  while `Nat.mul_le_mul_left`, `Nat.le_of_not_gt`, `Nat.lt_of_le_of_ne`, `Nat.succ_le_of_lt`,
  `Nat.add_left_cancel`, `Nat.sub_add_cancel`, `Nat.sub_sub_self` are `[propext]`-or-less. **For an
  axiom-gated law, `#print axioms <lemma>` *before* using any stdlib arithmetic lemma** — one `Classical.choice`
  in a single `Nat` step silently pushes the whole theorem off the `[propext, Quot.sound]` gate, and only
  `#print axioms <your theorem>` (not a green build) surfaces it. Replace `4*a < 4*b → a < b` with a tiny
  `private theorem … (h : 4*a < 4*b) : a < b := by omega` — `omega` is constructive.

- 2026-10-24 — **`omega` doesn't see field projections: surface them as `have`s.** `omega` does not see field projections (`t'.hle`, `i.isLt`): surface them as explicit `have`s.
  `omega` only uses *local binder* hypotheses, so `t' : Suffix n` contributes no `t'.remaining ≤ n` and `i : Fin k`
  contributes no `i.val < k`. Before `omega`, write `have hle : t'.remaining ≤ n := t'.hle` and
  `have hi : i.val < k := i.isLt`. The trap is worse in a **theorem statement's** `(by omega : i.val + L < m)`
  index annotation: that `omega` elaborates in the *statement* context (no `have`s in scope), so either inline
  the facts (`(by have hi := i.isLt; have hle := t'.hle; omega)`) or drop the annotation and pass the index proof
  as a named `(hidx : …)` parameter — the caller then closes the proof-term mismatch by proof irrelevance.

- 2026-10-24 — **`omega`'s Int-model emits *spurious* "counterexample may satisfy the constraints" on Nat
  subtraction inside a large context** (e.g. `m₁ + m₂ - t'.remaining` with `t'.remaining = 4·|rest|` and
  `m₂ < t'.remaining`; the model lets `a - b` go negative, so its `a - b ≤ -1` constraint violates the real
  `t'.hle`). Fix: don't hand `omega` the whole context with Nat-sub terms — first `rw` the equality hypotheses
  *into the goal* (`rw [← hL, ← hm₁len]` is safe on a plain Nat inequality, since only the goal's occurrences are
  rewritten), which leaves a clean `4*a < 4*b` / `4*a + 4 ≤ 4*b` fact, then finish with a minimal `omega` or a
  constructive `Nat.mul_le_mul_left` step. (`rw [hL]` fails differently when `hL`'s LHS is itself a *type index* —
  see the dependent-index entry below.)

- 2026-10-24 — **`rw [hm₂ : m₂ = 0]` fails with a dependent-motive error when `m₂` occurs in the *type* of a
  projection the goal mentions** — `t'.remaining` for `t' : Suffix (m₁ + m₂)`, even when the goal
  `(m₁ + m₂ - t'.remaining) + 4 ≤ m₁` is a plain Nat inequality. `rw` abstracts `m₂` everywhere in the goal,
  including inside `t'`'s type, and refuses. Use `simpa [hm₂] using t'.hle` (simp rewrites at the `Nat` level
  without abstracting the projection's type) or assemble the arithmetic explicitly (`Nat.sub_add_cancel t'.hle`,
  then `rw [h] at hsub`, then `Nat.add_left_cancel`) instead of `rw`-ing the equality.


- 2026-10-24 — **Do not fabricate paper provenance for your own derived combinators; verify the source
  actually defines them before writing "paper §X" in a docstring or README.** A faithful port adds
  combinators *in the spirit of* the source, but the paper only defines `many` (§3.4) and `chainl1` (§6.1);
  `sepBy`/`chainr1`/`optional`/`maybe`/`choice`/`count`/`manyUpTo` are the *port's own* additions and must be
  labeled as such ("not in the paper"), not cited to a section (§6.2 is the paper's *Abstract Syntax*,
  which defines no combinators at all). `grep` the source paper for each combinator name before citing it;
  a reviewer will.


- 2026-10-22 — **`termination_by` on a `where`-nested recursive proof must name the *helper's own* parameter, not the
  outer theorem's binder.** A `theorem f (bs) : … := exact go bs where go : (l : List α) → …` with `go` recursing
  three-elements-deep (`b0 :: b1 :: b2 :: t2 ↦ go t2`) needs `termination_by l => l.length` **inside `go`'s
  definition** (`decreasing_by …` right after the `where` cases) — writing `termination_by bs.length` after the whole
  theorem errors `Unknown identifier bs.length`. Also: `decreasing_by simp_arith` is **deprecated** (shorthand for
  `simp +arith +decide`); write `decreasing_by simp +arith` to stay zero-warning. A 3-deep/short-block-length recursion
  is the classic case where plain `induction` gives an IH only on the *immediate* tail, not the `t2` you need — use the
  `where` helper with its own `termination_by`.


- 2026-10-20 — **`simp` applies `or_self` (`p ∨ p ↔ p`), so `rcases` on a *deduplicated* disjunction after
  `simp` needs fewer patterns than the list length.**  `b ∈ [c0, c1, 61, 61]` simplifies to `b = c0 ∨ b = c1 ∨
  b = 61` (the duplicate `61` disjuncts merge), so `rcases hb with rfl | rfl | rfl` (3 arms), not 4.  This bites
  when a tail builder emits repeated `=` pads of the same literal; count *distinct* disjuncts after `simp`,
  not input list elements.


- 2026-10-20 — **`l ++ []` is not `rfl`-equal to `l`; in an induction step that emits `chars ++ []` vs the
  lemma's `chars`, `rw [← List.append_nil chars]` first (it rewrites `chars` to `chars ++ []`).** A total
  char-emitter `chars : B → List UInt8` leaves the `full/tail` case goal as `parse (chars)`, while the helper
  lemma is stated as `parse (chars' ++ rest) = …`; for the `rest = []` base, `simpa`/`rw` do not see the `++ []`,
  so insert `rw [← List.append_nil <chars>]` to align, then `rw [helper … []]`. (`List.append_nil : l ++ [] =
  l`; the `←` direction is `l = l ++ []`.


- 2026-10-19 — **`Nat.div_add_mod` puts the *divisor* first.** `Nat.div_add_mod m n` returns `n * (m / n) + m % n = m` — the *divisor first*.
  To get the `(m/n) * n + m%n = m` form a digit-sum identity needs, `simpa [Nat.mul_comm] using
  Nat.div_add_mod m n`.  `omega` does *not* commute it for you, and an `omega`-only digit reconstruction
  (`(v/64)*64 + ((v/8)%8)*8 + v%8 = v`) closes with just `have h1 := Nat.div_add_mod v 64; have h2 :=
  Nat.div_add_mod v 8; omega` — but **only** when the divisor-first form is in the local context; `omega`
  alone does not unfold `(v/8) % 8`.


- 2026-10-19 — **`decide` lemmas:.** the iff is `decide_eq_true_eq : (decide p = true) = p`; the one-direction
  forward is `of_decide_eq_true : decide p = true → p`; there is **no** `decide_eq_false_eq` (the mirror is
  `decide_eq_false : ¬ p → decide p = false` / `of_decide_eq_false`).  For a *left-associative* `&&` chain
  `(P && Q && R) = true`, decompose with `(Bool.and_eq_true_iff.mp hv).1 : (P && Q) = true` then
  `(Bool.and_eq_true_iff.mp that).1 : P = true` / `.2 : Q = true`, and `(Bool.and_eq_true_iff.mp hv).2 : R =
  true` — `hv.1`/`hv.2.2` on a `Bool` equality is an "invalid projection" (a `Bool` equality has no fields).
  Close a `(true && true && true) = true` residual (the `if (b : Bool)` desugars to `if b = true`) with
  `have hh : (true && true && true) = true := by decide; rw [hh]` — `simp`/`#reduce` do **not** reduce `=
  true` on its own.


- 2026-10-19 — **`by_contra` needs `Classical` (or a `[Decidable]`/`Fintype` instance).** In a
  stdlib-only, `[propext, Quot.sound]`-only library (`no mathlib`, no `Classical.choice`), `by_contra` is
  **not** available; proving `octToVal e ≤ 7 ⇒ 48 ≤ e` from `octValid e = true` must be done with `by_cases
  hle : e ≤ 55 <;> by_cases hge : 48 ≤ e` and `omega` in each branch (the invalid branches yield
  `octToVal e = 8`, contradicting `≤ 7`).  Do not reach for `by_contra`/`classical` in such a library — it
  breaks the axiom gate.


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

- 2026-10-18 — **A `ByteArray`-vs-C comparison against a semantic parser must be apples-to-apples;
  C `strptime`/`date`-style parsing is ~10 ns/op on a 23-byte record, vs ~200-400 ns for the boxed
  pure-Lean equivalent.** When someone asks "can Lean parse as fast as C", the concrete answer is a
  head-to-head: a hand-written `clang -O2` RFC 3339 parser (uint32 registers, no alloc) is ~10 ns/op,
  and no pure-Lean reshaping gets under ~20x that because the per-digit `acc*10+d` is bignum-boxed.
  The honest framing is a *ratio to the same-machine C baseline*, not an absolute MiB/s number.

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
