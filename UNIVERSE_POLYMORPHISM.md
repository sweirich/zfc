# Universe polymorphism and 'Big' an inaccessible cardinal

This note records the design rationale behind the universe-polymorphism
changes to the ZFC development. 

## Motivation

`Hierarchy.v` is "a step towards inaccessible cardinals": it defines the
*small* sets and collects them into a single set `Big`. Because Rocq did not
originally support universe polymorphism, the development duplicated the core
definitions of `Sets.v`/`Axioms.v` there — `Ens'`, `EXType'`, `prod_t'`,
`depprod''`, `EQ'`, `Power'` — just to obtain a copy living at a lower
universe.

Rocq now supports universe polymorphism, so the small sets can simply be the
*same* definitions instantiated at a strictly lower universe. The duplicated
inductives and definitions in `Hierarchy.v` were removed.

## What was made polymorphic (`Sets.v` / `Axioms.v`)

Only the handful of building blocks that the small-sets construction needs at
a *second* universe level were made universe polymorphic:

- `Ens` — the type of sets (`Sets.v`)
- `depprod` — dependent product on `Type` (`Sets.v`)
- `EQ` — extensional equality on sets (`Sets.v`)
- `Power` — the powerset (`Axioms.v`)

This is deliberately minimal: the file is *not* globally polymorphised. Every
theorem stays monomorphic, so existing proofs — which
rely on a single universe instance — are unaffected.

### `Ens` is also cumulative

`Ens` is declared `Polymorphic Cumulative`, so a lower-universe `Ens` is a
subtype of a higher one. Without cumulativity, monomorphic set-builders such
as `Vide` (whose universe minimises to `Set`) could not be passed to
operations whose `Ens` universe floats higher, e.g. `IN E Vide`.

### What was *not* changed

- **`EXType` stays monomorphic.** Were it polymorphic, `EQ` (which is built
  from it) would acquire extra floating universes whose per-occurrence
  variance breaks `fold`/`rewrite` in the quotient proofs of `lib/ZFSet.v`.
  `Hierarchy.v` uses plain `exists` instead of an `EXType` copy.

- **`depprod` stays non-cumulative** (polymorphic but not `Cumulative`).
  Making `EXType`/`depprod` cumulative perturbs `simpl`/`auto` in the `Power`
  proofs of `Axioms.v`.

## The small sets (`Hierarchy.v`)

Two universe levels are introduced:

```coq
Universe small big.
Constraint small < big.
```

The `small` sets sit strictly below the `big` universe in which `Big`, the
set of all small sets, lives. `small < big` is exactly what makes `Big`
"inaccessible" from below: it is not itself a small set.

- `Ens' := Ens@{small}` — the small sets (formerly the duplicated inductive
  `Ens'`).
- `inj : Ens' -> Ens@{big}` rebuilds each `sup` node at the big universe.
  With `small < big`, the index type `A : Type@{small}` is accepted by `sup`
  at the big universe through ordinary cumulativity.
- `Power_sound_inj` shows `inj` commutes with the powerset: the left `Power`
  is at the small universe and the right one at the big universe — the same
  polymorphic `Power`, replacing the former `Power'`.
