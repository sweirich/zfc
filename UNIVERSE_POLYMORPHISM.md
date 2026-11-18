# Universe polymorphism and `U0`, an inaccessible cardinal

This note records the design rationale behind the universe-polymorphism
changes to the ZFC development.

## Motivation

`Hierarchy.v` is "a step towards inaccessible cardinals": it defines the
*small* sets and collects them into a single set `U0` (called `Big` in the
original). Because Rocq did not originally support universe polymorphism, the
development duplicated the core definitions of `Sets.v`/`Axioms.v` there —
`Ens'`, `EXType'`, `prod_t'`, `depprod''`, `EQ'`, `Power'` — just to obtain a
copy living at a lower universe.

Rocq now supports universe polymorphism, so the small sets can simply be the
*same* definitions instantiated at a strictly lower universe. The duplicated
inductives and definitions in `Hierarchy.v` were removed.

## What is polymorphic (`Sets.v` / `Axioms.v`)

The definitions the small-sets construction needs at a second universe level
are declared polymorphic individually:

- `Ens` — the type of values (`Sets.v`), also `Cumulative` (below)
- `depprod` — dependent product on `Type` (`Sets.v`)
- `EQ` — extensional equality (`Sets.v`)
- `pi1`, `pi2` — the projections of a set (`Axioms.v`)
- `Power` — the powerset (`Axioms.v`)

Everything after these declarations is polymorphic too: `Sets.v` (from `IN`
on), `Axioms.v`, `Cartesian.v`, `Omega.v` and the other files that build on
them all `Set Universe Polymorphism`. (`zfc.v`, the original single-file
development with its own definitions, is left monomorphic.) With monomorphic theorems, every use of a lemma
pinned its `Ens` universe, so lemmas could not be applied to sets at two
different levels (e.g. `Hierarchy.v` uses them at both `small` and `big`).

### `Unset Universe Minimization ToSet`

Each polymorphic file also `Unset`s `Universe Minimization ToSet`. Without
it, the unconstrained `Ens` universe of a lemma is collapsed to `Set`, pinning
e.g. `Union_sound` to `Ens@{Set}`, so it could no longer be applied to
`big`-level sets in `Hierarchy.v`.

### `Ens` is cumulative

`Ens` is declared `Polymorphic Cumulative`, so a lower-universe `Ens` is a
subtype of a higher one. Without cumulativity, set-builders such as `Vide`
(whose universe minimises to `Set`) could not be passed to operations whose
`Ens` universe floats higher, e.g. `IN E Vide`.

### What stays monomorphic

- **`EXType` and `prod_t` are monomorphic.** Were `EXType` polymorphic, `EQ`
  (which is built from it) would acquire extra floating universes whose
  per-occurrence variance breaks `fold`/`rewrite` in a downstream quotient
  development built on these files. `Hierarchy.v` uses plain `exists` instead
  of an `EXType` copy.

- **`depprod` is non-cumulative** (polymorphic but not `Cumulative`).
  Making `EXType`/`depprod` cumulative perturbs `simpl`/`auto` in the `Power`
  proofs of `Axioms.v`.

## Atoms and pairs

`Ens` has two constructors besides `sup`: `atom n` (a natural number) and
`pair a b` (a primitive ordered pair). Neither has members, and `EQ` is
`False` across sorts; see the header of `Sets.v`. For the hierarchy this means:

- `inj` keeps atoms and rebuilds pairs componentwise, so atoms and pairs of
  small values are small (`U0_contains_atom`, `U0_closed_pair`).
- The numerals are atoms (`Nat n := atom n`), so `Omega` is small via
  `Omega_s := sup nat Nat_s` (`U0_contains_Omega`).

## The small sets (`Hierarchy.v`)

Two universe levels are introduced:

```coq
Universe small big.
Constraint small < big.
```

The `small` sets sit strictly below the `big` universe. `small < big` is
exactly what makes `U0` "inaccessible" from below: it is not itself a small
set.

- `Ens' := Ens@{small}` — the small sets (formerly the duplicated inductive
  `Ens'`).
- `inj@{j} : Ens' -> Ens@{j}` rebuilds each node at a target universe `j`
  above `small`. With `small < j`, the index type `A : Type@{small}` is
  accepted by `sup` at `j` through ordinary cumulativity.
- `U0@{j} := sup Ens' inj@{j}` is the set of small sets.
- `Power_sound_inj` shows `inj` commutes with the powerset: the left `Power`
  is at the small universe and the right one at `j` — the same polymorphic
  `Power`, replacing the former `Power'`. `inj_Paire_s`, `inj_Union_s`,
  `inj_Class_succ_s` and `inj_Omega_s` do the same for the other set-formers,
  from which `U0` is closed under `Power`, `Paire`, `Union`, `pair` and
  contains `Vide`, the atoms and `Omega`.

## The next level: `U1`

A third level `huge` with `big < huge` gives `U1 := Univ@{big huge}`, the set
of all `Ens@{big}` values, with `U0_in_U1` and `U1_transitive`. `Univ@{i j}`
and the injection `injp@{i j}` are the level-generic versions of `U0`/`inj`.
`injp_inj` relates instances of `inj` at different levels: `inj`/`U0` are
not cumulative, so `inj@{j} E` and `inj@{k} E` are not convertible, only
`EQ`.
