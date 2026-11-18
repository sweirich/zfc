# Atoms (natural numbers) and primitive pairs

This note records the change of `Ens` from pure sets to a type of *values*
with three sorts, and what it changed in each file. For the universe
polymorphism changes, see `UNIVERSE_POLYMORPHISM.md`.

## Motivation

In the original development every value is a set: a numeral is a von
Neumann ordinal and an ordered pair is the Kuratowski-style encoding
`Paire (Sing E) (Paire Vide (Sing E'))`. Using these sets as the semantic
domain of a programming language causes confusion between values. `Nat 0` is
the empty set, which is also the empty graph, and `Nat (S k)` contains it, so
a numeral can be a function. In the same way, projecting a component out of
an encoded pair takes a proof instead of a computation.

Making numbers and pairs their own sorts keeps them disjoint from sets and
from each other, and makes the projections of a pair definitional.

## The new `Ens` (`Sets.v`)

```coq
Polymorphic Cumulative Inductive Ens : Type :=
  | atom : nat -> Ens
  | pair : Ens -> Ens -> Ens
  | sup : forall A : Type, (A -> Ens) -> Ens.
```

- **`EQ`** compares two atoms by their numbers, two pairs componentwise and
  two sets extensionally as before. It is `False` across sorts.
- **`IN`** is as before when the container is a set. Atoms and pairs have no
  members.
- **`INC`** treats non-sets specially. A set is included in anything that
  contains all of its members. An atom or a pair is included only in
  something `EQ` to itself. With the member condition alone, every non-set
  would be a subset of everything, and two distinct atoms would include each
  other. With this definition `INC_EQ` (antisymmetry) still holds without any
  premise about sorts.
- New: the sort predicates `is_atom`, `is_pair`, `is_set` with
  `EQ_is_atom`/`EQ_is_pair`/`EQ_is_set`, `IN_is_set`, `IN_atom`, `IN_pair`,
  `EQ_atom_atom`, `EQ_pair_pair`, `pair_sound`, `INC_intro` and `INC_elim`.

## The set-formers (`Axioms.v`)

Every set-former (`Paire`, `Sing`, `Comp`, `Union`, `Inter`, `Power`) returns
a set. The ones that take apart their argument (`Comp`, `Union`, `Inter`,
`Power`) return `Vide` when applied to a non-set; `Paire` and `Sing` accept
any values as members. `pi1` of a non-set is the empty type. New `*_is_set`
lemmas state that each result is a set.

Four lemmas that recover a set from its members take an `is_set` premise,
because a non-set would make them false: `INC_IN_Power`, `Power_mon`,
`tout_vide_est_Vide` and `IN_INC_Union`.

## Pairs (`Cartesian.v`)

`Couple E E' := pair E E'`. Injectivity (`Couple_inj_left`/`_right`) is now
the `pair` clause of `EQ`. A couple has no members (`IN_Couple`) and is not a
set (`Couple_not_set`). `Prod` is unchanged, the set of couples of members,
and every member of a product is a pair (`IN_Prod_is_pair`).

## Natural numbers (`Omega.v`)

`Nat n := atom n`, and `Omega := sup nat Nat` is the set of all atoms.
Numerals have no members (`IN_Nat`), are injective (`Nat_inj`) and are not
sets (`Nat_not_set`). `Class_succ` is kept as an operation on sets but is no
longer related to `Nat`.

Removed:
- `Omega_EQ_Union` (`Omega = ⋃ Omega`). It is false now: the members of
  `Omega` are atoms, so its union is empty.
- `Vee`, the cumulative hierarchy. It moved to `Ordinal_theory.v`, its only
  user.

`Nat_Ord` and `Omega_Ord` were already commented out in the original.
`IN_Nat_EXType` now holds vacuously.

## The small sets (`Hierarchy.v`)

`inj` keeps atoms and rebuilds pairs componentwise. Atoms are small
(`U0_contains_atom`), small values are closed under pairing
(`U0_closed_pair`), and the components of a small pair are small
(`IN_U0_pair_inv`). `Omega` is small through `Omega_s := sup nat Nat_s`
(`U0_contains_Omega`). The closure proofs for the set-formers get a trivial
case for non-sets.

## Ordinals (`Plump.v`, `Ordinal_theory.v`)

Ordinals are sets: `ord` is `False` on an atom or a pair, and `Ord_is_set`
states it. Two statements take a new `is_set` premise because a non-set would
satisfy their other hypotheses vacuously: `ord_tech` (on `E2`) and
`Ord_intro` (on `E`).

`Vee` is defined in `Ordinal_theory.v`, with `Vee` of an atom or a pair
being `Vide`. Every member of a `Vee L` is a set, so an atom has no rank, and
neither does any set that contains one, e.g. `Omega`. The rank theorem
`ex_rk` therefore takes a premise `pure E`: `E` is a set and so is every
member, all the way down.

## Constructive sets (`Constructive.v`)

Aczel's `Type`-valued `EQC`, `CIN` and `CINC` follow `EQ`, `IN` and `INC`:
the same atom and pair clauses, and the same special treatment of non-sets
in `CINC`. `tout_vide_est_VideC` and `CIN_CINC_Union` take an `is_set`
premise, as their `Axioms.v` versions do. New: `CINC_intro`, `CINC_elim`,
`pi2_CIN`.

## Collection and replacement (`Replacement.v`)

Only `Choice_Collection` changed: an atom or a pair has no members, so
`Vide` serves as its collection.

## Unchanged

`Russell.v` needs no change. `zfc.v` is the original single-file
development with its own definition of `Ens`. It does not import the other
files and still uses pure sets.
