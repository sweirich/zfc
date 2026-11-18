# Use of AI in the modifications

The original development is by Benjamin Werner (INRIA, 1996–1999) and later
maintainers of the Coq/Rocq contributions; see the `rocq-archive/zfc` history.
It was written without AI tools.

The modifications in this fork, made by Stephanie Weirich in 2026, were
produced with Claude, an AI model by Anthropic, used through Claude Code. The
work was directed by the author. Claude wrote most of the changed Rocq code
and the accompanying documentation.

## What was AI-assisted

- **Universe polymorphism**: `Sets.v`, `Axioms.v`, `Hierarchy.v`, the port of
  `elimtype` uses in `Cartesian.v` and `zfc.v`, and `UNIVERSE_POLYMORPHISM.md`.
  Commit `2e47382` (2026-07-12) records Claude Opus 4.8 as co-author. Later
  extensions (polymorphic theorems, the `U1` level in `Hierarchy.v`) were
  developed in the author's `verse-paper` repository with Claude Opus 4.8.
- **Atoms and primitive pairs** in `Sets.v`, `Axioms.v`, `Cartesian.v`,
  `Omega.v` and `Hierarchy.v`. Developed in the `verse-paper` repository with
  Claude Fable 5.1 (commit `88d543b3`, 2026-09-15).
- **Port of `Plump.v`, `Ordinal_theory.v`, `Constructive.v` and
  `Replacement.v`** to the new `Ens`, the change notices at the top of each
  modified file, `ATOMS_AND_PAIRS.md`, the update to `UNIVERSE_POLYMORPHISM.md`,
  and this file. Done with Claude Opus 5.5 (2026-11-18).

Git commits that include AI-generated changes carry a `Co-Authored-By: Claude …`
trailer.

## Checking

Every theorem is checked by Rocq. No file contains `Admitted`, `admit` or
`Axiom`, and `Print Assumptions` reports the main results (e.g. `ex_rk`,
`U0_closed_for_power`, `U0_in_U1`, `Union_soundC`,
`classical_Collection_Replacement`) as closed under the global context. The
proofs themselves therefore do not depend on trusting the AI. What does
depend on review is that the *statements* and *definitions* say what is
intended: the definitions of `Ens`, `EQ`, `IN`, `INC` and `ord`, and the
premises added to existing theorems (listed in `ATOMS_AND_PAIRS.md`).
