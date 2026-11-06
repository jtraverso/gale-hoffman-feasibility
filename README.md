# Gale's feasibility theorem, Gale–Ryser and Hoffman's circulation theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of

- D. Gale, *A theorem on flows in networks*, Pacific J. Math. 7 (1957) 1073–1082
  ([doi:10.2140/pjm.1957.7.1073](https://doi.org/10.2140/pjm.1957.7.1073),
  [PDF](https://msp.org/pjm/1957/7-2/pjm-v7-n2-p04-s.pdf)): the Feasibility Theorem, its
  integral version, its second formulation, and the criterion for 0-1 matrices with given line sums
  (§3; with equal totals this is the Gale–Ryser theorem);
- Hoffman's circulation theorem (A. J. Hoffman, Proc. Sympos. Appl. Math. 10, AMS, 1960, 113–127,
  [doi:10.1090/psapm/010/0114759](https://doi.org/10.1090/psapm/010/0114759)), in the form of
  A. Schrijver, *A Course in Combinatorial Optimization* (version of 23 March 2017,
  [PDF](https://homepages.cwi.nl/~lex/files/dict.pdf)), Theorems 4.6 and 4.7.

## Statements (`GaleHoffmanChallenge.lean`, namespace `GaleHoffman`)

A network is a finite type `N` with capacities `c : N → N → ℝ`, `c ≥ 0`. A flow is
`f : N → N → ℝ` with `f x y + f y x = 0` and `f ≤ c`; a demand `d : N → ℝ` is feasible if some
flow has net inflow `∑ y, f y x ≥ d x` at every node `x`.

| Lean | Statement |
|---|---|
| `feasibility` | `d` is feasible iff `d(Sᶜ) ≤ c(S, Sᶜ)` for every `S ⊆ N` (Gale's Feasibility Theorem). |
| `feasibility_int` | The same with integer `c`, `d` and an integer flow (Gale's remark). |
| `feasibility_second` | `d` is feasible iff for every set `Y` of nodes of positive demand some flow meets the demand at every node of nonpositive demand and the aggregate demand of `Y` (Gale's second formulation). |
| `gale_ryser_unsorted` | A 0-1 matrix with row sums `≤ a i` and column sums `b j` exists iff `∑_{j ∈ Y} b j ≤ ∑_i min (a i) ‖Y‖` for every column set `Y`. |
| `gale_ryser` | For `b` nonincreasing: such a matrix exists iff `∑_{j<k} b j ≤ ∑_{j<k} #{i ∣ j < a i}` for every `k ≤ n` (Gale's theorem on Problem I). |
| `gale_ryser_exact` | If moreover `∑ a = ∑ b`, a 0-1 matrix with row sums exactly `a` and column sums `b` exists iff the same condition holds (the Gale–Ryser theorem). |
| `hoffman` | On a finite directed multigraph (arcs `A`, tail `src`, head `tgt`) with real bounds `d ≤ c` on the arcs, there is a circulation `f` with `d ≤ f ≤ c` iff `d(δ^in(U)) ≤ c(δ^out(U))` for every `U ⊆ V` (Schrijver, Theorem 4.6). |
| `hoffman_int` | The same with integer bounds and an integer circulation (Schrijver, Theorem 4.7). |

The Mathlib definitions used in these statements are excerpted in `MATHLIB_DEFINITIONS.md`.

## Relation to the sources

- Capacities are finite (Gale also allows `+∞`); the ordered-group generality of Gale's remark is
  formalized for `ℝ` and `ℤ`.
- The Feasibility Theorem is proved as in Gale's paper: a source and a sink are added, the cut
  `(N + s, s')` is shown to be minimum under Gale's condition, and the max-flow/min-cut theorem
  gives the flow.
- The criterion for Problem I is derived from the integral Feasibility Theorem on the bipartite
  network with unit capacities through the unsorted criterion `gale_ryser_unsorted`, rather than
  through Gale's second formulation; the sorted form follows by an exchange argument and the
  identity `∑_i min (a i) k = ∑_{j<k} a*_j`.
- Hoffman's theorem is derived from Gale's: writing `f = d + g`, the net flow of `g` between two
  vertices is a Gale flow for the demand `d(δ^out(v)) - d(δ^in(v))` with capacities
  `∑ (c - d)` over parallel arcs, and conversely a Gale flow is split over the parallel arcs.
- Not formalized: Gale's `n`-step filling procedure, the duality `{a}** = {a}` of dual
  sequences, and Schrijver's Exercise 4.13.

## Dependencies

Mathlib (`v4.35.0-rc3`, `c55e6e7`) and two registered entries by the same author, pinned as lake
dependencies (no code is copied):

- [jtraverso/dross-fractional-triangle-decomposition](https://github.com/jtraverso/dross-fractional-triangle-decomposition)
  @ `7720b7b` (PALOMAR-2026-10-15-000008): finite max-flow/min-cut (`LeanPool.MaxFlowMinCut`);
- [jtraverso/baranyai-theorem](https://github.com/jtraverso/baranyai-theorem) @ `0ff6d6f`
  (PALOMAR-2026-11-06-000003): integral maximum flows (`BaranyaiLib.IntegralFlow`).

## Files

- `GaleHoffmanLib/Feasibility.lean`: Gale's auxiliary network, the Feasibility Theorem over `ℝ`
  and `ℤ`, and the second formulation.
- `GaleHoffmanLib/Circulation.lean`: Hoffman's circulation theorem from Gale's, over any ordered
  commutative ring for which Gale's theorem holds, instantiated for `ℝ` and `ℤ`.
- `GaleHoffmanLib/GaleRyser.lean`: Problem I and the Gale–Ryser theorem.

## Checking

```
lake build GaleHoffmanChallenge GaleHoffmanSolution
```

`GaleHoffmanChallenge.lean` states the theorems (with `sorry`) using only Mathlib;
`GaleHoffmanSolution.lean` restates them and proves them from the library. `comparator.json` lists
the eight compared theorems.

## AI disclosure

The Lean development was written by an AI agent (Claude Opus 5.5 in Claude Code) under the
author's direction, and mechanically verified (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`). The formalization is by a different author than the articles; their authors were
not involved.
