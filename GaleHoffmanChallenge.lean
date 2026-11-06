/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Feasible flows, circulations and 0-1 matrices (Gale 1957, Hoffman 1960)

A network on a finite set `N` of nodes is a capacity function `c : N → N → ℝ` with `c ≥ 0`.
Following Gale, a flow is a function `f : N → N → ℝ` with `f x y + f y x = 0` and
`f x y ≤ c x y`; a demand `d : N → ℝ` is feasible if some flow has net inflow
`∑ y, f y x ≥ d x` at every node. For a set `S` of nodes, `Sᶜ` is its complement, `d(Sᶜ)` is
`∑ x ∈ Sᶜ, d x` and `c(S, Sᶜ)` is `∑ x ∈ S, ∑ y ∈ Sᶜ, c x y`.

* `GaleHoffman.feasibility`: **Gale's feasibility theorem.** The demand `d` is feasible if and
  only if `d(Sᶜ) ≤ c(S, Sᶜ)` for every `S`.
* `GaleHoffman.feasibility_int`: the same for integer capacities and demands, with an
  integer-valued flow (Gale's remark).
* `GaleHoffman.feasibility_second`: Gale's second formulation of the feasibility theorem.
* `GaleHoffman.gale_ryser_unsorted`, `GaleHoffman.gale_ryser`: Gale's criterion for a `0`-`1`
  matrix with row sums at most `a i` and column sums `b j` (Gale 1957, §3), and
  `GaleHoffman.gale_ryser_exact`: the Gale–Ryser theorem (row sums exactly `a i`).
* `GaleHoffman.hoffman`, `GaleHoffman.hoffman_int`: **Hoffman's circulation theorem.** On a
  finite directed multigraph (arcs `A`, tail `src`, head `tgt`) with bounds `d ≤ c` on the arcs,
  there is a circulation `f` with `d ≤ f ≤ c` if and only if `d(δ^in(U)) ≤ c(δ^out(U))` for every
  set `U` of vertices; for integral `d` and `c` the circulation can be chosen integral (Schrijver,
  *A Course in Combinatorial Optimization*, Theorems 4.6 and 4.7).

The Mathlib definitions used in these statements are listed in `MATHLIB_DEFINITIONS.md` at the
root of this repository.
-/

@[expose] public section

namespace GaleHoffman

/-- **Gale's feasibility theorem** (Gale 1957). For nonnegative real capacities `c`, a demand `d`
is feasible (some flow `f`, antisymmetric and bounded by `c`, has net inflow at least `d x` at every
node `x`) if and only if `d(Sᶜ) ≤ c(S, Sᶜ)` for every set `S` of nodes. -/
theorem feasibility {N : Type*} [Fintype N] [DecidableEq N] (c : N → N → ℝ)
    (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    (∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y := by
  sorry

/-- **Gale's feasibility theorem, integral version** (Gale 1957, Remark). For nonnegative integer
capacities and integer demands, there is an integer-valued flow satisfying the demand if and only
if `d(Sᶜ) ≤ c(S, Sᶜ)` for every set `S` of nodes. -/
theorem feasibility_int {N : Type*} [Fintype N] [DecidableEq N] (c : N → N → ℤ)
    (hc : ∀ x y, 0 ≤ c x y) (d : N → ℤ) :
    (∃ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y := by
  sorry

/-- **Second formulation of the feasibility theorem** (Gale 1957). The demand `d` is feasible if
and only if, for every set `Y` of nodes of positive demand, some flow meets the demand at every node
of nonpositive demand and the aggregate demand of `Y`. -/
theorem feasibility_second {N : Type*} [Fintype N] (c : N → N → ℝ)
    (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    (∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ Y : Finset N, (∀ y ∈ Y, 0 < d y) →
        ∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
          (∀ x, d x ≤ 0 → d x ≤ ∑ y, f y x) ∧ ∑ x ∈ Y, d x ≤ ∑ x ∈ Y, ∑ y, f y x := by
  sorry

/-- **Gale's Problem I, unsorted criterion** (Gale 1957, §3). There is a `0`-`1` matrix with row
sums at most `a i` and column sums `b j` if and only if `∑_{j ∈ Y} b j ≤ ∑_i min (a i) |Y|` for
every set `Y` of columns. -/
theorem gale_ryser_unsorted {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ Y : Finset (Fin n), ∑ j ∈ Y, b j ≤ ∑ i, min (a i) Y.card := by
  sorry

/-- **Gale's criterion for Problem I** (Gale 1957, §3). With `b` nonincreasing, there is a
`0`-`1` matrix with row sums at most `a i` and column sums `b j` if and only if
`∑_{j < k} b j ≤ ∑_{j < k} a*_j` for every `k ≤ n`, where `a*_j = #{i | j < a i}` is the dual
sequence of `a`. -/
theorem gale_ryser {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card := by
  sorry

/-- **The Gale–Ryser theorem.** If `∑ a = ∑ b` and `b` is nonincreasing, there is a `0`-`1`
matrix with row sums `a i` and column sums `b j` if and only if `∑_{j < k} b j ≤ ∑_{j < k} a*_j`
for every `k ≤ n`. -/
theorem gale_ryser_exact {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b)
    (hab : ∑ i, a i = ∑ j, b j) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j = a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card := by
  sorry

/-- **Hoffman's circulation theorem** (Hoffman 1960; Schrijver, Theorem 4.6). On a finite
directed multigraph with arcs `A`, tail map `src` and head map `tgt`, and real bounds `d ≤ c` on
the arcs, there is a circulation `f` (inflow equals outflow at every vertex) with `d ≤ f ≤ c` if
and only if `d(δ^in(U)) ≤ c(δ^out(U))` for every set `U` of vertices. -/
theorem hoffman {V A : Type*} [Finite V] [DecidableEq V] [Fintype A] (src tgt : A → V)
    (d c : A → ℝ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℝ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a := by
  sorry

/-- **Hoffman's circulation theorem, integral version** (Schrijver, Theorem 4.7). With integer
bounds `d ≤ c`, there is an integer circulation `f` with `d ≤ f ≤ c` if and only if
`d(δ^in(U)) ≤ c(δ^out(U))` for every set `U` of vertices. -/
theorem hoffman_int {V A : Type*} [Finite V] [DecidableEq V] [Fintype A] (src tgt : A → V)
    (d c : A → ℤ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℤ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a := by
  sorry

end GaleHoffman
