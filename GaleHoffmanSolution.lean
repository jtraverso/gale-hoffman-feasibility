/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GaleHoffmanLib.Circulation
public import GaleHoffmanLib.GaleRyser

/-!
# Proofs of the statements in `GaleHoffmanChallenge.lean`

The theorems are proved in `GaleHoffmanLib/` (namespace `GaleFlows`). `Feasibility.lean` proves
Gale's feasibility theorem as Gale does, by adding a source and a sink and applying the
max-flow/min-cut theorem of the registered entry PALOMAR-2026-10-15-000008
(`LeanPool.MaxFlowMinCut`, a pinned dependency); the integral version uses the integral max-flow
theorem of the registered entry PALOMAR-2026-11-06-000003 (`BaranyaiLib.IntegralFlow`, a pinned
dependency). `Circulation.lean` derives Hoffman's theorem from Gale's (over `ℝ` and over `ℤ`),
and `GaleRyser.lean` derives Gale's criterion for `0`-`1` matrices from the integral feasibility
theorem on the bipartite network with unit capacities.
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
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y :=
  GaleFlows.feasibility c hc d

/-- **Gale's feasibility theorem, integral version** (Gale 1957, Remark). For nonnegative integer
capacities and integer demands, there is an integer-valued flow satisfying the demand if and only
if `d(Sᶜ) ≤ c(S, Sᶜ)` for every set `S` of nodes. -/
theorem feasibility_int {N : Type*} [Fintype N] [DecidableEq N] (c : N → N → ℤ)
    (hc : ∀ x y, 0 ≤ c x y) (d : N → ℤ) :
    (∃ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y :=
  GaleFlows.feasibility_int c hc d

/-- **Second formulation of the feasibility theorem** (Gale 1957). The demand `d` is feasible if
and only if, for every set `Y` of nodes of positive demand, some flow meets the demand at every node
of nonpositive demand and the aggregate demand of `Y`. -/
theorem feasibility_second {N : Type*} [Fintype N] (c : N → N → ℝ)
    (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    (∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ Y : Finset N, (∀ y ∈ Y, 0 < d y) →
        ∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
          (∀ x, d x ≤ 0 → d x ≤ ∑ y, f y x) ∧ ∑ x ∈ Y, d x ≤ ∑ x ∈ Y, ∑ y, f y x :=
  GaleFlows.feasibility_second c hc d

/-- **Gale's Problem I, unsorted criterion** (Gale 1957, §3). There is a `0`-`1` matrix with row
sums at most `a i` and column sums `b j` if and only if `∑_{j ∈ Y} b j ≤ ∑_i min (a i) |Y|` for
every set `Y` of columns. -/
theorem gale_ryser_unsorted {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ Y : Finset (Fin n), ∑ j ∈ Y, b j ≤ ∑ i, min (a i) Y.card :=
  GaleFlows.gale_ryser_unsorted a b

/-- **Gale's criterion for Problem I** (Gale 1957, §3). With `b` nonincreasing, there is a
`0`-`1` matrix with row sums at most `a i` and column sums `b j` if and only if
`∑_{j < k} b j ≤ ∑_{j < k} a*_j` for every `k ≤ n`, where `a*_j = #{i | j < a i}` is the dual
sequence of `a`. -/
theorem gale_ryser {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card :=
  GaleFlows.gale_ryser a b hb

/-- **The Gale–Ryser theorem.** If `∑ a = ∑ b` and `b` is nonincreasing, there is a `0`-`1`
matrix with row sums `a i` and column sums `b j` if and only if `∑_{j < k} b j ≤ ∑_{j < k} a*_j`
for every `k ≤ n`. -/
theorem gale_ryser_exact {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b)
    (hab : ∑ i, a i = ∑ j, b j) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j = a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card :=
  GaleFlows.gale_ryser_exact a b hb hab

/-- **Hoffman's circulation theorem** (Hoffman 1960; Schrijver, Theorem 4.6). On a finite
directed multigraph with arcs `A`, tail map `src` and head map `tgt`, and real bounds `d ≤ c` on
the arcs, there is a circulation `f` (inflow equals outflow at every vertex) with `d ≤ f ≤ c` if
and only if `d(δ^in(U)) ≤ c(δ^out(U))` for every set `U` of vertices. -/
theorem hoffman {V A : Type*} [Finite V] [DecidableEq V] [Fintype A] (src tgt : A → V)
    (d c : A → ℝ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℝ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a :=
  GaleFlows.hoffman src tgt d c hdc

/-- **Hoffman's circulation theorem, integral version** (Schrijver, Theorem 4.7). With integer
bounds `d ≤ c`, there is an integer circulation `f` with `d ≤ f ≤ c` if and only if
`d(δ^in(U)) ≤ c(δ^out(U))` for every set `U` of vertices. -/
theorem hoffman_int {V A : Type*} [Finite V] [DecidableEq V] [Fintype A] (src tgt : A → V)
    (d c : A → ℤ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℤ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a :=
  GaleFlows.hoffman_int src tgt d c hdc

end GaleHoffman
