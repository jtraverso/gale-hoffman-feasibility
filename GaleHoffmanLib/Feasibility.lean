/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BaranyaiLib.IntegralFlow
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Gale's feasibility theorem

A network on a finite set `N` of nodes is a capacity function `c : N → N → ℝ` with `c ≥ 0`.
Following Gale (1957), a *flow* is a function `f : N → N → ℝ` with `f x y + f y x = 0` and
`f x y ≤ c x y`; a *demand* `d : N → ℝ` is *feasible* if some flow has net inflow
`∑ y, f y x ≥ d x` at every node `x`.

**Feasibility theorem** (`feasibility`). The demand `d` is feasible if and only if
`d(S') ≤ c(S, S')` for every set `S` of nodes, where `S'` is the complement of `S`.

The proof is Gale's: add a source and a sink, and apply the max-flow/min-cut theorem of the
registered entry PALOMAR-2026-10-15-000008 (`Contrib.MaxFlowMinCut`). The integral version
(`feasibility_int`, Gale's remark) uses the integral max-flow theorem of the registered entry
PALOMAR-2026-11-06-000003 (`Baranyai.exists_integral_maxflow`). The second formulation of the
theorem is `feasibility_second`.
-/

@[expose] public section

namespace GaleFlows

open Finset Contrib.MaxFlowMinCut

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ## Necessity (over any linearly ordered abelian group) -/

section Generic

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

omit [Fintype N] [DecidableEq N] in
/-- An antisymmetric function has zero total over `T × T`. -/
theorem sum_sum_antisymm_eq_zero (f : N → N → R) (hf : ∀ x y, f x y + f y x = 0)
    (T : Finset N) : ∑ x ∈ T, ∑ y ∈ T, f y x = 0 := by
  set A := ∑ x ∈ T, ∑ y ∈ T, f y x with hA
  have h1 : ∑ x ∈ T, ∑ y ∈ T, f x y = A := Finset.sum_comm
  have h2 : A + ∑ x ∈ T, ∑ y ∈ T, f x y = 0 := by
    rw [hA, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun x _ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun y _ => hf y x
  rw [h1] at h2
  rcases le_total A 0 with h | h
  · refine le_antisymm h ?_
    calc (0 : R) = A + A := h2.symm
      _ ≤ A + 0 := add_le_add_right h A
      _ = A := add_zero A
  · refine le_antisymm ?_ h
    calc A = A + 0 := (add_zero A).symm
      _ ≤ A + A := add_le_add_right h A
      _ = 0 := h2

/-- The net inflow into `S'` is bounded by the capacity from `S` to `S'`. -/
theorem inflow_le_cut (c f : N → N → R) (hf : ∀ x y, f x y + f y x = 0)
    (hfc : ∀ x y, f x y ≤ c x y) (S : Finset N) :
    ∑ x ∈ Sᶜ, ∑ y, f y x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y := by
  have hsplit : ∀ x, ∑ y, f y x = ∑ y ∈ S, f y x + ∑ y ∈ Sᶜ, f y x :=
    fun x => (Finset.sum_add_sum_compl S _).symm
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
    sum_sum_antisymm_eq_zero f hf Sᶜ, add_zero, Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hfc x y

/-- Necessity of Gale's condition. -/
theorem feasible_cond (c : N → N → R) (d : N → R) (f : N → N → R)
    (hf : ∀ x y, f x y + f y x = 0) (hfc : ∀ x y, f x y ≤ c x y)
    (hd : ∀ x, d x ≤ ∑ y, f y x) (S : Finset N) :
    ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y :=
  (Finset.sum_le_sum fun x _ => hd x).trans (inflow_le_cut c f hf hfc S)

end Generic

/-! ## The auxiliary network -/

/-- Capacities of Gale's auxiliary network on `Option (Option N)`: the source is `none`, the
sink is `some none`; the source feeds each supply node `x` with capacity `max (-d x) 0`, each
demand node `x` feeds the sink with capacity `max (d x) 0`. -/
def galeCap (c : N → N → ℝ) (d : N → ℝ) : Option (Option N) → Option (Option N) → ℝ
  | some (some x), some (some y) => c x y
  | none, some (some x) => max (-d x) 0
  | some (some x), some none => max (d x) 0
  | _, _ => 0

/-- Gale's auxiliary network. -/
noncomputable def galeNet (c : N → N → ℝ) (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    Network (Option (Option N)) where
  cap := galeCap c d
  capNonneg := by
    rintro (_ | _ | x) (_ | _ | y) <;>
      first
      | exact le_refl _
      | exact hc _ _
      | exact le_max_right _ _
  s := none
  t := some none
  st := by simp

section Aux

variable (c : N → N → ℝ) (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ)

@[simp] lemma galeNet_s : (galeNet c hc d).s = none := rfl
@[simp] lemma galeNet_t : (galeNet c hc d).t = some none := rfl
@[simp] lemma cap_xy (x y : N) : (galeNet c hc d).cap (some (some x)) (some (some y)) = c x y :=
  rfl
@[simp] lemma cap_sx (x : N) : (galeNet c hc d).cap none (some (some x)) = max (-d x) 0 := rfl
@[simp] lemma cap_xt (x : N) : (galeNet c hc d).cap (some (some x)) (some none) = max (d x) 0 :=
  rfl
@[simp] lemma cap_ss : (galeNet c hc d).cap none none = 0 := rfl
@[simp] lemma cap_st : (galeNet c hc d).cap none (some none) = 0 := rfl
@[simp] lemma cap_xs (x : N) : (galeNet c hc d).cap (some (some x)) none = 0 := rfl
@[simp] lemma cap_t (v : Option (Option N)) : (galeNet c hc d).cap (some none) v = 0 := by
  rcases v with _ | _ | _ <;> rfl

/-- **Extraction.** A flow of value at least the total demand restricts to a Gale flow
satisfying the demand. -/
theorem extract (F : Flow (galeNet c hc d)) (hF : ∑ x, max (d x) 0 ≤ F.value) :
    (∀ x y, F.f (some (some x)) (some (some y)) + F.f (some (some y)) (some (some x)) = 0) ∧
    (∀ x y, F.f (some (some x)) (some (some y)) ≤ c x y) ∧
    ∀ x, d x ≤ ∑ y, F.f (some (some y)) (some (some x)) := by
  refine ⟨fun x y => ?_, fun x y => F.capacitated (some (some x)) (some (some y)), fun x => ?_⟩
  · rw [F.skew (some (some x)) (some (some y))]; exact neg_add_cancel _
  -- the value is the flow into the sink
  set t : Option (Option N) := some none with ht_def
  have hft : F.f t t = 0 := by have := F.skew t t; linarith
  have hst : F.f none t ≤ 0 := by have := F.capacitated none t; simpa [t] using this
  let C : Cut (galeNet c hc d) := ⟨{t}ᶜ, by simp [t], by simp [t]⟩
  have hval : F.value = ∑ u ∈ ({t}ᶜ : Finset _), F.f u t := by
    rw [F.value_eq_flow_across C]
    have : (Finset.univ \ C.S) = {t} := by ext v; simp [C]
    rw [this]; simp [C]
  have hall : ∑ u, F.f u t = F.f none t + (F.f t t + ∑ y, F.f (some (some y)) t) := by
    rw [Fintype.sum_option, Fintype.sum_option]
  have hcompl : ∑ u ∈ ({t}ᶜ : Finset _), F.f u t + F.f t t = ∑ u, F.f u t := by
    rw [← Finset.sum_compl_add_sum {t}, Finset.sum_singleton]
  have hle : ∀ y ∈ (Finset.univ : Finset N), F.f (some (some y)) t ≤ max (d y) 0 :=
    fun y _ => F.capacitated (some (some y)) t
  have hsum : ∑ y, max (d y) 0 ≤ ∑ y, F.f (some (some y)) t := by linarith
  have heq : ∑ y, F.f (some (some y)) t = ∑ y, max (d y) 0 :=
    le_antisymm (Finset.sum_le_sum hle) hsum
  have hxt : F.f (some (some x)) t = max (d x) 0 :=
    ((Finset.sum_eq_sum_iff_of_le hle).1 heq) x (Finset.mem_univ x)
  -- conservation at `x`
  have hcons := F.conserved (some (some x)) (by simp) (by simp)
  rw [Fintype.sum_option, Fintype.sum_option] at hcons
  have hsx : F.f none (some (some x)) ≤ max (-d x) 0 := F.capacitated none (some (some x))
  have hxs : F.f (some (some x)) none = - F.f none (some (some x)) := F.skew _ _
  have hin : ∑ y, F.f (some (some y)) (some (some x)) = - ∑ y, F.f (some (some x)) (some (some y))
      := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => F.skew _ _
  have hmax := max_zero_sub_max_neg_zero_eq_self (d x)
  rw [hin]
  change F.f (some (some x)) none + (F.f (some (some x)) t + _) = 0 at hcons
  linarith

/-- Under Gale's condition every cut of the auxiliary network has capacity at least the total
demand. -/
theorem cut_ge (h : ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y)
    (C : Cut (galeNet c hc d)) : ∑ x, max (d x) 0 ≤ C.capacity := by
  classical
  set P : N → Prop := fun x => some (some x) ∈ C.S with hP
  have hs : (none : Option (Option N)) ∈ C.S := C.hs
  have ht : (some none : Option (Option N)) ∉ C.S := C.ht
  have e1 : ∀ g : Option (Option N) → ℝ, ∑ u ∈ C.S, g u = ∑ u, if u ∈ C.S then g u else 0 := by
    intro g; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have e2 : ∀ g : Option (Option N) → ℝ,
      ∑ v ∈ Finset.univ \ C.S, g v = ∑ v, if v ∈ C.S then 0 else g v := by
    intro g
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun v _ => by by_cases hv : v ∈ C.S <;> simp [hv]
  have hcap : C.capacity = ∑ x, (if P x then 0 else max (-d x) 0) +
      ∑ x, (if P x then max (d x) 0 + ∑ y, (if P y then 0 else c x y) else 0) := by
    unfold Cut.capacity
    rw [e1]
    simp only [e2, Fintype.sum_option, hs, ht, ite_true, ite_false, cap_st,
      cap_sx, cap_t, cap_xt, cap_xy]
    simp [P]
  -- Gale's condition for the set of original nodes on the source side
  set S : Finset N := Finset.univ.filter P with hS
  have hcond := h S
  have hc1 : ∑ x ∈ Sᶜ, d x = ∑ x, if P x then 0 else d x := by
    rw [Finset.compl_filter, Finset.sum_filter]
    simp only [ite_not]
  have hc2 : ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y = ∑ x, if P x then ∑ y, (if P y then 0 else c x y) else 0 :=
    by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.compl_filter, Finset.sum_filter]
    simp only [ite_not]
    rfl
  rw [hc1, hc2] at hcond
  have hpt : ∀ x, max (d x) 0 = (if P x then max (d x) 0 else 0) + (if P x then 0 else d x) +
      (if P x then 0 else max (-d x) 0) := by
    intro x
    have := max_zero_sub_max_neg_zero_eq_self (d x)
    by_cases hx : P x <;> simp only [hx, ite_true, ite_false] <;> linarith
  have hsplit : ∑ x, (if P x then max (d x) 0 + ∑ y, (if P y then 0 else c x y) else 0) =
      ∑ x, (if P x then max (d x) 0 else 0) +
        ∑ x, (if P x then ∑ y, (if P y then 0 else c x y) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by by_cases hx : P x <;> simp [hx]
  rw [hcap, hsplit, Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  linarith

/-- Under Gale's condition the auxiliary network has a flow of value at least the total demand.
-/
theorem exists_big_flow (h : ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y) :
    ∃ F : Flow (galeNet c hc d), ∑ x, max (d x) 0 ≤ F.value := by
  obtain ⟨F, C, hFC⟩ := maxflow_eq_mincut (galeNet c hc d)
  exact ⟨F, hFC ▸ cut_ge c hc d h C⟩

end Aux

/-! ## The feasibility theorem -/

/-- **Gale's feasibility theorem** (Gale 1957). For nonnegative real capacities `c`, the demand
`d` is feasible if and only if `d(S') ≤ c(S, S')` for every set `S` of nodes. -/
theorem feasibility (c : N → N → ℝ) (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    (∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y := by
  constructor
  · rintro ⟨f, hf, hfc, hd⟩ S
    exact feasible_cond c d f hf hfc hd S
  · intro h
    obtain ⟨F, hF⟩ := exists_big_flow c hc d h
    obtain ⟨h1, h2, h3⟩ := extract c hc d F hF
    exact ⟨fun x y => F.f (some (some x)) (some (some y)), h1, h2, h3⟩

/-- Integer capacities of the auxiliary network. -/
def galeCapInt (c : N → N → ℤ) (d : N → ℤ) : Option (Option N) → Option (Option N) → ℤ
  | some (some x), some (some y) => c x y
  | none, some (some x) => max (-d x) 0
  | some (some x), some none => max (d x) 0
  | _, _ => 0

/-- **Gale's feasibility theorem, integral version** (Gale's remark). For nonnegative integer
capacities and integer demands, the condition `d(S') ≤ c(S, S')` for all `S` holds if and only
if there is an integer-valued flow satisfying the demand. -/
theorem feasibility_int (c : N → N → ℤ) (hc : ∀ x y, 0 ≤ c x y) (d : N → ℤ) :
    (∃ f : N → N → ℤ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ S : Finset N, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y := by
  constructor
  · rintro ⟨f, hf, hfc, hd⟩ S
    exact feasible_cond c d f hf hfc hd S
  · intro h
    set cR : N → N → ℝ := fun x y => (c x y : ℝ)
    set dR : N → ℝ := fun x => (d x : ℝ)
    have hcR : ∀ x y, 0 ≤ cR x y := fun x y => by simp [cR, hc x y]
    have hR : ∀ S : Finset N, ∑ x ∈ Sᶜ, dR x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, cR x y := by
      intro S; simp only [dR, cR]; exact_mod_cast h S
    obtain ⟨F₀, hF₀⟩ := exists_big_flow cR hcR dR hR
    have hcap : ∀ u v, (galeNet cR hcR dR).cap u v = galeCapInt c d u v := by
      rintro (_ | _ | x) (_ | _ | y) <;> simp [galeCapInt, cR, dR]
    obtain ⟨F, g, hg, hmax⟩ := Baranyai.exists_integral_maxflow (galeNet cR hcR dR)
      (galeCapInt c d) hcap
    obtain ⟨h1, h2, h3⟩ := extract cR hcR dR F (hF₀.trans (hmax F₀))
    refine ⟨fun x y => g (some (some x)) (some (some y)), fun x y => ?_, fun x y => ?_,
      fun x => ?_⟩
    · change g (some (some x)) (some (some y)) + g (some (some y)) (some (some x)) = 0
      have := h1 x y; rw [hg, hg] at this; exact_mod_cast this
    · change g (some (some x)) (some (some y)) ≤ c x y
      have := h2 x y; rw [hg] at this; simp only [cR] at this; exact_mod_cast this
    · change d x ≤ ∑ y, g (some (some y)) (some (some x))
      have := h3 x; simp only [hg, dR] at this; exact_mod_cast this

/-! ## The second formulation -/

omit [DecidableEq N] in
/-- **Second formulation of the feasibility theorem** (Gale 1957). The demand `d` is feasible
if and only if, for every set `Y` of nodes of positive demand, some flow satisfies the demand at
every node of nonpositive demand and the aggregate demand of `Y`. -/
theorem feasibility_second (c : N → N → ℝ) (hc : ∀ x y, 0 ≤ c x y) (d : N → ℝ) :
    (∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, d x ≤ ∑ y, f y x) ↔
      ∀ Y : Finset N, (∀ y ∈ Y, 0 < d y) →
        ∃ f : N → N → ℝ, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
          (∀ x, d x ≤ 0 → d x ≤ ∑ y, f y x) ∧ ∑ x ∈ Y, d x ≤ ∑ x ∈ Y, ∑ y, f y x := by
  constructor
  · rintro ⟨f, hf, hfc, hd⟩ Y _
    exact ⟨f, hf, hfc, fun x _ => hd x, Finset.sum_le_sum fun x _ => hd x⟩
  · intro h
    classical
    rw [feasibility c hc d]
    intro S
    obtain ⟨f, hf, hfc, hU, hY⟩ := h (Sᶜ.filter fun x => 0 < d x) (fun y hy => by
      simp only [Finset.mem_filter] at hy; exact hy.2)
    have hneg : ∑ x ∈ Sᶜ.filter (fun x => ¬ 0 < d x), d x ≤
        ∑ x ∈ Sᶜ.filter (fun x => ¬ 0 < d x), ∑ y, f y x :=
      Finset.sum_le_sum fun x hx => hU x (not_lt.1 (Finset.mem_filter.1 hx).2)
    have e1 := Finset.sum_filter_add_sum_filter_not Sᶜ (fun x => 0 < d x) d
    have e2 := Finset.sum_filter_add_sum_filter_not Sᶜ (fun x => 0 < d x) (fun x => ∑ y, f y x)
    have := inflow_le_cut c f hf hfc S
    linarith

end GaleFlows
