/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GaleHoffmanLib.Feasibility

/-!
# Hoffman's circulation theorem

A directed multigraph on a finite vertex set `V` is given by a finite arc type `A` with tail and
head maps `src tgt : A → V` (parallel arcs and loops are allowed). For lower and upper bounds
`d ≤ c` on the arcs, there is a circulation `f` with `d ≤ f ≤ c` if and only if
`d(δ^in(U)) ≤ c(δ^out(U))` for every set `U` of vertices (Hoffman 1960; Schrijver, *A Course in
Combinatorial Optimization*, Theorems 4.6 and 4.7). If `d` and `c` are integral, the
circulation can be taken integral.

The proof derives the theorem from Gale's feasibility theorem (`GaleFlows.feasibility`,
`GaleFlows.feasibility_int`): write `f = d + g` with `0 ≤ g ≤ c - d`; the net flow of `g`
between two vertices is a Gale flow for the demand `d(δ^out(v)) - d(δ^in(v))`, and conversely a
Gale flow is split over the parallel arcs.
-/

@[expose] public section

namespace GaleFlows

open Finset

section Sums

variable {M : Type*} [AddCommMonoid M] {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]

lemma ite_zero_of_not {p : Prop} [Decidable p] {a : M} (h : ¬p) : (if p then a else 0) = 0 := by
  simp [h]

lemma sum_ite_pair (S : Finset V) (p q : V) (k : M) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, (if p = x ∧ q = y then k else 0) = if p ∈ S ∧ q ∉ S then k else 0 := by
  by_cases hp : p ∈ S
  · rw [Finset.sum_eq_single_of_mem p hp (fun x _ hx =>
      Finset.sum_eq_zero fun y _ => ite_zero_of_not fun h => hx h.1.symm)]
    by_cases hq : q ∈ S
    · rw [Finset.sum_eq_zero fun y hy =>
        ite_zero_of_not fun h => (Finset.mem_compl.1 hy) (h.2 ▸ hq)]
      simp [hq]
    · rw [Finset.sum_eq_single_of_mem q (Finset.mem_compl.2 hq) (fun y _ hy =>
        ite_zero_of_not fun h => hy h.2.symm)]
      simp [hp, hq]
  · rw [Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ =>
      ite_zero_of_not fun (h : p = x ∧ q = y) => hp (h.1 ▸ hx)]
    simp [hp]

omit [Fintype V] in
lemma sum_fiber_ite (T : Finset V) (p : A → V) (g : A → M) :
    ∑ v ∈ T, ∑ a, (if p a = v then g a else 0) = ∑ a, if p a ∈ T then g a else 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq T (p a) (fun _ => g a)

end Sums

section Generic

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Split a nonnegative amount `P ≤ ∑ h` into parts `0 ≤ g ≤ h`. -/
theorem exists_split {ι : Type*} (s : Finset ι) (h : ι → R)
    (hh : ∀ i, 0 ≤ h i) (P : R) (hP0 : 0 ≤ P) (hP : P ≤ ∑ i ∈ s, h i) :
    ∃ g : ι → R, (∀ i, 0 ≤ g i ∧ g i ≤ h i) ∧ ∑ i ∈ s, g i = P := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty =>
    refine ⟨0, fun i => ⟨le_refl 0, hh i⟩, ?_⟩
    simp only [Finset.sum_empty] at hP ⊢
    exact (le_antisymm hP hP0).symm
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at hP
    obtain ⟨g, hg, hgs⟩ := ih (P - min (h j) P) (by linarith [min_le_right (h j) P]) (by
      rcases le_total (h j) P with hjP | hjP
      · rw [min_eq_left hjP]; linarith
      · rw [min_eq_right hjP, sub_self]; exact Finset.sum_nonneg fun i _ => hh i)
    refine ⟨Function.update g j (min (h j) P), fun i => ?_, ?_⟩
    · by_cases hi : i = j
      · subst hi
        simp only [Function.update_self]
        exact ⟨le_min (hh _) hP0, min_le_left _ _⟩
      · simp only [Function.update_of_ne hi]; exact hg i
    · rw [Finset.sum_insert hj, Function.update_self,
        Finset.sum_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi hj) _ _),
        hgs]
      ring

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]

/-- Gale's sufficiency direction over `R` on the vertex set `V`. -/
def GaleSuff (R V : Type*) [CommRing R] [LinearOrder R] [Fintype V] [DecidableEq V] : Prop :=
  ∀ c : V → V → R, (∀ x y, 0 ≤ c x y) → ∀ d : V → R,
    (∀ S : Finset V, ∑ x ∈ Sᶜ, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y) →
    ∃ f : V → V → R, (∀ x y, f x y + f y x = 0) ∧ (∀ x y, f x y ≤ c x y) ∧
      ∀ x, d x ≤ ∑ y, f y x

omit [Fintype V] in
/-- Necessity of Hoffman's condition. -/
theorem hoffman_nec (src tgt : A → V) (d c f : A → R) (hf : ∀ a, d a ≤ f a ∧ f a ≤ c a)
    (hcons : ∀ v, ∑ a, (if tgt a = v then f a else 0) = ∑ a, (if src a = v then f a else 0))
    (U : Finset V) :
    ∑ a, (if tgt a ∈ U ∧ src a ∉ U then d a else 0) ≤
      ∑ a, (if src a ∈ U ∧ tgt a ∉ U then c a else 0) := by
  have hU : ∑ a, (if tgt a ∈ U then f a else 0) = ∑ a, (if src a ∈ U then f a else 0) := by
    rw [← sum_fiber_ite U tgt f, ← sum_fiber_ite U src f]
    exact Finset.sum_congr rfl fun v _ => hcons v
  have h1 : ∑ a, (if tgt a ∈ U then f a else 0) =
      ∑ a, (if tgt a ∈ U ∧ src a ∉ U then f a else 0) +
        ∑ a, (if tgt a ∈ U ∧ src a ∈ U then f a else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      by_cases ht : tgt a ∈ U <;> by_cases hs : src a ∈ U <;> simp [ht, hs]
  have h2 : ∑ a, (if src a ∈ U then f a else 0) =
      ∑ a, (if src a ∈ U ∧ tgt a ∉ U then f a else 0) +
        ∑ a, (if tgt a ∈ U ∧ src a ∈ U then f a else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      by_cases ht : tgt a ∈ U <;> by_cases hs : src a ∈ U <;> simp [ht, hs]
  have h3 : ∑ a, (if tgt a ∈ U ∧ src a ∉ U then d a else 0) ≤
      ∑ a, (if tgt a ∈ U ∧ src a ∉ U then f a else 0) :=
    Finset.sum_le_sum fun a _ => by split_ifs <;> simp [(hf a).1]
  have h4 : ∑ a, (if src a ∈ U ∧ tgt a ∉ U then f a else 0) ≤
      ∑ a, (if src a ∈ U ∧ tgt a ∉ U then c a else 0) :=
    Finset.sum_le_sum fun a _ => by split_ifs <;> simp [(hf a).2]
  linarith

/-- Sufficiency of Hoffman's condition, from Gale's feasibility theorem over `R`. -/
theorem hoffman_suff (hG : GaleSuff R V) (src tgt : A → V) (d c : A → R)
    (hdc : ∀ a, d a ≤ c a)
    (h : ∀ U : Finset V, ∑ a, (if tgt a ∈ U ∧ src a ∉ U then d a else 0) ≤
      ∑ a, (if src a ∈ U ∧ tgt a ∉ U then c a else 0)) :
    ∃ f : A → R, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
      ∀ v, ∑ a, (if tgt a = v then f a else 0) = ∑ a, (if src a = v then f a else 0) := by
  classical
  -- Gale data
  set C : V → V → R := fun x y => ∑ a, if src a = x ∧ tgt a = y then c a - d a else 0 with hC
  have hC0 : ∀ x y, 0 ≤ C x y := fun x y =>
    Finset.sum_nonneg fun a _ => by split_ifs <;> simp [hdc a]
  set e : V → R := fun v =>
    ∑ a, (if src a = v then d a else 0) - ∑ a, (if tgt a = v then d a else 0) with he
  have hcond : ∀ S : Finset V, ∑ x ∈ Sᶜ, e x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, C x y := by
    intro S
    have hL : ∑ x ∈ Sᶜ, e x = ∑ a, (if src a ∈ Sᶜ then d a else 0) -
        ∑ a, (if tgt a ∈ Sᶜ then d a else 0) := by
      rw [he, Finset.sum_sub_distrib, sum_fiber_ite, sum_fiber_ite]
    have hR : ∑ x ∈ S, ∑ y ∈ Sᶜ, C x y =
        ∑ a, if src a ∈ S ∧ tgt a ∉ S then c a - d a else 0 := by
      simp only [hC]
      rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => sum_ite_pair S (src a) (tgt a) (c a - d a)
    have hpt : ∀ a, (if src a ∈ Sᶜ then d a else 0) - (if tgt a ∈ Sᶜ then d a else 0) =
        (if tgt a ∈ S ∧ src a ∉ S then d a else 0) -
          (if src a ∈ S ∧ tgt a ∉ S then d a else 0) := by
      intro a
      by_cases hs : src a ∈ S <;> by_cases ht : tgt a ∈ S <;> simp [hs, ht]
    have hpt2 : ∀ a, (if src a ∈ S ∧ tgt a ∉ S then c a - d a else 0) =
        (if src a ∈ S ∧ tgt a ∉ S then c a else 0) -
          (if src a ∈ S ∧ tgt a ∉ S then d a else 0) := by
      intro a; split_ifs <;> simp
    rw [hL, hR, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun a _ => hpt a,
      Finset.sum_congr rfl fun a _ => hpt2 a, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith [h S]
  obtain ⟨φ, hφ, hφC, hφe⟩ := hG C hC0 e hcond
  -- the demand is met with equality
  have hsum_e : ∑ x, e x = 0 := by
    have h1 := sum_fiber_ite (Finset.univ : Finset V) src d
    have h2 := sum_fiber_ite (Finset.univ : Finset V) tgt d
    simp only [Finset.mem_univ, ite_true] at h1 h2
    rw [he, Finset.sum_sub_distrib, h1, h2, sub_self]
  have hsum_φ : ∑ x, ∑ y, φ y x = 0 := sum_sum_antisymm_eq_zero φ hφ Finset.univ
  have hφe' : ∀ x, ∑ y, φ y x = e x := by
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun x _ => hφe x)).1
      (by rw [hsum_e, hsum_φ])
    exact fun x => (this x (Finset.mem_univ x)).symm
  -- split the positive part of `φ x y` over the arcs from `x` to `y`
  have hsplit : ∀ x y, ∃ g : A → R, (∀ a, 0 ≤ g a ∧ g a ≤ c a - d a) ∧
      ∑ a ∈ Finset.univ.filter (fun a => src a = x ∧ tgt a = y), g a = max (φ x y) 0 := by
    intro x y
    refine exists_split _ (fun a => c a - d a) (fun a => by simp [hdc a]) _
      (le_max_right _ _) ?_
    rw [Finset.sum_filter]
    exact max_le (hφC x y) (hC0 x y)
  choose g hg hgs using hsplit
  have hgs' : ∀ x y, ∑ a, (if src a = x ∧ tgt a = y then g x y a else 0) = max (φ x y) 0 :=
    fun x y => by rw [← Finset.sum_filter]; exact hgs x y
  refine ⟨fun a => d a + g (src a) (tgt a) a, fun a => ⟨?_, ?_⟩, fun v => ?_⟩
  · linarith [(hg (src a) (tgt a) a).1]
  · linarith [(hg (src a) (tgt a) a).2]
  -- conservation
  have hin : ∑ a, (if tgt a = v then g (src a) (tgt a) a else 0) = ∑ x, max (φ x v) 0 := by
    rw [← Finset.sum_congr rfl fun x _ => hgs' x v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ht : tgt a = v
    · subst ht; simp
    · simp [ht]
  have hout : ∑ a, (if src a = v then g (src a) (tgt a) a else 0) = ∑ y, max (φ v y) 0 := by
    rw [← Finset.sum_congr rfl fun y _ => hgs' v y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hs : src a = v
    · subst hs
      rw [Finset.sum_eq_single (tgt a) (fun y _ hy => ite_zero_of_not fun h => hy h.2.symm)
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · simp [hs]
  have hdiff : ∑ x, max (φ x v) 0 - ∑ y, max (φ v y) 0 = e v := by
    rw [← hφe' v, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : φ v x = - φ x v := by linarith [hφ x v]
    rw [this, max_zero_sub_max_neg_zero_eq_self]
  have hL : ∑ a, (if tgt a = v then d a + g (src a) (tgt a) a else 0) =
      ∑ a, (if tgt a = v then d a else 0) + ∑ a, (if tgt a = v then g (src a) (tgt a) a else 0)
      := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  have hR : ∑ a, (if src a = v then d a + g (src a) (tgt a) a else 0) =
      ∑ a, (if src a = v then d a else 0) + ∑ a, (if src a = v then g (src a) (tgt a) a else 0)
      := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  change ∑ a, (if tgt a = v then d a + g (src a) (tgt a) a else 0) =
    ∑ a, (if src a = v then d a + g (src a) (tgt a) a else 0)
  rw [hL, hR, hin, hout]
  have : e v = ∑ a, (if src a = v then d a else 0) - ∑ a, (if tgt a = v then d a else 0) := rfl
  linarith

/-- Hoffman's theorem over `R`, given Gale's sufficiency over `R`, in filter notation. -/
theorem hoffman_of_gale (hG : GaleSuff R V) (src tgt : A → V) (d c : A → R)
    (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → R, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a := by
  simp only [Finset.sum_filter]
  constructor
  · rintro ⟨f, hf, hcons⟩ U
    exact hoffman_nec src tgt d c f hf hcons U
  · exact hoffman_suff hG src tgt d c hdc

end Generic

variable {V A : Type*} [DecidableEq V] [Fintype A]

theorem galeSuff_real [Fintype V] : GaleSuff ℝ V := fun c hc d h => (feasibility c hc d).2 h

theorem galeSuff_int [Fintype V] : GaleSuff ℤ V := fun c hc d h => (feasibility_int c hc d).2 h

/-- **Hoffman's circulation theorem** (Hoffman 1960; Schrijver, Theorem 4.6). -/
theorem hoffman [Finite V] (src tgt : A → V) (d c : A → ℝ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℝ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a := by
  have := Fintype.ofFinite V
  exact hoffman_of_gale galeSuff_real src tgt d c hdc

/-- **Hoffman's circulation theorem, integral version** (Schrijver, Theorem 4.7). -/
theorem hoffman_int [Finite V] (src tgt : A → V) (d c : A → ℤ) (hdc : ∀ a, d a ≤ c a) :
    (∃ f : A → ℤ, (∀ a, d a ≤ f a ∧ f a ≤ c a) ∧
        ∀ v, ∑ a with tgt a = v, f a = ∑ a with src a = v, f a) ↔
      ∀ U : Finset V, ∑ a with tgt a ∈ U ∧ src a ∉ U, d a ≤
        ∑ a with src a ∈ U ∧ tgt a ∉ U, c a := by
  have := Fintype.ofFinite V
  exact hoffman_of_gale galeSuff_int src tgt d c hdc

end GaleFlows
