/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GaleHoffmanLib.Feasibility
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The Gale–Ryser theorem

Gale's Problem I (Gale 1957, §3): given `a : Fin m → ℕ` and `b : Fin n → ℕ`, find a `0`-`1`
matrix `α` with row sums at most `a i` and column sums equal to `b j`. With the columns indexed
so that `b` is nonincreasing, this is possible if and only if
`∑_{j < k} b j ≤ ∑_{j < k} a*_j` for every `k ≤ n`, where `a*_j = #{i | j < a i}` is the dual
sequence (`gale_ryser`). When `∑ a = ∑ b` the row sums are then exactly `a` (`gale_ryser_exact`,
the Gale–Ryser theorem).

The proof applies the integral feasibility theorem (`feasibility_int`) to the bipartite network
with unit capacities from rows to columns, as in Gale's paper, through the unsorted criterion
`∑_{j ∈ Y} b j ≤ ∑_i min (a i) |Y|` (`gale_ryser_unsorted`).
-/

@[expose] public section

namespace GaleFlows

open Finset

variable {m n : ℕ}

/-- Unit capacities from rows to columns. -/
def grCap : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℤ
  | .inl _, .inr _ => 1
  | _, _ => 0

/-- Rows supply `a i`, columns demand `b j`. -/
def grDem (a : Fin m → ℕ) (b : Fin n → ℕ) : Fin m ⊕ Fin n → ℤ
  | .inl i => -(a i : ℤ)
  | .inr j => (b j : ℤ)

lemma sum_compl_ite {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    ∑ x ∈ Sᶜ, g x = ∑ x, if x ∈ S then 0 else g x := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1
  ext x
  simp

lemma sum_ite_mem' {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    ∑ x ∈ S, g x = ∑ x, if x ∈ S then g x else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Unsorted criterion** for Gale's Problem I. -/
theorem gale_ryser_unsorted (a : Fin m → ℕ) (b : Fin n → ℕ) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ Y : Finset (Fin n), ∑ j ∈ Y, b j ≤ ∑ i, min (a i) Y.card := by
  constructor
  · rintro ⟨α, h1, hrow, hcol⟩ Y
    calc ∑ j ∈ Y, b j = ∑ j ∈ Y, ∑ i, α i j := Finset.sum_congr rfl fun j _ => (hcol j).symm
      _ = ∑ i, ∑ j ∈ Y, α i j := Finset.sum_comm
      _ ≤ ∑ i, min (a i) Y.card := Finset.sum_le_sum fun i _ => le_min
          ((Finset.sum_le_sum_of_subset (Finset.subset_univ Y)).trans (hrow i))
          ((Finset.sum_le_card_nsmul Y _ 1 fun j _ => h1 i j).trans (by simp))
  · intro hY
    -- Gale's condition for the bipartite network
    have hcond : ∀ S : Finset (Fin m ⊕ Fin n),
        ∑ x ∈ Sᶜ, grDem a b x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, grCap x y := by
      intro S
      set Y : Finset (Fin n) := Finset.univ.filter fun j => Sum.inr j ∉ S with hYdef
      have hL : ∑ x ∈ Sᶜ, grDem a b x =
          ∑ i, (if Sum.inl i ∈ S then 0 else -(a i : ℤ)) + ∑ j ∈ Y, (b j : ℤ) := by
        rw [sum_compl_ite, Fintype.sum_sum_type, hYdef, Finset.sum_filter]
        simp only [grDem]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by by_cases hj : Sum.inr j ∈ S <;> simp [hj]
      have hR : ∑ x ∈ S, ∑ y ∈ Sᶜ, grCap x y =
          ∑ i, (if Sum.inl i ∈ S then (Y.card : ℤ) else 0) := by
        rw [sum_ite_mem', Fintype.sum_sum_type]
        simp only [sum_compl_ite, Fintype.sum_sum_type, grCap]
        simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : Sum.inl i ∈ S
        · simp only [hi, ite_true, hYdef, Finset.card_filter]
          push_cast
          exact Finset.sum_congr rfl fun j _ => by by_cases hj : Sum.inr j ∈ S <;> simp [hj]
        · simp [hi]
      have hmin := hY Y
      have hpt : ∀ i, (min (a i) Y.card : ℤ) ≤
          (if Sum.inl i ∈ S then (Y.card : ℤ) else 0) + (if Sum.inl i ∈ S then 0 else (a i : ℤ))
          := by
        intro i; by_cases hi : Sum.inl i ∈ S <;> simp [hi]
      have hZ : ((∑ j ∈ Y, b j : ℕ) : ℤ) ≤ ((∑ i, min (a i) Y.card : ℕ) : ℤ) := by
        exact_mod_cast hmin
      push_cast at hZ
      have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpt i
      rw [Finset.sum_add_distrib] at hsum
      have hneg : ∑ i, (if Sum.inl i ∈ S then 0 else -(a i : ℤ)) =
          - ∑ i, (if Sum.inl i ∈ S then 0 else (a i : ℤ)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      rw [hL, hR, hneg]
      linarith
    obtain ⟨f, hf, hfc, hd⟩ := (feasibility_int grCap
      (by rintro (_ | _) (_ | _) <;> simp [grCap]) (grDem a b)).2 hcond
    -- the flow on row–column pairs is 0 or 1
    have hlo : ∀ i j, 0 ≤ f (Sum.inl i) (Sum.inr j) := by
      intro i j; have h1 := hf (Sum.inl i) (Sum.inr j); have h2 := hfc (Sum.inr j) (Sum.inl i)
      simp only [grCap] at h2; linarith
    have hhi : ∀ i j, f (Sum.inl i) (Sum.inr j) ≤ 1 := fun i j => hfc (Sum.inl i) (Sum.inr j)
    have hll : ∀ i i', f (Sum.inl i) (Sum.inl i') = 0 := by
      intro i i'; have h1 := hf (Sum.inl i) (Sum.inl i'); have h2 := hfc (Sum.inl i) (Sum.inl i')
      have h3 := hfc (Sum.inl i') (Sum.inl i); simp only [grCap] at h2 h3; linarith
    have hrr : ∀ j j', f (Sum.inr j) (Sum.inr j') = 0 := by
      intro j j'; have h1 := hf (Sum.inr j) (Sum.inr j'); have h2 := hfc (Sum.inr j) (Sum.inr j')
      have h3 := hfc (Sum.inr j') (Sum.inr j); simp only [grCap] at h2 h3; linarith
    set β : Fin m → Fin n → ℕ := fun i j => (f (Sum.inl i) (Sum.inr j)).toNat with hβ
    have hβz : ∀ i j, (β i j : ℤ) = f (Sum.inl i) (Sum.inr j) := fun i j =>
      Int.toNat_of_nonneg (hlo i j)
    have hβ1 : ∀ i j, β i j ≤ 1 := fun i j => by have := hβz i j; have := hhi i j; omega
    have hrow : ∀ i, ∑ j, β i j ≤ a i := by
      intro i
      have h := hd (Sum.inl i)
      rw [Fintype.sum_sum_type] at h
      simp only [grDem] at h
      have e1 : ∑ i', f (Sum.inl i') (Sum.inl i) = 0 := Finset.sum_eq_zero fun i' _ => hll i' i
      have e2 : ∑ j, f (Sum.inr j) (Sum.inl i) = - ∑ j, (β i j : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hβz]; linarith [hf (Sum.inl i) (Sum.inr j)]
      rw [e1, e2] at h
      have : ((∑ j, β i j : ℕ) : ℤ) ≤ (a i : ℤ) := by push_cast; linarith
      exact_mod_cast this
    have hcol : ∀ j, b j ≤ ∑ i, β i j := by
      intro j
      have h := hd (Sum.inr j)
      rw [Fintype.sum_sum_type] at h
      simp only [grDem] at h
      have e1 : ∑ j', f (Sum.inr j') (Sum.inr j) = 0 := Finset.sum_eq_zero fun j' _ => hrr j' j
      rw [e1, add_zero] at h
      have : (b j : ℤ) ≤ ((∑ i, β i j : ℕ) : ℤ) := by
        push_cast; rw [Finset.sum_congr rfl fun i _ => hβz i j]; exact h
      exact_mod_cast this
    -- keep exactly `b j` ones in each column
    have hT : ∀ j, ∃ U ⊆ Finset.univ.filter (fun i => β i j = 1), U.card = b j := by
      intro j
      apply Finset.exists_subset_card_eq
      rw [Finset.card_filter]
      calc b j ≤ ∑ i, β i j := hcol j
        _ = ∑ i, if β i j = 1 then 1 else 0 := Finset.sum_congr rfl fun i _ => by
            have := hβ1 i j
            by_cases h : β i j = 1
            · simp [h]
            · have h0 : β i j = 0 := by omega
              simp [h0]
    choose U hU hUc using hT
    refine ⟨fun i j => if i ∈ U j then 1 else 0, fun i j => by dsimp only; split_ifs <;> simp,
      fun i => ?_, fun j => ?_⟩
    · refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hrow i)
      dsimp only
      split_ifs with h
      · have := (Finset.mem_filter.1 (hU j h)).2; omega
      · exact Nat.zero_le _
    · simp [Finset.sum_ite_mem, hUc j]

/-- `∑_i min (a i) k = ∑_{j < k} #{i | j < a i}`. -/
lemma sum_min_eq_sum_dual (a : Fin m → ℕ) (k : ℕ) :
    ∑ i, min (a i) k = ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  have : (Finset.range k).filter (fun j => j < a i) = Finset.range (min (a i) k) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

lemma card_filter_val_lt (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter fun j : Fin n => j.val < k).card = k := by
  have : (Finset.univ.filter fun j : Fin n => j.val < k).map Fin.valEmbedding =
      Finset.range k := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, this, Finset.card_range]

/-- For nonincreasing `b`, the first `|Y|` columns carry the largest sum. -/
lemma sum_le_sum_initial (b : Fin n → ℕ) (hb : Antitone b) (Y : Finset (Fin n)) :
    ∑ j ∈ Y, b j ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < Y.card), b j := by
  set k := Y.card with hk
  set T := Finset.univ.filter fun j : Fin n => j.val < k with hT
  have hkn : k ≤ n := by
    have := Finset.card_le_univ Y; simpa using this
  have hTc : T.card = k := card_filter_val_lt k hkn
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [hk, Finset.card_eq_zero] at h0; simp [h0]
  set B := b ⟨k - 1, by omega⟩ with hB
  have h1 := Finset.sum_inter_add_sum_sdiff Y T b
  have h2 := Finset.sum_inter_add_sum_sdiff T Y b
  rw [Finset.inter_comm] at h2
  have hc1 := Finset.card_sdiff_add_card_inter Y T
  have hc2 := Finset.card_sdiff_add_card_inter T Y
  rw [Finset.inter_comm] at hc2
  have hcard : (Y \ T).card = (T \ Y).card := by omega
  have hYT : ∑ j ∈ Y \ T, b j ≤ (Y \ T).card • B := by
    refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
    have : ¬ j.val < k := by
      have := (Finset.mem_sdiff.1 hj).2; simpa [hT] using this
    exact hb (show (⟨k - 1, by omega⟩ : Fin n) ≤ j from by
      rw [Fin.le_def]; simp only; omega)
  have hTY : (T \ Y).card • B ≤ ∑ j ∈ T \ Y, b j := by
    refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
    have : j.val < k := by
      have := (Finset.mem_sdiff.1 hj).1; simpa [hT] using this
    exact hb (show j ≤ (⟨k - 1, by omega⟩ : Fin n) from by
      rw [Fin.le_def]; simp only; omega)
  rw [hcard] at hYT
  omega

/-- **Gale's criterion for Problem I** (Gale 1957, §3). With `b` nonincreasing, there is a
`0`-`1` matrix with row sums at most `a i` and column sums `b j` if and only if
`∑_{j < k} b j ≤ ∑_{j < k} a*_j` for all `k ≤ n`, where `a*_j = #{i | j < a i}`. -/
theorem gale_ryser (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j ≤ a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card := by
  rw [gale_ryser_unsorted]
  constructor
  · intro h k hk
    have := h (Finset.univ.filter fun j : Fin n => j.val < k)
    rwa [card_filter_val_lt k hk, sum_min_eq_sum_dual] at this
  · intro h Y
    have hkn : Y.card ≤ n := by have := Finset.card_le_univ Y; simpa using this
    calc ∑ j ∈ Y, b j ≤ _ := sum_le_sum_initial b hb Y
      _ ≤ _ := h Y.card hkn
      _ = _ := (sum_min_eq_sum_dual a Y.card).symm

/-- **The Gale–Ryser theorem.** If `∑ a = ∑ b` and `b` is nonincreasing, there is a `0`-`1`
matrix with row sums `a` and column sums `b` if and only if `∑_{j < k} b j ≤ ∑_{j < k} a*_j`
for all `k ≤ n`. -/
theorem gale_ryser_exact (a : Fin m → ℕ) (b : Fin n → ℕ) (hb : Antitone b)
    (hab : ∑ i, a i = ∑ j, b j) :
    (∃ α : Fin m → Fin n → ℕ, (∀ i j, α i j ≤ 1) ∧ (∀ i, ∑ j, α i j = a i) ∧
        ∀ j, ∑ i, α i j = b j) ↔
      ∀ k ≤ n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), b j ≤
        ∑ j ∈ Finset.range k, (Finset.univ.filter fun i => j < a i).card := by
  rw [← gale_ryser a b hb]
  constructor
  · rintro ⟨α, h1, hrow, hcol⟩
    exact ⟨α, h1, fun i => (hrow i).le, hcol⟩
  · rintro ⟨α, h1, hrow, hcol⟩
    refine ⟨α, h1, ?_, hcol⟩
    have htot : ∑ i, ∑ j, α i j = ∑ i, a i := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hcol j, hab]
    exact fun i => (Finset.sum_eq_sum_iff_of_le fun i _ => hrow i).1 htot i (Finset.mem_univ i)

end GaleFlows
