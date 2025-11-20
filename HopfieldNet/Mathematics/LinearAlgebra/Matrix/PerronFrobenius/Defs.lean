import HopfieldNet.Mathematics.aux
import HopfieldNet.Mathematics.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.Topology.Compactness.ExtremeValueUSC
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Perron-Frobenius Theory for Matrices

This file develops the essential Perron-Frobenius theory for non-negative matrices.
It provides the spectral analysis of non-negative irreducible matrices, which underlies
applications like Markov chain convergence and spectral graph theory.

## Main Definitions

* `Matrix.toQuiver`: The directed graph associated with a matrix `A`.
* `Matrix.Irreducible`: A matrix `A` is irreducible if its associated directed graph is
  strongly connected.
* `Matrix.IsPrimitive`: A matrix `A` is primitive if some power of it is strictly positive.

## Main Results

The file builds towards the Perron-Frobenius theorem by formalizing key characterizations:

* `Matrix.irreducible_iff_exists_pow_pos`: A combinatorial characterization of
  irreducibility.
* `Matrix.pow_entry_pos_iff_exists_path`: A fundamental link between matrix powers and
  path existence in the associated graph.
-/

namespace Matrix
open Finset Quiver
variable {n : Type*} [Fintype n]

lemma pow_nonneg [DecidableEq n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; simp [one_apply]; by_cases h : i = j <;> simp [h]
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

def toQuiver (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

abbrev IsStronglyConnected (G : Quiver n) : Prop :=   ∀ i j : n, Nonempty { p : Path i j // p.length > 0 }

def Irreducible (A : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ IsStronglyConnected (toQuiver A)

def IsPrimitive [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∃ k, 0 < k ∧ ∀ i j, 0 < (A ^ k) i j

/-- If `A` is irreducible and `n>1` then every row has a positive entry. -/
lemma irreducible_no_zero_row
    (A : Matrix n n ℝ) --(hA_nonneg : ∀ i j, 0 ≤ A i j)
    (h_irr : Irreducible A) (h_dim : 1 < Fintype.card n) (i : n) :
    ∃ j, 0 < A i j := by
  by_contra h_row ; push_neg at h_row   -- `h_row : ∀ j, A i j ≤ 0`
  letI G := toQuiver A
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j ↦ ⟨fun h ↦ (h_row j).not_gt h⟩
  obtain ⟨j, hij⟩ := Fintype.exists_ne_of_one_lt_card h_dim i
  obtain ⟨⟨p, _⟩⟩ := h_irr.2 i j
  have : False := by
    have aux : (∀ {v} (q : G.Path i v), v ≠ i → False) := by
      intro v q
      induction q with
      | nil =>
          intro hvi ; exact hvi rfl
      | cons r e ih =>
          cases r with
          | nil =>
              intro _
              exact (no_out _).false e
          | cons r' e' =>
              intro hvi ; simp_all only [isEmpty_Prop, ne_eq, imp_false, not_not, G]
    exact aux p hij
  exact this.elim

section PerronFrobeniusTheorems

variable {A : Matrix n n ℝ}

open Classical in
lemma sum_pos_of_mem  {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
    Eq.symm (add_sum_erase s f ha_mem)
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (λ x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [h_sum_split]
  exact add_pos_of_pos_of_nonneg ha_pos h_erase_nonneg

theorem pow_entry_pos_iff_exists_path [DecidableEq n] (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := toQuiver A; 0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, nonempty_subtype]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq; exact ⟨letI := toQuiver A; Quiver.Path.nil, rfl⟩
      · exfalso; linarith [h_pos]
    · rintro ⟨p, hp⟩
      have h_eq : i = j := letI := toQuiver A; Quiver.Path.eq_of_length_zero p hp
      simp [h_eq]
  | succ m ih =>
    rw [pow_succ, mul_apply, nonempty_subtype]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ univ, 0 < (A ^ m) i l * A l j :=
        exists_mem_of_sum_pos h_pos fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j)
      rcases (mul_pos_iff_of_nonneg (pow_nonneg hA m i l) (hA l j)).mp hl_pos with ⟨h_Am, h_A⟩
      obtain ⟨⟨p, hp_len⟩⟩ := (ih i l).mp h_Am
      exact ⟨letI := toQuiver A; p.cons h_A, by
        subst hp_len
        simp_all only [mem_univ, nonempty_subtype, mul_pos_iff_of_pos_left, exists_apply_eq_apply,
          Path.cons_eq_comp_toPath, Path.length_comp, Nat.add_left_cancel_iff]
        rfl⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos
        exact sum_pos_of_mem
          (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j))
          b
          (Finset.mem_univ b)
          h_prod

theorem irreducible_iff_exists_pow_pos [DecidableEq n]  (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < k ∧ 0 < (A ^ k) i j := by
  constructor
  · intro h_irr i j
    rcases h_irr.2 i j with ⟨⟨p, hp_len⟩⟩
    letI := toQuiver A;
    use p.length, hp_len, by
      rw [pow_entry_pos_iff_exists_path hA]
      exact ⟨p, rfl⟩
  · intro h_exists
    constructor
    · exact hA
    · intro i j
      obtain ⟨k, hk_pos, hk_entry⟩ := h_exists i j
      letI := toQuiver A
      obtain ⟨⟨p, hp_len⟩⟩ := (pow_entry_pos_iff_exists_path hA k i j).mp hk_entry
      subst hp_len
      exact ⟨p, hk_pos⟩

theorem IsPrimitive.to_Irreducible [DecidableEq n] (h_prim : IsPrimitive A) (hA : ∀ i j, 0 ≤ A i j) :
    Irreducible A := by
  rw [irreducible_iff_exists_pow_pos hA]
  intro i j
  obtain ⟨k, _hk_gt_zero, hk_pos⟩ := h_prim
  simp_all only [implies_true]
  obtain ⟨left, right⟩ := hk_pos
  apply Exists.intro
  · apply And.intro
    · exact left
    · simp_all only

/-- A matrix is irreducible iff its transpose is. -/
theorem Irreducible.transpose [DecidableEq n] (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA : Irreducible A) : Irreducible Aᵀ := by
  have h_exists := (irreducible_iff_exists_pow_pos hA_nonneg).1 hA
  have h_iff := irreducible_iff_exists_pow_pos (λ i j => hA_nonneg j i)
  apply h_iff.mpr
  intro i j
  obtain ⟨k, hk_pos, hk⟩ := h_exists j i
  use k, hk_pos
  erw [← transpose_pow]
  exact hk


end PerronFrobeniusTheorems
end Matrix
