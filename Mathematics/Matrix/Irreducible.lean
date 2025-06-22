import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic

open BigOperators Finset

/-!
# Perron-Frobenius Theory for Matrices

This file develops the essential Perron-Frobenius theory for non-negative matrices,
as presented in Berman & Plemmons, "Nonnegative Matrices in the Mathematical Sciences".
It provides the spectral analysis of non-negative irreducible matrices, which underlies
applications like Markov chain convergence and spectral graph theory.

## Main Definitions

* `Matrix.toQuiver`: The directed graph associated with a matrix `A`.
* `Matrix.Irreducible`: A matrix `A` is irreducible if its associated directed graph is
  strongly connected.
* `Matrix.IsPrimitive`: A matrix `A` is primitive if it is irreducible and some power of it
  is strictly positive.
* `Matrix.HasPerronFrobeniusProperty`: A helper class bundling the common assumptions
  for the Perron-Frobenius theorem.

## Main Results

The file builds towards the Perron-Frobenius theorem by formalizing key characterizations:

* `Matrix.irreducible_iff_exists_pow_pos`: A combinatorial characterization of
  irreducibility, matching Theorem 2.1 in the text.

The main Perron-Frobenius theorem will be stated in several parts in subsequent files:
  1. For an irreducible non-negative matrix `A`, its spectral radius `ρ(A)` is a positive,
     simple eigenvalue.
  2. There exists a unique (up to scaling) strictly positive eigenvector corresponding to `ρ(A)`.
  3. If `A` has `h` eigenvalues with modulus `ρ(A)`, these are the `h`-th roots of unity
     scaled by `ρ(A)`.
-/

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*} [MulOneClass R]

/-- The weight of a path, defined as the product of the weights of its arrows.
    This version of weight uses a weight function on pairs of vertices. -/
def weight_from_vertices (w : V → V → R) : ∀ {i j : V}, Path i j → R
  | _, _, .nil => 1
  | _, j, @Path.cons _ _ _ k _ p (_e : k ⟶ j) => weight_from_vertices w p * w k j

/-- The weight of a path is positive if the weight of each arrow is positive. -/
lemma weight_from_vertices_pos {V : Type*} [Quiver V] {w : V → V → ℝ}
    (hw : ∀ {i j : V} (_ : i ⟶ j), 0 < w i j)
    {i j : V} (p : Path i j) : 0 < p.weight_from_vertices w := by
  induction p with
  | nil =>
    simp [weight_from_vertices, zero_lt_one]
  | cons p e ih =>
    rw [weight_from_vertices]
    exact mul_pos ih (hw e)

/-- The weight of a path is non-negative if the weight of each arrow is non-negative. -/
lemma weight_from_vertices_nonneg {V : Type*} [Quiver V] {w : V → V → ℝ}
    (hw : ∀ i j, 0 ≤ w i j) {i j : V} (p : Quiver.Path i j) : 0 ≤ p.weight_from_vertices w := by
  induction p with
  | nil => simp [Quiver.Path.weight_from_vertices];
  | cons _ _ ih => rw [Quiver.Path.weight_from_vertices]; exact mul_nonneg ih (hw _ _)

end Quiver.Path


namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix power `A^k` remains non-negative if the base matrix `A` is non-negative.
    This is a fundamental prerequisite for the entire theory. -/
lemma pow_nonneg {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    intro i j
    rw [pow_succ, mul_apply]
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (ih i l) (hA l j)

variable [Nonempty n]

/-!
## Irreducibility
-/

/-- The directed graph associated with a matrix `A`, where an edge `i → j` exists if `A i j > 0`.
    For non-negative matrices, this is equivalent to `A i j ≠ 0`. -/
def toQuiver (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => 0 < A i j⟩

/-- The directed graph associated with a matrix `A`, where an edge `i → j` exists if `A i j ≠ 0`.
    This definition is a direct match of Berman & Plemmons, Chapter 2, Definition 2.4 (p. 29). -/
def toQuiver' (A : Matrix n n ℝ) : Quiver n :=
  ⟨fun i j => A i j ≠ 0⟩

/-- A quiver is strongly connected if there is a path from any vertex to any other vertex.
    This corresponds to the definition of a strongly connected graph in Berman & Plemmons,
    Chapter 2, Definition 2.6 (p. 30). 
    Note: In practice, strong connectivity implies paths of bounded length (≤ |V|), but
    we use the simpler definition here for compatibility. -/
def IsStronglyConnected (G : Quiver n) : Prop := 
  ∀ i j : n, Nonempty (G.Path i j)

/-- Strengthened version of strong connectivity with bounded path lengths.
    This is equivalent to the standard definition but makes the bound explicit. -/
def IsStronglyConnectedBounded (G : Quiver n) : Prop := 
  ∀ i j : n, ∃ p : G.Path i j, p.length ≤ Fintype.card n

/-- Strong connectivity implies bounded strong connectivity. -/
theorem stronglyConnected_implies_bounded {G : Quiver n} :
    IsStronglyConnected G → IsStronglyConnectedBounded G := by
  sorry -- This requires graph theory about cycle elimination

/-- A matrix `A` is irreducible if its associated directed graph is strongly connected.
    This is the characterization given in Berman & Plemmons, Chapter 2, Theorem 2.7 (p. 30).
    The book's primary definition is in terms of block matrices (p. 27, Def 1.2), but the
    graph-theoretic one is equivalent and central to the combinatorial approach. -/
def Irreducible (A : Matrix n n ℝ) : Prop :=
  IsStronglyConnected (toQuiver A)

/-- A matrix is primitive if it's irreducible and some power of it is strictly positive.
    The smallest such power is called the index of primitivity.
    This corresponds to the characterization in Berman & Plemmons, Chapter 2, Theorem 1.7(c) (p. 49),
    which is then used as the definition of a primitive matrix in Definition 1.8. -/
def IsPrimitive (A : Matrix n n ℝ) : Prop :=
  Irreducible A ∧ ∃ k > 0, ∀ i j, 0 < (A ^ k) i j

/-- Primitivity implies irreducibility. -/
theorem primitive_implies_irreducible {A : Matrix n n ℝ} [Nonempty n] :
    IsPrimitive A → Irreducible A := fun h => h.1

/-- For a matrix with the HasPerronFrobeniusProperty, we can derive irreducibility. -/
instance (A : Matrix n n ℝ) [Nonempty n] [HasPerronFrobeniusProperty A] : 
    Irreducible A := primitive_implies_irreducible HasPerronFrobeniusProperty.primitive

/-- The index of primitivity is the smallest positive integer k such that A^k is strictly positive. -/
noncomputable def indexOfPrimitivity (A : Matrix n n ℝ) (h : IsPrimitive A) : ℕ :=
  Nat.find (Classical.choose_spec h.2).exists

/-- This is a helper class to bundle the common hypotheses for the Perron-Frobenius theorem:
    nonnegativity and primitivity (which implies irreducibility). The book states these as
    assumptions on its theorems, e.g., 'If A is a nonnegative square matrix...'
    (Theorem 1.1, p. 47). -/
class HasPerronFrobeniusProperty (A : Matrix n n ℝ) : Prop where
  /-- All entries of the matrix are non-negative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- For some power `k`, `A^k` is strictly positive (primitivity implies irreducibility). -/
  primitive : IsPrimitive A

/-- A helper lemma stating that the product of two non-negative numbers is positive
iff both numbers are positive. -/
private lemma mul_pos_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · rintro rfl; rw [zero_mul] at h; exact h.false
    · rintro rfl; rw [mul_zero] at h; exact h.false
  · rintro ⟨ha_pos, hb_pos⟩; exact mul_pos ha_pos hb_pos

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*} [MulOneClass R]

/-- The target vertex of a path. -/
def target {V : Type*} [Quiver V] {a b : V} : Quiver.Path a b → V
| Quiver.Path.nil => a
| Quiver.Path.cons _ _ => b

/-- If a finite sum is positive, then there exists at least one summand that is positive. -/
lemma exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) : ∃ a ∈ s, 0 < f a := by
  by_contra h
  push_neg at h
  have h_nonpos : ∀ a ∈ s, f a ≤ 0 := h
  have h_sum_nonpos : ∑ a ∈ s, f a ≤ 0 := by
    apply Finset.sum_nonpos h_nonpos
  linarith [h_pos, h_sum_nonpos]

/-- Variant for when we know all terms satisfy a non-negativity condition. -/
lemma exists_mem_of_sum_pos' {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a)
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h
  push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := by
    intro a ha
    exact le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by
    rw [← Finset.sum_const_zero]
    congr 1
    ext a
    simp_all only [sum_const_zero, lt_self_iff_false]
  linarith [h_pos, h_sum_zero]

end Finset

omit [Nonempty n] in
/-- This theorem formalizes the fundamental combinatorial principle that the `(i, j)`-entry of `A^k`
    is positive if and only if there is a path of length `k` from `i` to `j` whose arrows
    correspond to positive entries in `A`.
    See Berman & Plemmons on p. 30, where it states "Since aᵢⱼ(q) > 0 if and only if there exists
    a sequence of q edges from Pᵢ to Pⱼ...".
    (Note: aᵢⱼ(q) is defined on p. 29 as the (i, j) element of A^q). -/
theorem pow_entry_pos_iff_exists_path (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    0 < (A ^ k) i j ↔ (letI := toQuiver A; ∃ p : Quiver.Path i j, p.length = k ∧ 0 < p.weight_from_vertices A) := by
  letI G := toQuiver A
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, gt_iff_lt, zero_lt_one]
    constructor
    · intro h_pos
      split_ifs at h_pos with h_eq
      · subst h_eq
        use Quiver.Path.nil
        simp [Quiver.Path.length, Quiver.Path.weight_from_vertices]
      · simp only [lt_self_iff_false] at h_pos;
    · rintro ⟨p, hp_len, _⟩
      have h_eq : i = j := Quiver.Path.eq_of_length_zero p hp_len
      subst h_eq
      have : p = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero p hp_len
      subst this
      simp
  | succ m ih =>
    simp_rw [pow_succ, mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ : ∃ l ∈ Finset.univ, 0 < (A ^ m) i l * A l j := by
        apply Finset.exists_mem_of_sum_pos' h_pos (fun x _ => mul_nonneg (pow_nonneg hA m i x) (hA x j))
      rw [mul_pos_iff_of_nonneg (pow_nonneg hA m i l) (hA l j)] at hl_pos
      obtain ⟨h_Am_pos, h_A_pos_val⟩ := hl_pos
      have h_Am_pos := (ih i l).mp h_Am_pos
      obtain ⟨p_il, hp_len, hp_weight⟩ := h_Am_pos
      use p_il.cons h_A_pos_val
      refine ⟨by simp [Quiver.Path.length_cons, hp_len], by simp [Quiver.Path.weight_from_vertices]; exact mul_pos hp_weight h_A_pos_val⟩
    · rintro ⟨p, hp_len, hp_weight⟩
      cases p with
      | nil => simp [Quiver.Path.length_nil] at hp_len
      | cons q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        -- The path p = q.cons e represents: i --q--> intermediate --e--> j
        -- We need to extract the positive weight contribution
        simp only [Quiver.Path.weight_from_vertices] at hp_weight
        -- Split the weight: weight(q.cons e) = weight(q) * A(intermediate, j)
        -- where e certifies A(intermediate, j) > 0
        have h_A_pos : 0 < A (q.target) j := e
        have h_q_weight_pos : 0 < q.weight_from_vertices A := by
          -- Since the total weight is positive and A(q.target, j) > 0, 
          -- the weight of q must also be positive
          have h_split : q.weight_from_vertices A * A q.target j = hp_weight := by
            exact hp_weight
          exact pos_of_mul_pos_right hp_weight (le_of_lt h_A_pos)
        have h_Am_pos : 0 < (A ^ m) i (q.target) := by
          apply (ih i (q.target)).mpr
          exact ⟨q, hp_len, h_q_weight_pos⟩
        apply Finset.sum_pos'
        · intro l _
          exact mul_nonneg (pow_nonneg hA m i l) (hA l j)
        · use q.target, Finset.mem_univ _
          exact mul_pos h_Am_pos h_A_pos

omit [Nonempty n] in
/-- A nonnegative matrix `A` is irreducible if and only if for every `i, j`, there exists a
    natural number `k` such that `(A^k) i j > 0`.
    This is a direct formalization of Berman & Plemmons, Chapter 2, Theorem 2.1 (p. 29). -/
theorem irreducible_iff_exists_pow_pos (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    Irreducible A ↔ ∀ i j, ∃ k, 0 < (A ^ k) i j := by
  letI G := toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p⟩ := h_irr i j
    use p.length
    rw [pow_entry_pos_iff_exists_path A hA_nonneg]
    use p
    exact ⟨rfl, Quiver.Path.weight_from_vertices_pos (fun {i j} h => h) p⟩
  · intro h_exists i j
    obtain ⟨k, hk_pos⟩ := h_exists i j
    rw [pow_entry_pos_iff_exists_path A hA_nonneg] at hk_pos
    obtain ⟨p, _, _⟩ := hk_pos
    exact ⟨p⟩

end Matrix

/-!
## Spectral Properties of Irreducible Matrices
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral radius of a matrix, defined as the supremum of absolute values of eigenvalues. -/
noncomputable def spectralRadius (A : Matrix n n ℂ) : ℝ := 
  sSup {|λ| | λ ∈ spectrum ℂ A.toLin'}

/-- For an irreducible nonnegative matrix, the spectral radius is a positive eigenvalue. -/
theorem spectralRadius_is_eigenvalue {A : Matrix n n ℝ} [Nonempty n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_irr : Irreducible A) :
    ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A.mulVec v = spectralRadius (A.map (algebraMap ℝ ℂ)) • v := by
  sorry -- This would require significant spectral theory development

/-- The Perron-Frobenius theorem: For irreducible nonnegative matrices,
    the spectral radius is a simple eigenvalue with a positive eigenvector. -/
theorem perronFrobenius_theorem {A : Matrix n n ℝ} [Nonempty n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_irr : Irreducible A) :
    ∃! v : n → ℝ, (∀ i, 0 < v i) ∧ (∑ i, v i = 1) ∧ 
    A.mulVec v = spectralRadius (A.map (algebraMap ℝ ℂ)) • v := by
  sorry -- This would require the full spectral theory development

/-- For primitive matrices, all eigenvalues other than the spectral radius 
    have strictly smaller absolute value. -/
theorem primitive_eigenvalue_gap {A : Matrix n n ℝ} [Nonempty n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_prim : IsPrimitive A) :
    ∀ λ ∈ spectrum ℂ A.toLin', λ ≠ spectralRadius (A.map (algebraMap ℝ ℂ)) → 
    |λ| < spectralRadius (A.map (algebraMap ℝ ℂ)) := by
  sorry -- This requires advanced spectral analysis

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- If a matrix `A` is strictly positive, then for any non-negative non-zero vector `v`,
the vector `A.mulVec v` is strictly positive. -/
lemma positive_mul_vec_pos {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < (A.mulVec v) i := by
  haveI : Nonempty n := by
    obtain ⟨k, _⟩ := Function.ne_iff.mp hv_ne_zero
    exact ⟨k⟩
  intro i
  simp [mulVec, dotProduct]
  obtain ⟨k, hvk_ne_zero⟩ : ∃ k, v k ≠ 0 := by rwa [Function.ne_iff] at hv_ne_zero
  have hv_k_pos : 0 < v k := (hv_nonneg k).lt_of_ne' hvk_ne_zero
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hA_pos i j).le (hv_nonneg j)
  · use k, Finset.mem_univ k
    exact mul_pos (hA_pos i k) hv_k_pos

end Matrix

