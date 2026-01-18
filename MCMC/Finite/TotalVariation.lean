--import Mathlib
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Multiplicity
import MCMC.Finite.Core

/-!
This module formalizes the analytical properties of the Dobrushin coefficient for
row-stochastic matrices on finite state spaces. The definitions and theorems are
grounded in the concepts introduced in R. L. Dobrushin's 1956 paper on the
Central Limit Theorem for nonstationary Markov chains.

The main components are:

-   **Total Variation Distance (`tvDist`):** The module defines the total variation
    distance as half the L1-norm between two probability vectors. This corresponds
    to the norm of the difference between two measures, `||μ₁ - μ₂||`, as
    discussed in the paper (cf. §1.4, eq. 1.10). The formalization includes a proof
    (`tvDist_eq_one_sub_sum_min`) of the identity `tvDist(u, v) = 1 - ∑ min(uⱼ, vⱼ)`,
    which directly connects the L1-based definition to the formulation `1 - ᾶ(μ₁, μ₂)`
    used by Dobrushin (cf. eq. 1.15, 1.16).

-   **Dobrushin Coefficient (`dobrushinCoeff`):** The coefficient `δ(P)` is formalized
    as the supremum of the total variation distance between any two rows of the
    stochastic matrix `P`. This quantity is related to Dobrushin's ergodic
    coefficient `α(P)` by the identity `δ(P) = 1 - α(P)` (cf. eq. 1.5, 1.5'). The
    paper's definition for denumerable chains (eq. 1.19), `α(Q) = inf ∑ min(qₖₘ, qₗₘ)`,
    is thus equivalent via the `tvDist_eq_one_sub_sum_min` identity.

-   **Contraction and Submultiplicativity:** The module proves two central properties
    of the coefficient:
    1.  The contraction theorem (`tvDist_contract`), which bounds the TV distance
        between the images of two distributions by `δ(P)` times their initial
        distance. This is the foundational result that establishes the coefficient's
        role in measuring convergence.
    2.  The submultiplicativity of the coefficient (`dobrushinCoeff_mul`), which
        states `δ(PQ) ≤ δ(P)δ(Q)`. This property corresponds to the inequality
        `1 - α(P_composed) ≤ Π(1 - α(P_i))` used in the paper's argument for
        bounding the ergodicity of multi-step transitions (cf. §1.11).

-   **Primitivity and Strict Contraction:** The final theorem in this module,
    `dobrushinCoeff_pow_lt_one_of_primitive`, establishes a sufficient condition
    for strict contractivity. It proves that if a stochastic matrix `P` is primitive,
    there exists a power `k > 0` such that `δ(P^k) < 1`. This provides a
    concrete combinatorial condition under which the assumptions of uniform
    ergodicity (i.e., `α(P) > 0` for some transition `P`) used throughout the
    Dobrushin paper are satisfied in the context of a time-homogeneous chain.
-/

noncomputable section
open Matrix Finset MCMC.Finite
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-!
Total variation on the finite simplex and the Dobrushin coefficient
for row-stochastic kernels.
-/

/-- Total variation distance on the finite simplex (sup over sets = 1/2 L1). -/
def tvDist (p q : n → ℝ) : ℝ :=
  (∑ j, |p j - q j|) / 2

lemma tvDist_nonneg (p q : n → ℝ) : 0 ≤ tvDist p q := by
  have : 0 ≤ ∑ j, |p j - q j| := by
    exact sum_nonneg (fun _ _ => abs_nonneg _)
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  simpa [tvDist, div_eq_mul_inv, mul_comm]

/-- For finite families with equal total mass, each coordinate deviation is bounded by TV. -/
lemma coord_abs_le_tvDist_of_eq_sum [DecidableEq n] (p q : n → ℝ)
    (hsum : ∑ j, p j = ∑ j, q j) (j : n) :
    |p j - q j| ≤ tvDist p q := by
  have hx_sum0 : ∑ t, (p t - q t) = 0 := by
    simp [sum_sub_distrib, hsum]
  have hsplit :
      ∑ t, |p t - q t|
        = |p j - q j| + ∑ t ∈ (Finset.univ.erase j), |p t - q t| := by
    have : (Finset.univ : Finset n) = insert j ((Finset.univ).erase j) := by
      simp
    calc
      ∑ t, |p t - q t|
          = ∑ t ∈ insert j ((Finset.univ).erase j), |p t - q t| := by
          rw [this]
          exact
            Eq.symm
              (sum_congr (congrArg (insert j) (congrFun (congrArg erase (id (Eq.symm this))) j))
                fun x => congrFun rfl)
      _ = |p j - q j| + ∑ t ∈ ((Finset.univ).erase j), |p t - q t| := by
            simp [Finset.mem_univ]
  have hrest_sum :
      ∑ t ∈ (Finset.univ.erase j), (p t - q t) = (q j - p j) := by
    have huniv_split :
        ∑ t, (p t - q t)
          = (p j - q j) + ∑ t ∈ (Finset.univ.erase j), (p t - q t) := by
      have : (Finset.univ : Finset n) = insert j ((Finset.univ).erase j) := by
        simp
      calc
        ∑ t, (p t - q t)
            = ∑ t ∈ insert j ((Finset.univ).erase j), (p t - q t) :=
              congrFun (congrArg Finset.sum this) fun t => p t - q t
        _ = (p j - q j) + ∑ t ∈ ((Finset.univ).erase j), (p t - q t) := by
              simp [Finset.mem_univ]
              grind
    have hx0' : (p j - q j) + ∑ t ∈  (Finset.univ.erase j), (p t - q t) = 0 := by
      simpa [huniv_split] using hx_sum0
    have := eq_neg_of_add_eq_zero_left hx0'
    simpa [sub_eq_add_neg, add_comm] using this
  have hrest_abs_le :
      |∑ t ∈  (Finset.univ.erase j), (p t - q t)|
        ≤ ∑ t ∈  (Finset.univ.erase j), |p t - q t| :=
    (abs_sum_le_sum_abs _ _)
  have hL1_ge :
      ∑ t, |p t - q t| ≥ |p j - q j| + |q j - p j| := by
    calc
      ∑ t, |p t - q t|
          = |p j - q j| + ∑ t ∈  (Finset.univ.erase j), |p t - q t| := hsplit
      _ ≥ |p j - q j| + |∑ t ∈  (Finset.univ.erase j), (p t - q t)| := by
            gcongr
      _ = |p j - q j| + |q j - p j| := by simp [hrest_sum]
  have h2mul : (∑ t, |p t - q t|) ≥ 2 * |p j - q j| := by
    simpa [two_mul, abs_sub_comm] using hL1_ge
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h_div : |p j - q j| ≤ (∑ t, |p t - q t|) / 2 := (le_div_iff₀' h2pos).mpr h2mul
  simpa [tvDist, div_eq_mul_inv, mul_comm] using h_div

/-- The row `i` of a row-stochastic matrix seen as a probability vector. -/
def rowDist (P : Matrix n n ℝ) (i : n) : n → ℝ := fun j => P i j

/-- Dobrushin coefficient δ(P) = sup over pairs of rows of TV distance. -/
def dobrushinCoeff (P : Matrix n n ℝ) : ℝ :=
  sSup { d | ∃ i i' : n, d = tvDist (rowDist P i) (rowDist P i') }

lemma dobrushinCoeff_nonneg [Nonempty n] (P : Matrix n n ℝ) : 0 ≤ dobrushinCoeff P := by
  let f : (n × n) → ℝ := fun p => tvDist (rowDist P p.1) (rowDist P p.2)
  have hset_eq : { d | ∃ i i' : n, d = tvDist (rowDist P i) (rowDist P i') }
                  = Set.range f := by
    ext d; constructor
    · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
    · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
  have hfin : (Set.range f).Finite := (Set.finite_range f)
  have hmem : 0 ∈ Set.range f := by
    let i0 : n := Classical.arbitrary n
    refine ⟨⟨i0, i0⟩, ?_⟩
    simp [f, rowDist, tvDist, sub_self, abs_zero, sum_const_zero]
  have hbdd : BddAbove (Set.range f) := hfin.bddAbove
  simpa [dobrushinCoeff, hset_eq] using le_csSup hbdd hmem

/-- Contraction in TV under a row-stochastic kernel (with Dobrushin's coefficient). -/
lemma tvDist_contract [Nonempty n]
    (P : Matrix n n ℝ) --(hP : MCMC.Finite.IsStochastic P)
    (p q : n → ℝ)-- (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (hp1 : ∑ j, p j = 1) (hq1 : ∑ j, q j = 1) :
    tvDist ((fun j => ∑ k, p k * P k j)) ((fun j => ∑ k, q k * P k j))
      ≤ dobrushinCoeff P * tvDist p q := by
  let r : n → ℝ := fun k => p k - q k
  have hsum_r : ∑ k, r k = 0 := by
    simp [r, sum_sub_distrib, hp1, hq1]
  let a : n → ℝ := fun j => ∑ k, r k * P k j
  let s : n → ℝ := fun j => if 0 ≤ a j then 1 else -1
  have hs_abs : ∀ j, |s j| = 1 := by
    intro j; by_cases h : 0 ≤ a j
    · simp [s, h]
    · have : a j < 0 := lt_of_not_ge h
      simp [s, h]
  have hsum_abs_eq : ∑ j, |a j| = ∑ j, s j * a j := by
    apply sum_congr rfl; intro j _
    by_cases h : 0 ≤ a j
    · simp [s, h, abs_of_nonneg h]
    · have : a j < 0 := lt_of_not_ge h
      have hnn : a j ≤ 0 := le_of_lt this
      aesop
  let g : n → ℝ := fun k => ∑ j, s j * P k j
  have hswap : ∑ j, s j * a j = ∑ k, r k * g k := by
    unfold a g
    calc
      ∑ j, s j * ∑ k, r k * P k j
          = ∑ j, ∑ k, s j * (r k * P k j) := by
                simp [mul_sum]
      _ = ∑ j, ∑ k, r k * (s j * P k j) := by
                apply sum_congr rfl; intro j _; simp [mul_left_comm, mul_assoc, mul_comm]
      _ = ∑ k, ∑ j, r k * (s j * P k j) := by
                simpa using
                  (Finset.sum_comm (s := (Finset.univ : Finset n))
                    (t := (Finset.univ : Finset n))
                    (f := fun j k => r k * (s j * P k j)))
      _ = ∑ k, r k * ∑ j, s j * P k j := by
                simp [mul_sum]
  -- oscillation bound for g via rows of P
  have g_diff_le : ∀ k ℓ, |g k - g ℓ| ≤ 2 * dobrushinCoeff P := by
    intro k ℓ
    have : |g k - g ℓ| ≤ ∑ j, |P k j - P ℓ j| := by
      have : g k - g ℓ = ∑ j, s j * (P k j - P ℓ j) := by
        simp [g, sum_sub_distrib, mul_sub]
      calc
        |g k - g ℓ| = |∑ j, s j * (P k j - P ℓ j)| := by simp [this]
        _ ≤ ∑ j, |s j * (P k j - P ℓ j)| := by
              simpa using
                (abs_sum_le_sum_abs
                  (s := (Finset.univ : Finset n))
                  (f := fun j => s j * (P k j - P ℓ j)))
        _ = ∑ j, |s j| * |P k j - P ℓ j| := by
              apply sum_congr rfl; intro j _; simp [abs_mul]
        _ = ∑ j, |P k j - P ℓ j| := by
              simp [hs_abs]
    let f : (n × n) → ℝ := fun p => tvDist (rowDist P p.1) (rowDist P p.2)
    have hset_eq :
      { d | ∃ i i' : n, d = tvDist (rowDist P i) (rowDist P i') } = Set.range f := by
      ext d; constructor
      · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
      · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
    have hbdd : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
    have h_tv_le : tvDist (rowDist P k) (rowDist P ℓ) ≤ dobrushinCoeff P := by
      have : tvDist (rowDist P k) (rowDist P ℓ) ∈ Set.range f := ⟨⟨k, ℓ⟩, rfl⟩
      simpa [dobrushinCoeff, hset_eq] using (le_csSup hbdd this)
    have : |g k - g ℓ| ≤ 2 * tvDist (rowDist P k) (rowDist P ℓ) := by
      simpa [two_mul, tvDist, rowDist, div_eq_mul_inv, mul_comm] using this
    exact this.trans (by
      have : tvDist (rowDist P k) (rowDist P ℓ) ≤ dobrushinCoeff P := h_tv_le
      have hnonneg : 0 ≤ 2 := by norm_num
      simp [*])
  obtain ⟨kmax, _, hkmax⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset n)) (f := fun k => g k)
      (by simp)
  obtain ⟨kmin, _, hkmin⟩ :=
    Finset.exists_min_image (s := (Finset.univ : Finset n)) (f := fun k => g k)
      (by simp)
  have h_le_max : ∀ k, g k ≤ g kmax := by intro k; exact hkmax k (by simp)
  have h_ge_min : ∀ k, g kmin ≤ g k := by intro k; exact hkmin k (by simp)
  let rpos : n → ℝ := fun k => max (r k) 0
  let rneg : n → ℝ := fun k => max (-r k) 0
  have hrpos_nonneg : ∀ k, 0 ≤ rpos k := by
    intro k; have : 0 ≤ max (0:ℝ) (r k) := le_max_left _ _
    simp [rpos]
  have hrneg_nonneg : ∀ k, 0 ≤ rneg k := by
    intro k; have : 0 ≤ max (0:ℝ) (-r k) := le_max_left _ _
    simp [rneg]
  have h_r_decomp : ∀ k, r k = rpos k - rneg k := by
    intro k; by_cases hk : 0 ≤ r k
    · have : -r k ≤ 0 := neg_nonpos.mpr hk
      simp [rpos, rneg, hk, this]
    · have hk' : r k ≤ 0 := le_of_lt (lt_of_not_ge hk)
      have hneg' : 0 ≤ -r k := neg_nonneg.mpr hk'
      simp [rpos, rneg, hk', hneg', sub_eq_add_neg, add_comm]
  have hsum_pos_eq_neg : ∑ k, rpos k = ∑ k, rneg k := by
    have hsum : (∑ k, rpos k) - (∑ k, rneg k) = 0 := by
      simpa [h_r_decomp, sum_sub_distrib] using hsum_r
    exact sub_eq_zero.mp hsum
  have h_abs_split : ∀ k, |r k| = rpos k + rneg k := by
    intro k; by_cases hk : 0 ≤ r k
    · have : -r k ≤ 0 := neg_nonpos.mpr hk
      simp [rpos, rneg, hk, this, abs_of_nonneg]
    · have hk' : r k ≤ 0 := le_of_lt (lt_of_not_ge hk)
      have hneg' : 0 ≤ -r k := neg_nonneg.mpr hk'
      simp [rpos, rneg, hk', hneg', abs_of_nonpos, add_comm]
  have hsum_abs : ∑ k, |r k| = 2 * (∑ k, rpos k) := by
    calc
      ∑ k, |r k| = ∑ k, (rpos k + rneg k) := by
          apply sum_congr rfl; intro k _; simp [h_abs_split k]
      _ = (∑ k, rpos k) + (∑ k, rneg k) := by
          simp [sum_add_distrib]
      _ = (∑ k, rpos k) + (∑ k, rpos k) := by
          simp [hsum_pos_eq_neg]
      _ = 2 * (∑ k, rpos k) := by ring
  let α : ℝ := ∑ k, rpos k
  have h_sum_pos_le : ∑ k, rpos k * g k ≤ (g kmax) * α := by
    calc
      ∑ k, rpos k * g k
          ≤ ∑ k, rpos k * (g kmax) := by
            apply sum_le_sum; intro k _; exact mul_le_mul_of_nonneg_left (h_le_max k) (hrpos_nonneg k)
      _ = (g kmax) * ∑ k, rpos k := by
        simp [mul_comm]
        exact Eq.symm (sum_mul univ (fun i => max (r i) 0) (g kmax))
      _ = (g kmax) * α := rfl
  have h_sum_neg_ge : ∑ k, rneg k * g k ≥ (g kmin) * α := by
    have hα : α = ∑ k, rneg k := by
      simpa [α] using hsum_pos_eq_neg
    have h : (g kmin) * α ≤ ∑ k, rneg k * g k := by
      calc
        (g kmin) * α = ∑ k, rneg k * (g kmin) := by
          simp [mul_comm, hα, sum_mul]
        _ ≤ ∑ k, rneg k * g k := by
          apply sum_le_sum; intro k _; exact mul_le_mul_of_nonneg_left (h_ge_min k) (hrneg_nonneg k)
    simpa using h
  have h_rg_le : ∑ k, r k * g k ≤ (g kmax - g kmin) * α := by
    have h' :
        ∑ k, rpos k * g k - ∑ k, rneg k * g k
          ≤ g kmax * α - g kmin * α :=
      sub_le_sub h_sum_pos_le h_sum_neg_ge
    have h'' :
        ∑ k, rpos k * g k - ∑ k, rneg k * g k
          ≤ (g kmax - g kmin) * α := by
      have hR : g kmax * α - g kmin * α = (g kmax - g kmin) * α := by ring
      simpa [hR] using h'
    have hL :
        ∑ k, r k * g k
          = ∑ k, rpos k * g k - ∑ k, rneg k * g k := by
      calc
        ∑ k, r k * g k
            = ∑ k, (rpos k - rneg k) * g k := by
              apply sum_congr rfl; intro k _; simp [h_r_decomp k]
        _ = ∑ k, (rpos k * g k - rneg k * g k) := by
              apply sum_congr rfl; intro k _; rw [@mul_sub_right_distrib]
        _ = ∑ k, rpos k * g k - ∑ k, rneg k * g k := by
              simp [sum_sub_distrib]
    simpa [hL] using h''
  have h_sum_bound : ∑ j, |a j| ≤ (g kmax - g kmin) / 2 * ∑ k, |r k| := by
    have hα : α = (∑ k, |r k|) / 2 := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have : 2 * α = ∑ k, |r k| := by
        simp [α, hsum_abs, two_mul]
      have : ∑ k, |r k| = 2 * α := by simpa [α] using hsum_abs
      have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
      calc
        α = (2 * α) / 2 := by field_simp
        _ = (∑ k, |r k|) / 2 := by simp [this]
    have : ∑ j, |a j| = ∑ k, r k * g k := by
      simpa [hswap] using hsum_abs_eq
    calc
      ∑ j, |a j| = ∑ k, r k * g k := this
      _ ≤ (g kmax - g kmin) * α := h_rg_le
      _ = ((g kmax - g kmin) / 2) * (∑ k, |r k|) := by
            have : α = (∑ k, |r k|) / 2 := hα
            simp [this, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  -- relate oscillation of g to δ(P)
  have h_osc_le : g kmax - g kmin ≤ 2 * dobrushinCoeff P := by
    have := g_diff_le kmax kmin
    have hge : g kmin ≤ g kmax := h_ge_min kmax
    have : |g kmax - g kmin| = g kmax - g kmin := by
      simp [abs_of_nonneg (sub_nonneg.mpr hge)]
    simp; grind
  have hLHS : tvDist (fun j => ∑ k, p k * P k j) (fun j => ∑ k, q k * P k j)
            = (∑ j, |a j|) / 2 := by
    simp only [tvDist, a, r, sub_eq_add_neg]
    congr 1
    dsimp [sum_neg_distrib, sum_add_distrib]
    congr 1
    ext j
    dsimp [sum_add_distrib, mul_neg, sum_neg_distrib]
    ring_nf
    simp
  have hR_r : tvDist p q = (∑ k, |r k|) / 2 := by
    simp [tvDist, r]
  have hcoef : (g kmax - g kmin) / 2 ≤ dobrushinCoeff P := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    rwa [div_le_iff h2pos, mul_comm]
  have h_mul : (∑ j, |a j|) ≤ dobrushinCoeff P * ∑ k, |r k| := by
    have S_nonneg : 0 ≤ ∑ k, |r k| :=
      sum_nonneg (by
        intro _ _
        exact abs_nonneg _)
    have h_temp :
        ((g kmax - g kmin) / 2) * (∑ k, |r k|) ≤
          dobrushinCoeff P * (∑ k, |r k|) :=
      mul_le_mul_of_nonneg_right hcoef S_nonneg
    exact h_sum_bound.trans h_temp
  have h_div : (∑ j, |a j|) / 2 ≤ (dobrushinCoeff P * ∑ k, |r k|) / 2 := by
    have : (1 / 2 : ℝ) * (∑ j, |a j|) ≤
           (1 / 2 : ℝ) * (dobrushinCoeff P * ∑ k, |r k|) :=
      mul_le_mul_of_nonneg_left h_mul (by norm_num)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have : tvDist (fun j => ∑ k, p k * P k j)
                (fun j => ∑ k, q k * P k j)
        ≤ dobrushinCoeff P * tvDist p q := by
    rw [hLHS, hR_r, ← mul_div_assoc]
    exact h_div
  exact this

open MCMC.Finite

/-- Submultiplicativity of the Dobrushin coefficient. -/
lemma dobrushinCoeff_mul [DecidableEq n] (P Q : Matrix n n ℝ)
    [Nonempty n]
    (hP : IsStochastic P) (_ : IsStochastic Q) :
    dobrushinCoeff (P * Q) ≤ dobrushinCoeff P * dobrushinCoeff Q := by
  classical
  -- we rewrite δ(P*Q) as sSup over a finite range
  let fPQ : (n × n) → ℝ := fun p => tvDist (rowDist (P * Q) p.1) (rowDist (P * Q) p.2)
  have hset_eq_PQ :
      { d | ∃ i i' : n, d = tvDist (rowDist (P * Q) i) (rowDist (P * Q) i') }
        = Set.range fPQ := by
    ext d; constructor
    · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
    · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
  have hbddPQ : BddAbove (Set.range fPQ) := (Set.finite_range fPQ).bddAbove
  have hforall :
      ∀ d ∈ Set.range fPQ, d ≤ dobrushinCoeff P * dobrushinCoeff Q := by
    intro d hd
    rcases hd with ⟨⟨i, i'⟩, rfl⟩
    have hp1 : ∑ j, rowDist P i j = 1 := by simpa [rowDist] using hP.2 i
    have hq1 : ∑ j, rowDist P i' j = 1 := by simpa [rowDist] using hP.2 i'
    -- contract by Q
    have hcontract :
        tvDist (rowDist (P * Q) i) (rowDist (P * Q) i')
          ≤ dobrushinCoeff Q * tvDist (rowDist P i) (rowDist P i') := by
      simpa [rowDist, Matrix.mul_apply] using
        (tvDist_contract (P := Q) (p := rowDist P i) (q := rowDist P i') (hp1 := hp1) (hq1 := hq1))
    -- bound tvDist among rows of P by δ(P)
    let fP : (n × n) → ℝ := fun p => tvDist (rowDist P p.1) (rowDist P p.2)
    have hset_eq_P :
      { d | ∃ i i' : n, d = tvDist (rowDist P i) (rowDist P i') } = Set.range fP := by
      ext d; constructor
      · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
      · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
    have hbddP : BddAbove (Set.range fP) := (Set.finite_range fP).bddAbove
    have hleP : tvDist (rowDist P i) (rowDist P i') ≤ dobrushinCoeff P := by
      have hx : tvDist (rowDist P i) (rowDist P i') ∈ Set.range fP := ⟨⟨i, i'⟩, rfl⟩
      simpa [dobrushinCoeff, hset_eq_P] using le_csSup hbddP hx
    have hnonnegQ : 0 ≤ dobrushinCoeff Q := dobrushinCoeff_nonneg (P := Q)
    have := hcontract.trans (mul_le_mul_of_nonneg_left hleP hnonnegQ)
    simpa [mul_comm] using this
  have hnonemptyPQ : (Set.range fPQ).Nonempty := by
    classical
    let i0 : n := Classical.arbitrary n
    exact ⟨fPQ ⟨i0, i0⟩, ⟨⟨i0, i0⟩, rfl⟩⟩
  have : sSup (Set.range fPQ) ≤ dobrushinCoeff P * dobrushinCoeff Q :=
    csSup_le hnonemptyPQ hforall
  simpa [dobrushinCoeff, hset_eq_PQ] using this

/-- Power bound for the Dobrushin coefficient. -/
lemma dobrushinCoeff_pow [DecidableEq n] (P : Matrix n n ℝ) [Nonempty n] (hP : MCMC.Finite.IsStochastic P) (k : ℕ) :
    dobrushinCoeff (P^k) ≤ (dobrushinCoeff P)^k := by
  classical
  induction' k with k ih
  · -- base: δ(I) ≤ 1 = (δ P)^0
    have hpair :
        ∀ i i' : n,
          tvDist (rowDist (1 : Matrix n n ℝ) i) (rowDist (1 : Matrix n n ℝ) i') ≤ 1 := by
      intro i i'
      have hpt :
          ∀ j,
            |(1 : Matrix n n ℝ) i j - (1 : Matrix n n ℝ) i' j|
              ≤ |(1 : Matrix n n ℝ) i j| + |(1 : Matrix n n ℝ) i' j| := by
        intro j
        simpa [sub_eq_add_neg] using
          (abs_add_le ((1 : Matrix n n ℝ) i j) (-(1 : Matrix n n ℝ) i' j))
      have hsum_le :
          ∑ j, |(1 : Matrix n n ℝ) i j - (1 : Matrix n n ℝ) i' j|
            ≤ ∑ j, (|(1 : Matrix n n ℝ) i j| + |(1 : Matrix n n ℝ) i' j|) := by
        apply sum_le_sum
        intro j _
        simpa using hpt j
      have hsum_abs_one (i : n) : ∑ j, |(1 : Matrix n n ℝ) i j| = 1 := by
        classical
        have habs : ∀ j, |(1 : Matrix n n ℝ) i j| = (if i = j then (1 : ℝ) else 0) := by
          intro j
          by_cases h : i = j
          · simp [Matrix.one_apply, h]
          · simp [h]
        have hsum_eq :
            ∑ j, |(1 : Matrix n n ℝ) i j| = ∑ j, (if i = j then (1 : ℝ) else 0) := by
          apply sum_congr rfl
          intro j _
          simpa using habs j
        have hsum_ind : ∑ j, (if i = j then (1 : ℝ) else 0) = 1 := by
          simp
        simp [hsum_eq]
      have : (∑ j, |(1 : Matrix n n ℝ) i j - (1 : Matrix n n ℝ) i' j|) / 2 ≤ 1 := by
        have h2 : (0 : ℝ) < 2 := by norm_num
        have hnum :
            ∑ j, |(1 : Matrix n n ℝ) i j - (1 : Matrix n n ℝ) i' j| ≤ 2 := by
          have hbound :
              ∑ j, |(1 : Matrix n n ℝ) i j - (1 : Matrix n n ℝ) i' j|
                ≤ (∑ j, |(1 : Matrix n n ℝ) i j|) + (∑ j, |(1 : Matrix n n ℝ) i' j|) := by
            simpa [sum_add_distrib] using hsum_le
          have hx : (∑ j, |(1 : Matrix n n ℝ) i j|) + (∑ j, |(1 : Matrix n n ℝ) i' j|) = (2 : ℝ) := by
            have h12 : (1 : ℝ) + 1 = 2 := by norm_num
            simpa [hsum_abs_one i, hsum_abs_one i'] using h12
          simpa [hx] using hbound
        exact (div_le_iff h2).mpr (by simpa [one_mul] using hnum)
      simpa [tvDist, rowDist] using this
    let fId : (n × n) → ℝ :=
      fun p => tvDist (rowDist (1 : Matrix n n ℝ) p.1) (rowDist (1 : Matrix n n ℝ) p.2)
    have hforall : ∀ d ∈ Set.range fId, d ≤ 1 := by
      intro d hd
      rcases hd with ⟨⟨i, i'⟩, rfl⟩
      simpa using hpair i i'
    have hnonempty : (Set.range fId).Nonempty := by
      let i0 : n := Classical.arbitrary n
      exact ⟨fId ⟨i0, i0⟩, ⟨⟨i0, i0⟩, rfl⟩⟩
    have hset_eqId :
        { d | ∃ i i' : n, d = tvDist (rowDist (1 : Matrix n n ℝ) i) (rowDist (1 : Matrix n n ℝ) i') }
          = Set.range fId := by
      ext d; constructor
      · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
      · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
    have : sSup (Set.range fId) ≤ 1 := csSup_le hnonempty hforall
    simpa [dobrushinCoeff, pow_zero, rowDist, hset_eqId] using this
  · have hPow : IsStochastic (P^k) := by
      simpa using (isStochastic_pow (P := P) (hP := hP) k)
    have hmul :
        dobrushinCoeff (P^(k+1)) ≤ dobrushinCoeff (P^k) * dobrushinCoeff P := by
      simpa [pow_succ] using
        (dobrushinCoeff_mul (P := P^k) (Q := P) (hP := hPow) hP)
    have hnonneg : 0 ≤ dobrushinCoeff P := dobrushinCoeff_nonneg (P := P)
    have := hmul.trans (mul_le_mul_of_nonneg_right ih hnonneg)
    simpa [pow_succ, mul_left_comm, mul_comm, mul_assoc] using this

/-- Entrywise deviation is bounded by TV distance when the totals match. -/
lemma entry_abs_le_tvDist_of_rows [DecidableEq n]
    (P : Matrix n n ℝ) (i : n) (x : n → ℝ) (j : n)
    (hsum : ∑ t, rowDist P i t = ∑ t, x t) :
    |(P i j) - x j| ≤ tvDist (rowDist P i) x := by
  simpa [rowDist] using
    coord_abs_le_tvDist_of_eq_sum (p := rowDist P i) (q := x) (hsum := by simpa [rowDist] using hsum) (j := j)

-- Helper: TV identity for nonnegative unit-mass vectors.
lemma tvDist_eq_one_sub_sum_min
    (u v : n → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hv0 : ∀ j, 0 ≤ v j)
    (hu1 : ∑ j, u j = 1) (hv1 : ∑ j, v j = 1) :
    Matrix.tvDist u v = 1 - ∑ j, min (u j) (v j) := by
  classical
  have habs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      |a - b| = a + b - 2 * min a b := by
    by_cases h : a ≤ b
    · have hnonpos : a - b ≤ 0 := sub_nonpos.mpr h
      have hmin : min a b = a := by simpa [min_eq_left_iff] using h
      calc
        |a - b| = -(a - b) := abs_of_nonpos hnonpos
        _ = b - a := by ring
        _ = a + b - 2 * a := by ring
        _ = a + b - 2 * min a b := by simp [hmin]
    · have h' : b ≤ a := le_of_not_ge h
      have hnonneg : 0 ≤ a - b := sub_nonneg.mpr h'
      have hmin : min a b = b := by simpa [min_eq_right_iff] using h'
      calc
        |a - b| = a - b := abs_of_nonneg hnonneg
        _ = a + b - 2 * b := by ring
        _ = a + b - 2 * min a b := by simp [hmin]
  have hsum_abs :
      ∑ j, |u j - v j|
        = ∑ j, (u j + v j - 2 * min (u j) (v j)) := by
    apply sum_congr rfl
    intro j _
    exact habs (u j) (v j) (hu0 j) (hv0 j)
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hdiv :
      (∑ j, |u j - v j|) / 2
        = 1 - ∑ j, min (u j) (v j) := by
    calc
      (∑ j, |u j - v j|) / 2
          = (∑ j, (u j + v j - 2 * min (u j) (v j))) / 2 := by
                simp [hsum_abs]
      _ = ((∑ j, (u j + v j)) - ∑ j, (2 * min (u j) (v j))) / 2 := by
                simp [sum_sub_distrib]
      _ = ((∑ j, u j) + (∑ j, v j) - 2 * ∑ j, min (u j) (v j)) / 2 := by
                simp only [sum_add_distrib, two_mul]
      _ = (2 - 2 * ∑ j, min (u j) (v j)) / 2 := by
                simp only [hu1, hv1, one_add_one_eq_two]
      _ = 1 - ∑ j, min (u j) (v j) := by
                have := sub_div (2 : ℝ) (2 * ∑ j, min (u j) (v j)) (2 : ℝ)
                simpa [h2ne, mul_comm, mul_left_comm, mul_assoc] using this
  simpa [Matrix.tvDist] using hdiv

/--
  Primitive ⇒ some power has Dobrushin coefficient strictly less than 1,
  with an explicit quantitative bound via the minimal entry.
-/
theorem dobrushinCoeff_pow_lt_one_of_primitive
    [Nonempty n] [ DecidableEq n] (P : Matrix n n ℝ)
    (h_stoch : IsStochastic P) (h_prim : IsPrimitive P) :
    ∃ k > 0, Matrix.dobrushinCoeff (P^k) < 1 := by
  classical
  rcases h_prim with ⟨h_nonneg, ⟨k, hk_pos, hpos⟩⟩
  have hPk : IsStochastic (P^k) := by
    simpa using (isStochastic_pow (P := P) (hP := h_stoch) k)
  let s : Finset (n × n) := (Finset.univ.product Finset.univ)
  obtain ⟨p0, hp0_mem, hmin⟩ :=
    Finset.exists_min_image (s := s) (f := fun p : n×n => (P^k) p.1 p.2)
      (by
        refine (Finset.univ_nonempty.product Finset.univ_nonempty))
  let β : ℝ := (P^k) p0.1 p0.2
  have hβ_pos : 0 < β := hpos p0.1 p0.2
  have hβ_le (i j : n) : β ≤ (P^k) i j := by
    have hij_mem : (i, j) ∈ s := by simp [s]
    exact hmin (i, j) hij_mem
  have h_overlap (i i' : n) :
      ∑ j, min ((P^k) i j) ((P^k) i' j) ≥ (Fintype.card n : ℝ) * β := by
    have hpoint : ∀ j, β ≤ min ((P^k) i j) ((P^k) i' j) := by
      intro j
      have h1 := hβ_le i j
      have h2 := hβ_le i' j
      exact le_min_iff.mpr ⟨h1, h2⟩
    have : ∑ j, (β : ℝ) ≤ ∑ j, min ((P^k) i j) ((P^k) i' j) :=
      sum_le_sum (by intro j _; exact hpoint j)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hpair (i i' : n) :
      Matrix.tvDist (Matrix.rowDist (P^k) i) (Matrix.rowDist (P^k) i')
        ≤ 1 - (Fintype.card n : ℝ) * β := by
    have hi0 : ∀ j, 0 ≤ (P^k) i j := by intro j; exact (hPk.1 i j)
    have hi'0 : ∀ j, 0 ≤ (P^k) i' j := by intro j; exact (hPk.1 i' j)
    have hi1 : ∑ j, (P^k) i j = 1 := by simpa [Matrix.rowDist] using hPk.2 i
    have hi'1 : ∑ j, (P^k) i' j = 1 := by simpa [Matrix.rowDist] using hPk.2 i'
    have := tvDist_eq_one_sub_sum_min
      (u := Matrix.rowDist (P^k) i) (v := Matrix.rowDist (P^k) i')
      (hu0 := hi0) (hv0 := hi'0) (hu1 := hi1) (hv1 := hi'1)
    have : Matrix.tvDist (Matrix.rowDist (P^k) i) (Matrix.rowDist (P^k) i')
            = 1 - ∑ j, min ((P^k) i j) ((P^k) i' j) := by
      simpa [Matrix.rowDist] using this
    have hover := h_overlap i i'
    have : Matrix.tvDist (Matrix.rowDist (P^k) i) (Matrix.rowDist (P^k) i')
            ≤ 1 - (Fintype.card n : ℝ) * β := by
      rw [this]
      have h_mono : 1 - ∑ j, min ((P^k) i j) ((P^k) i' j)
                ≤ 1 - (Fintype.card n : ℝ) * β := by
        exact sub_le_sub_left hover 1
      exact h_mono
    exact this
  -- Take sup over all pairs of rows to bound δ(P^k)
  let fPk : (n × n) → ℝ :=
    fun p => Matrix.tvDist (Matrix.rowDist (P^k) p.1) (Matrix.rowDist (P^k) p.2)
  have hforall : ∀ d ∈ Set.range fPk, d ≤ 1 - (Fintype.card n : ℝ) * β := by
    intro d hd; rcases hd with ⟨⟨i, i'⟩, rfl⟩; simpa using hpair i i'
  have hnonempty : (Set.range fPk).Nonempty := by
    let i0 : n := Classical.arbitrary n
    exact ⟨fPk ⟨i0, i0⟩, ⟨⟨i0, i0⟩, rfl⟩⟩
  have hset_eq :
      { d | ∃ i i' : n, d = Matrix.tvDist (Matrix.rowDist (P^k) i) (Matrix.rowDist (P^k) i') }
        = Set.range fPk := by
    ext d; constructor
    · intro h; rcases h with ⟨i, i', rfl⟩; exact ⟨⟨i, i'⟩, rfl⟩
    · intro h; rcases h with ⟨⟨i, i'⟩, rfl⟩; exact ⟨i, i', rfl⟩
  have h_sup :
      Matrix.dobrushinCoeff (P^k) ≤ 1 - (Fintype.card n : ℝ) * β := by
    have : sSup (Set.range fPk) ≤ 1 - (Fintype.card n : ℝ) * β :=
      csSup_le hnonempty hforall
    simpa [Matrix.dobrushinCoeff, hset_eq] using this
  have hcard_pos : 0 < (Fintype.card n : ℝ) := by
    have : (0 : ℕ) < Fintype.card n := Fintype.card_pos_iff.mpr ‹Nonempty n›
    exact_mod_cast this
  have hbound_lt_one : 1 - (Fintype.card n : ℝ) * β < 1 := by
    have : 0 < (Fintype.card n : ℝ) * β := mul_pos hcard_pos hβ_pos
    linarith
  exact ⟨k, hk_pos, lt_of_le_of_lt h_sup hbound_lt_one⟩

-- Primitive stochastic matrices admit a power with Dobrushin coefficient < 1.
theorem dobrushinCoeff_lt_one_of_primitive
    [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (h_stoch : IsStochastic P) (h_prim : IsPrimitive P) :
    ∃ k > 0, Matrix.dobrushinCoeff (P^k) < 1 := by
  exact dobrushinCoeff_pow_lt_one_of_primitive (P := P) h_stoch h_prim

end Matrix
