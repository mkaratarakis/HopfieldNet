import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Aperiodic
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Stochastic
namespace MCMC.Finite

open Matrix Finset
open BigOperators
variable {n : Type*} [Fintype n]

/--
  A matrix P is (row) stochastic if it is non-negative and its rows sum to 1.
  This is the standard definition for a Markov chain transition matrix.
-/
def IsStochastic (P : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = 1)

lemma isStochastic_one [DecidableEq n] : IsStochastic (1 : Matrix n n ℝ) := by
  constructor
  · intro i j
    by_cases h : i = j
    · simp [Matrix.one_apply, h]
    · simp [h]
  · intro i
    simp [Matrix.one_apply, Finset.mem_univ]

lemma isStochastic_mul {P Q : Matrix n n ℝ}
    (hP : IsStochastic P) (hQ : IsStochastic Q) :
    IsStochastic (P * Q) := by
  constructor
  · intro i j
    have hterm : ∀ k, 0 ≤ P i k * Q k j := by
      intro k
      exact mul_nonneg (hP.1 i k) (hQ.1 k j)
    have : 0 ≤ ∑ k, P i k * Q k j :=
      sum_nonneg (by intro k _; simpa using hterm k)
    simpa [Matrix.mul_apply] using this
  · intro i
    calc
      ∑ j, (P * Q) i j
          = ∑ j, ∑ k, P i k * Q k j := by simp [Matrix.mul_apply]
      _ = ∑ k, ∑ j, P i k * Q k j := by
            simpa using
              (Finset.sum_comm (s := (Finset.univ : Finset n))
                (t := (Finset.univ : Finset n))
                (f := fun j k => P i k * Q k j))
      _ = ∑ k, P i k * ∑ j, Q k j := by
            simp [mul_sum]
      _ = ∑ k, P i k * 1 := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [hQ.2 k]
      _ = ∑ k, P i k := by simp
      _ = 1 := hP.2 i

lemma isStochastic_pow [DecidableEq n] {P : Matrix n n ℝ} (hP : IsStochastic P) :
    ∀ k, IsStochastic (P^k)
  | 0 => by simpa [pow_zero] using isStochastic_one
  | k+1 =>
    by
      have hk : IsStochastic (P^k) := isStochastic_pow hP k
      simpa [pow_succ] using isStochastic_mul hk hP

/--
  A probability distribution π (represented as a column vector in the standard simplex)
  is stationary for P if Pᵀ *ᵥ π = π.
  (This corresponds to the row vector definition π_row P = π_row).
-/
def IsStationary (P : Matrix n n ℝ) (π : stdSimplex ℝ n) : Prop :=
  Pᵀ *ᵥ π.val = π.val

/-- The main object for a verified MCMC algorithm on finite spaces. -/
class IsMCMC [DecidableEq n] (P : Matrix n n ℝ) (π : stdSimplex ℝ n) where
  stochastic : IsStochastic P
  stationary : IsStationary P π
  irreducible : Matrix.IsIrreducible P
  primitive : IsPrimitive P

variable [Nonempty n]

/--
  Leveraging the PF theorem to show existence and uniqueness of a stationary distribution
  for irreducible stochastic matrices.
-/
theorem exists_unique_stationary_distribution_of_irreducible
    [DecidableEq n]
    {P : Matrix n n ℝ} (h_stoch : IsStochastic P) (h_irred : Matrix.IsIrreducible P) :
    ∃! (π : stdSimplex ℝ n), IsStationary P π := by
  -- 1. Pᵀ is Irreducible. (Irreducibility is preserved under transposition for non-negative matrices).
  have hPT_irred : Matrix.IsIrreducible Pᵀ := isIrreducible_transpose_iff.mpr h_irred
  -- 2. Pᵀ is Column-Stochastic. (Since P is row-stochastic).
  have hPT_col_stoch : ∀ j, ∑ i, Pᵀ i j = 1 := by
    intro j
    simp [transpose_apply]
    exact h_stoch.2 j
  -- 3. We apply the PF theorem to Pᵀ.
  have h_exists := Matrix.exists_positive_eigenvector_of_irreducible_stochastic hPT_irred hPT_col_stoch
  -- 4. The result (Pᵀ *ᵥ v = v) is exactly the definition of IsStationary P π.
  simp [IsStationary]
  exact h_exists

/-- The unique stationary distribution of an irreducible stochastic matrix. -/
noncomputable def stationaryDistribution [DecidableEq n] (P : Matrix n n ℝ) (h_irred : Matrix.IsIrreducible P)
  (h_stoch : IsStochastic P) : stdSimplex ℝ n :=
  (Classical.choose (exists_unique_stationary_distribution_of_irreducible h_stoch h_irred).exists)

lemma stationaryDistribution_is_stationary [DecidableEq n] (P : Matrix n n ℝ) (h_irred : Matrix.IsIrreducible P)
  (h_stoch : IsStochastic P) :
  IsStationary P (stationaryDistribution P h_irred h_stoch) :=
  (Classical.choose_spec (exists_unique_stationary_distribution_of_irreducible h_stoch h_irred).exists)

/--
  If a transition matrix is stochastic,
  irreducible, and primitive, it defines a valid MCMC setup targeting its unique
  stationary distribution (which is guaranteed to exist by the PF theorem).
-/
theorem isMCMC_of_properties
    (P : Matrix n n ℝ) [DecidableEq n]
    (h_stoch : IsStochastic P)
    (h_irred : Matrix.IsIrreducible P)
    (h_prim : IsPrimitive P) :
    IsMCMC P (stationaryDistribution P h_irred h_stoch) :=
{
  stochastic := h_stoch,
  stationary := stationaryDistribution_is_stationary P h_irred h_stoch,
  irreducible := h_irred,
  primitive := h_prim
}

omit [Nonempty n] in
/-- Convenience: aperiodicity follows from primitivity  -/
theorem aperiodic_of_properties
    [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ)
    (h_stoch : IsStochastic P)
    (h_prim : IsPrimitive P) :
    Matrix.IsAperiodic P :=
  Matrix.primitive_implies_irreducible_and_aperiodic (A := P) h_stoch.1 h_prim

omit [Nonempty n] in
/-- Convenience: expose aperiodicity from an IsMCMC instance. -/
lemma IsMCMC.aperiodic
    [DecidableEq n] [Nonempty n]
    {P : Matrix n n ℝ} {π : stdSimplex ℝ n}
    (h : IsMCMC P π) : Matrix.IsAperiodic P :=
  Matrix.primitive_implies_irreducible_and_aperiodic (A := P) h.stochastic.1 h.primitive

end MCMC.Finite
