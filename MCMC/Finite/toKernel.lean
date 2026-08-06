import MCMC.Finite.MetropolisHastings
import Mathlib.Probability.Kernel.Invariance

set_option maxHeartbeats 0
namespace MCMC.Finite

open ProbabilityTheory MeasureTheory Matrix Kernel Mathlib
open scoped Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n]

/-- Convert a stochastic matrix to a Markov kernel on finite types -/
noncomputable def matrixToKernel (P : Matrix n n ℝ) (_ : IsStochastic P) :
    Kernel n n :=
  -- Build kernel rows as sums of (nonnegative) weights times Dirac measures.
  let rowMeasure : n → Measure n :=
    fun i => ∑ j : n, (ENNReal.ofReal (P i j)) • Measure.dirac j
  ProbabilityTheory.Kernel.ofFunOfCountable rowMeasure

/-- Convert a probability vector to a probability measure on finite types -/
noncomputable def vecToMeasure (π : stdSimplex ℝ n) : Measure n :=
  ∑ i : n, (ENNReal.ofReal (π.val i)) • Measure.dirac i

omit [DecidableEq n] in
private lemma kernel_eval_on_set
    {P : Matrix n n ℝ} (hP : IsStochastic P) (i : n)
    (B : Set n) (hB : MeasurableSet B) :
    (matrixToKernel P hP) i B
      = ∑ j : n, ENNReal.ofReal (P i j) * B.indicator 1 j := by
  change ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) B = _
  simp [hB, Measure.dirac_apply']

omit [DecidableEq n] in
private lemma kernel_eval_singleton
    {P : Matrix n n ℝ} (hP : IsStochastic P) (i j : n) :
    (matrixToKernel P hP) i {j} = ENNReal.ofReal (P i j) := by
  have hB : MeasurableSet ({j} : Set n) := measurableSet_singleton j
  rw [kernel_eval_on_set (P := P) (hP := hP) (i := i) ({j}) hB]
  rw [Finset.sum_eq_single j]
  · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
  · intro b _ hb
    simp [Set.indicator_of_notMem, hb]
  · simp

open scoped ENNReal

omit [DecidableEq n] in
/-- Matrix stationarity is equivalent to kernel invariance -/
theorem isStationary_iff_invariant (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
  (hP : IsStochastic P) :
  IsStationary P π ↔
  Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) := by
  set κ := matrixToKernel P hP
  set μ := vecToMeasure (n := n) π
  constructor
  · -- (→) Stationarity ⇒ Invariance
    intro hstat
    ext s hs
    have hL0 :
        (μ.bind κ) s = ∑ i : n, ENNReal.ofReal (π.val i) * κ i s := by
      simp [μ, vecToMeasure, Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_dirac]
    have hk :
        ∀ i, κ i s = ∑ j : n, ENNReal.ofReal (P i j) * s.indicator 1 j := by
      intro i
      change ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) s
              = ∑ j : n, ENNReal.ofReal (P i j) * s.indicator 1 j
      simp [hs, Measure.dirac_apply']
    have hL1 :
        (μ.bind κ) s
          = ∑ i : n, ∑ j : n,
              ENNReal.ofReal (π.val i) *
                (ENNReal.ofReal (P i j) * s.indicator 1 j) := by
      simp [hL0, hk, Finset.mul_sum, mul_left_comm]
    have hswap :
        ∑ i : n, ∑ j : n,
            ENNReal.ofReal (π.val i) *
              (ENNReal.ofReal (P i j) * s.indicator 1 j)
          = ∑ j : n, ∑ i : n,
              ENNReal.ofReal (π.val i) *
                (ENNReal.ofReal (P i j) * s.indicator 1 j) := by
      simpa using
        (Finset.sum_comm
          (s := (Finset.univ : Finset n))
          (t := (Finset.univ : Finset n))
          (f := fun i j =>
            ENNReal.ofReal (π.val i) *
              (ENNReal.ofReal (P i j) * s.indicator 1 j)))
    have hLHS :
        (μ.bind κ) s
          = ∑ j : n, (∑ i : n,
                ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)) *
              s.indicator 1 j := by
      calc
        (μ.bind κ) s
            = ∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val i) *
                  (ENNReal.ofReal (P i j) * s.indicator 1 j) := hL1
        _ = ∑ j : n, ∑ i : n,
                ENNReal.ofReal (π.val i) *
                  (ENNReal.ofReal (P i j) * s.indicator 1 j) := hswap
        _ = ∑ j : n,
                (∑ i : n,
                  ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j))
                * s.indicator 1 j := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa [mul_left_comm, mul_assoc] using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset n))
                  (f := fun i => ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j))
                  (a := s.indicator 1 j)).symm
    have hRHS :
        μ s = ∑ j : n, ENNReal.ofReal (π.val j) * s.indicator 1 j := by
      simp [μ, vecToMeasure, hs, Measure.dirac_apply']
    have hπ_nonneg : ∀ i, 0 ≤ π.val i := π.property.1
    have hP_nonneg : ∀ i j, 0 ≤ P i j := hP.1
    have hcoord : ∀ j, ∑ i, ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
                        = ENNReal.ofReal (π.val j) := by
      intro j
      have hL :
          (∑ i, ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j))
            = ∑ i, ENNReal.ofReal (π.val i * P i j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hPij := hP_nonneg i j
        have hπi := hπ_nonneg i
        simp [ENNReal.ofReal_mul, mul_comm, hPij]
      have hsum_ofReal :
          ∑ i, ENNReal.ofReal (π.val i * P i j)
            = ENNReal.ofReal (∑ i, π.val i * P i j) := by
        have hnn : ∀ i ∈ (Finset.univ : Finset n), 0 ≤ π.val i * P i j := by
          intro i _
          exact mul_nonneg (hπ_nonneg i) (hP_nonneg i j)
        simpa using (ENNReal.ofReal_sum_of_nonneg
          (s := (Finset.univ : Finset n))
          (f := fun i => π.val i * P i j) hnn).symm
      have hstat_j : ∑ i, π.val i * P i j = π.val j := by
        have := congrArg (fun v => v j) hstat
        simpa [IsStationary, Matrix.mulVec, dotProduct, Matrix.transpose,
               Matrix.transpose_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
          using this
      simpa [hL, hsum_ofReal] using congrArg ENNReal.ofReal hstat_j
    have : (μ.bind κ) s
            = ∑ j : n, ENNReal.ofReal (π.val j) * s.indicator 1 j := by
      rw [hLHS]
      simp only [hcoord]
    simpa [hRHS] using this
  · -- (←) Invariance ⇒ Stationarity
    intro hinv
    have k_singleton : ∀ i j, κ i {j} = ENNReal.ofReal (P i j) := by
      intro i j
      exact kernel_eval_singleton hP i j
    have mu_singleton : ∀ j, μ {j} = ENNReal.ofReal (π.val j) := by
      intro j
      have hmeas : MeasurableSet ({j} : Set n) := measurableSet_singleton j
      simp [μ, vecToMeasure, hmeas, Measure.dirac_apply']
      rw [Finset.sum_eq_single j]
      · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
      · intro x _ hx
        simp [Set.indicator_of_notMem, hx]
      · simp
    have hpoint : ∀ j, ∑ i, ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
                        = ENNReal.ofReal (π.val j) := by
      intro j
      have hmeas : MeasurableSet ({j} : Set n) := measurableSet_singleton j
      have hbind :
          (μ.bind κ) {j} = ∑ i : n, ENNReal.ofReal (π.val i) * κ i {j} := by
        simp [μ, vecToMeasure, Measure.bind_apply hmeas (Kernel.aemeasurable _),
              lintegral_dirac]
      have := congrArg (fun m => m {j}) hinv
      simpa [hbind, k_singleton, mu_singleton] using this
    have hcoord : ∀ j, (∑ i, P i j * π.val i) = π.val j := by
      intro j
      have hπ_nonneg : ∀ i, 0 ≤ π.val i := π.property.1
      have hP_nonneg : ∀ i, 0 ≤ P i j := fun i => hP.1 i j
      have hL :
          (∑ i, ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j))
            = ∑ i, ENNReal.ofReal (π.val i * P i j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [ENNReal.ofReal_mul, hP_nonneg i, mul_comm]
      have hsum_ofReal :
          ∑ i, ENNReal.ofReal (π.val i * P i j)
            = ENNReal.ofReal (∑ i, π.val i * P i j) := by
        have hnn : ∀ i ∈ (Finset.univ : Finset n), 0 ≤ π.val i * P i j := by
          intro i _
          exact mul_nonneg (hπ_nonneg i) (hP_nonneg i)
        simpa using (ENNReal.ofReal_sum_of_nonneg
          (s := (Finset.univ : Finset n))
          (f := fun i => π.val i * P i j) hnn).symm
      have := hpoint j
      have : ENNReal.ofReal (∑ i, π.val i * P i j) = ENNReal.ofReal (π.val j) := by
        simpa [hL, hsum_ofReal] using this
      have h_sum_nonneg : 0 ≤ ∑ i, π.val i * P i j := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (hπ_nonneg i) (hP_nonneg i)
      have h_π_nonneg_j : 0 ≤ π.val j := hπ_nonneg j
      have : ∑ i, π.val i * P i j = π.val j :=
        Eq.symm
          ((fun {p q} hp hq ↦ (ENNReal.ofReal_eq_ofReal_iff hp hq).mp) (hπ_nonneg j) h_sum_nonneg
            (id (Eq.symm this)))
      simpa [mul_comm (π.val _) (P _ j)] using this
    ext j
    simpa [IsStationary, Matrix.mulVec, dotProduct, Matrix.transpose,
           Matrix.transpose_apply] using hcoord j

/-- Matrix reversibility is equivalent to kernel reversibility -/
theorem isReversible_iff_kernel_reversible (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (hP : IsStochastic P) :
    IsReversible P π ↔
    Kernel.IsReversible (matrixToKernel P hP) (vecToMeasure π) := by
  set κ := matrixToKernel P hP
  set μ := vecToMeasure (n := n) π
  constructor
  · -- (→) Matrix detailed balance ⇒ Kernel reversibility
    intro hrev A B hA hB
    have k_on_set :
        ∀ i, κ i B = ∑ j : n, ENNReal.ofReal (P i j) * B.indicator 1 j := by
      intro i
      exact kernel_eval_on_set hP i B hB
    have hL0' :
        ∫⁻ x, (A.indicator (fun x => κ x B)) x ∂μ
          = ∑ i : n, ENNReal.ofReal (π.val i) *
                (A.indicator (fun x => κ x B) i) := by
      simp [μ, vecToMeasure]
    have hL0 :
        ∫⁻ x in A, κ x B ∂μ
          = ∑ i : n, ENNReal.ofReal (π.val i) *
                (A.indicator (fun x => κ x B) i) := by
      simpa [lintegral_indicator (μ := μ) (s := A) (f := fun x => κ x B) hA] using hL0'
    have hind :
        ∀ i, A.indicator (fun x => κ x B) i = κ i B * A.indicator 1 i := by
      intro i
      by_cases hi : i ∈ A
      · simp [Set.indicator_of_mem, hi, mul_comm]
      · simp [Set.indicator_of_notMem, hi]
    have hL1 :
        ∫⁻ x in A, κ x B ∂μ
          = ∑ i : n, ENNReal.ofReal (π.val i) * κ i B * A.indicator 1 i := by
      simpa [hind, mul_comm, mul_left_comm, mul_assoc] using hL0
    have hL2 :
        ∫⁻ x in A, κ x B ∂μ
          = ∑ i : n, ∑ j : n,
              ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
                * A.indicator 1 i * B.indicator 1 j := by
      have hstep1 :
          (∑ i : n, ENNReal.ofReal (π.val i) * κ i B * A.indicator 1 i)
            = ∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val i) *
                  (ENNReal.ofReal (P i j) * B.indicator 1 j) *
                  A.indicator 1 i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        calc
          ENNReal.ofReal (π.val i) * κ i B * A.indicator 1 i
              = (ENNReal.ofReal (π.val i) * A.indicator 1 i) * κ i B := by
                ac_rfl
          _ = (ENNReal.ofReal (π.val i) * A.indicator 1 i)
                * ∑ j : n, ENNReal.ofReal (P i j) * B.indicator 1 j := by
                simp [k_on_set i]
          _ = ∑ j : n,
                (ENNReal.ofReal (π.val i) * A.indicator 1 i)
                  * (ENNReal.ofReal (P i j) * B.indicator 1 j) := by
                simp [Finset.mul_sum]
          _ = ∑ j : n,
                ENNReal.ofReal (π.val i)
                  * (ENNReal.ofReal (P i j) * B.indicator 1 j)
                  * A.indicator 1 i := by
                refine Finset.sum_congr rfl (fun j _ => ?_)
                simp [mul_comm, mul_left_comm, mul_assoc]
      have hstep2 :
          (∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val i) *
                  (ENNReal.ofReal (P i j) * B.indicator 1 j) *
                  A.indicator 1 i)
            = ∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
                  * A.indicator 1 i * B.indicator 1 j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp [mul_comm, mul_left_comm, mul_assoc]
      simpa [hL1] using hstep1.trans hstep2
    have hR0' :
        ∫⁻ x, (B.indicator (fun x => κ x A)) x ∂μ
          = ∑ j : n, ENNReal.ofReal (π.val j) * (B.indicator (fun x => κ x A) j) := by
      simp [μ, vecToMeasure]
    have hR0 :
        ∫⁻ x in B, κ x A ∂μ
          = ∑ j : n, ENNReal.ofReal (π.val j) * (B.indicator (fun x => κ x A) j) := by
      simpa [lintegral_indicator (μ := μ) (s := B) (f := fun x => κ x A) hB] using hR0'
    have hind' :
        ∀ j, B.indicator (fun x => κ x A) j = κ j A * B.indicator 1 j := by
      intro j
      by_cases hj : j ∈ B
      · simp [Set.indicator_of_mem, hj, mul_comm]
      · simp [Set.indicator_of_notMem, hj]
    have hR0'' :
        ∫⁻ x in B, κ x A ∂μ
          = ∑ j : n, ENNReal.ofReal (π.val j) * κ j A * B.indicator 1 j := by
      simpa [hind', mul_comm, mul_left_comm, mul_assoc] using hR0
    have k_on_set' :
        ∀ j, κ j A = ∑ i : n, ENNReal.ofReal (P j i) * A.indicator 1 i := by
      intro j
      exact kernel_eval_on_set hP j A hA
    have hR1 :
        ∫⁻ x in B, κ x A ∂μ
          = ∑ j : n, ∑ i : n,
              ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                * B.indicator 1 j * A.indicator 1 i := by
      have hstep1 :
          (∑ j : n, ENNReal.ofReal (π.val j) * κ j A * B.indicator 1 j)
            = ∑ j : n, ∑ i : n,
                ENNReal.ofReal (π.val j) *
                  (ENNReal.ofReal (P j i) * A.indicator 1 i) *
                  B.indicator 1 j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        calc
          ENNReal.ofReal (π.val j) * κ j A * B.indicator 1 j
              = (ENNReal.ofReal (π.val j) * B.indicator 1 j) * κ j A := by
                ac_rfl
          _ = (ENNReal.ofReal (π.val j) * B.indicator 1 j)
                * ∑ i : n, ENNReal.ofReal (P j i) * A.indicator 1 i := by
                simp [k_on_set' j]
          _ = ∑ i : n,
                (ENNReal.ofReal (π.val j) * B.indicator 1 j)
                  * (ENNReal.ofReal (P j i) * A.indicator 1 i) := by
                simp [Finset.mul_sum]
          _ = ∑ i : n,
                ENNReal.ofReal (π.val j)
                  * (ENNReal.ofReal (P j i) * A.indicator 1 i)
                  * B.indicator 1 j := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                simp [mul_comm, mul_left_comm, mul_assoc]
      have hstep2 :
          (∑ j : n, ∑ i : n,
                ENNReal.ofReal (π.val j) *
                  (ENNReal.ofReal (P j i) * A.indicator 1 i) *
                  B.indicator 1 j)
            = ∑ j : n, ∑ i : n,
                ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                  * B.indicator 1 j * A.indicator 1 i := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [mul_comm, mul_left_comm, mul_assoc]
      rw [hR0'', hstep1, hstep2]
    have hR2 :
        ∫⁻ x in B, κ x A ∂μ
          = ∑ i : n, ∑ j : n,
              ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                * A.indicator 1 i * B.indicator 1 j := by
      calc
        ∫⁻ x in B, κ x A ∂μ
            = ∑ j : n, ∑ i : n,
                ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                  * B.indicator 1 j * A.indicator 1 i := hR1
        _ = ∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                  * B.indicator 1 j * A.indicator 1 i := by
              exact
                (Finset.sum_comm
                  (s := (Finset.univ : Finset n))
                  (t := (Finset.univ : Finset n))
                  (f := fun j i =>
                    ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                      * B.indicator 1 j * A.indicator 1 i))
        _ = ∑ i : n, ∑ j : n,
                ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i)
                  * A.indicator 1 i * B.indicator 1 j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simp [mul_comm, mul_left_comm, mul_assoc]
    have hπ_nonneg : ∀ i, 0 ≤ π.val i := π.property.1
    have hP_nonneg : ∀ i j, 0 ≤ P i j := hP.1
    have hcoeff :
        ∀ i j,
          ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
            = ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i) := by
      intro i j
      simpa [ENNReal.ofReal_mul, hπ_nonneg _, hP_nonneg _ _, mul_comm, mul_left_comm, mul_assoc]
        using congrArg ENNReal.ofReal (hrev i j)
    have : ∫⁻ x in A, κ x B ∂μ
            = ∫⁻ x in B, κ x A ∂μ := by
      rw [hL2, hR2]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hcoeff i j]
    exact this
  · -- (←) Kernel reversibility ⇒ Matrix detailed balance on entries
    intro hker
    have k_singleton : ∀ i j, κ i {j} = ENNReal.ofReal (P i j) := by
      intro i j
      exact kernel_eval_singleton hP i j
    intro i j
    have hAi : MeasurableSet ({i} : Set n) := measurableSet_singleton i
    have hBj : MeasurableSet ({j} : Set n) := measurableSet_singleton j
    have hsingle := hker hAi hBj
    have hL :
        ∫⁻ x in ({i} : Set n), κ x {j} ∂μ
          = ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j) := by
      classical
      have hInt :
          ∫⁻ x in ({i} : Set n), κ x {j} ∂μ
            = ∑ k : n, ENNReal.ofReal (π.val k) *
                (({i} : Set n).indicator (fun x => κ x {j}) k) := by
        simp [μ, vecToMeasure]
        ring_nf
        simp [Set.indicator_apply]
      have hsum :
          ∑ k : n, ENNReal.ofReal (π.val k) *
              (({i} : Set n).indicator (fun x => κ x {j}) k)
            = ENNReal.ofReal (π.val i) * κ i {j} := by
        rw [Finset.sum_eq_single i]
        · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
        · intro x _ hx
          simp [Set.indicator_of_notMem, hx]
        · simp
      rw [hInt, hsum, k_singleton i j]
    have hR :
        ∫⁻ x in ({j} : Set n), κ x {i} ∂μ
          = ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i) := by
      classical
      have hInt :
          ∫⁻ x in ({j} : Set n), κ x {i} ∂μ
            = ∑ k : n, ENNReal.ofReal (π.val k) *
                (({j} : Set n).indicator (fun x => κ x {i}) k) := by
        simp [μ, vecToMeasure]
        ring_nf
        simp [Set.indicator_apply]
      have hsum :
          ∑ k : n, ENNReal.ofReal (π.val k) *
              (({j} : Set n).indicator (fun x => κ x {i}) k)
            = ENNReal.ofReal (π.val j) * κ j {i} := by
        rw [Finset.sum_eq_single j]
        · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
        · intro k _ hki
          have : k ∉ ({j} : Set n) := by simpa [Set.mem_singleton_iff] using hki
          simp [Set.indicator_of_notMem, this]
        · simp
      rw [hInt, hsum, k_singleton j i]
    have hπ_nonneg : ∀ x, 0 ≤ π.val x := π.property.1
    have hP_nonneg : ∀ x y, 0 ≤ P x y := hP.1
    have hENN :
        ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j)
          = ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i) := by
      rw [← hL, ← hR]
      exact hsingle
    have hreal :
        π.val i * P i j = π.val j * P j i := by
      have h₁ :
          ENNReal.ofReal (π.val i * P i j)
            = ENNReal.ofReal (π.val i) * ENNReal.ofReal (P i j) := by
        simp [ENNReal.ofReal_mul, hP_nonneg i j, mul_comm]
      have h₂ :
          ENNReal.ofReal (π.val j * P j i)
            = ENNReal.ofReal (π.val j) * ENNReal.ofReal (P j i) := by
        simp [ENNReal.ofReal_mul, hP_nonneg j i, mul_comm]
      have : ENNReal.ofReal (π.val i * P i j)
                = ENNReal.ofReal (π.val j * P j i) := by
        simpa [h₁, h₂] using hENN
      have hL_nonneg : 0 ≤ π.val i * P i j :=
        mul_nonneg (hπ_nonneg i) (hP_nonneg i j)
      have hR_nonneg : 0 ≤ π.val j * P j i :=
        mul_nonneg (hπ_nonneg j) (hP_nonneg j i)
      exact (ENNReal.ofReal_eq_ofReal_iff hL_nonneg hR_nonneg).mp this
    exact hreal

/-! A Markov-kernel instance for the matrix-induced kernel -/
instance matrixToKernel_isMarkov (P : Matrix n n ℝ) (hP : IsStochastic P) :
    IsMarkovKernel (matrixToKernel P hP) := by
  classical
  constructor
  intro i
  refine ⟨?_⟩
  change
    ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) Set.univ = 1
  have hsum_univ :
      ((∑ j : n, ENNReal.ofReal (P i j) • Measure.dirac j) : Measure n) Set.univ
        = ∑ j : n, ENNReal.ofReal (P i j) := by
    simp
  have hsum_ofReal :
      ∑ j : n, ENNReal.ofReal (P i j) = ENNReal.ofReal (∑ j, P i j) := by
    have hnn : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ P i j := by
      intro j _; exact hP.1 i j
    simpa using
      (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset n))
        (f := fun j => P i j) hnn).symm
  simp [hsum_univ, hsum_ofReal, hP.2 i]

theorem IsReversible.is_stationary' {P : Matrix n n ℝ} {π : stdSimplex ℝ n}
    (hP : IsStochastic P) (h_rev : IsReversible P π) :
    IsStationary P π := by
  rw [isStationary_iff_invariant P π hP]
  rw [isReversible_iff_kernel_reversible P π hP] at h_rev
  haveI : IsMarkovKernel (matrixToKernel P hP) := matrixToKernel_isMarkov P hP
  exact h_rev.invariant


end MCMC.Finite
