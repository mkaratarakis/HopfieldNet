import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Stochastic
import MCMC.Finite.Convergence
import NeuralNetwork.NeuralNetwork.HopfieldBoltzmannR

/-!
# Ergodicity via PF for `HasToReal`-models (row-stochastic form)

This is the `R`-generic proof-layer analogue of `Ergodicity.lean`, but phrased for the
**row-stochastic** matrix `HopfieldBoltzmannR.randomScanMatrix`.

Key point: even if the model energy lives in an abstract scalar `R`, as long as we have
`HasToReal R` we obtain a concrete `ℝ`-valued transition matrix, so Perron–Frobenius /
`MCMC.Finite` results apply unchanged.
-/

namespace NeuralNetwork

set_option linter.unusedSectionVars false

open scoped ENNReal
open TwoState HopfieldBoltzmannR Matrix
open scoped BigOperators
open Filter Topology

section

variable {R : Type} {U : Type} {σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

variable (NN : NeuralNetwork R U σ)
variable [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [DecidableEq σ]
variable [TwoState.TwoStateExclusiveR (NN := NN)]
variable [HasToReal R]

variable (p : Params NN) (T : Temperature)

local notation "f" => (HasToReal.toRealRingHom (R := R))

noncomputable def A : Matrix NN.State NN.State ℝ :=
  HopfieldBoltzmannR.randomScanMatrix NN p T f

/-- Sites (as a Finset) where two states differ. -/
noncomputable def diffSites (s s' : NN.State) : Finset U :=
  (Finset.univ.filter (fun u : U => s.act u ≠ s'.act u))

lemma diffSites_card_zero {s s' : NN.State} :
    (diffSites (NN := NN) s s').card = 0 → s = s' := by
  intro h0
  ext u
  by_contra hneq
  have : u ∈ diffSites (NN := NN) s s' := by
    simp [diffSites, hneq]
  have hpos : 0 < (diffSites (NN := NN) s s').card :=
    Finset.card_pos.mpr ⟨u, this⟩
  simp [h0] at hpos

/--
One-step “towards-target” flip: picking a differing site reduces the number of differences.

Given `u ∈ diffSites s s'`, build `s₁` that differs from `s` only at `u` (by setting it to `s'.act u`),
so that the number of differing sites to `s'` drops by exactly one.
-/
lemma exists_single_flip_reduce
    {s s' : NN.State} {u : U}
    (hu : u ∈ diffSites (NN := NN) s s') :
    ∃ s₁ : NN.State,
      HopfieldBoltzmannR.DiffOnly (NN := NN) u s₁ s ∧
      (diffSites (NN := NN) s₁ s').card + 1 = (diffSites (NN := NN) s s').card := by
  -- The site really differs
  have hneq : s.act u ≠ s'.act u := by
    simp [diffSites] at hu; exact hu
  -- Classify `s'.act u` (two-state exclusive)
  rcases (TwoState.TwoStateExclusiveR.pact_iff (NN := NN) (a := s'.act u)).1 (s'.hp u) with hpos | hneg
  · -- Target value is σ_pos: use updPos
    refine ⟨updPos (NN := NN) s u, ?_, ?_⟩
    · refine And.intro ?hcoord ?hdiffu
      · intro v hv
        simp [updPos, Function.update, hv]
      · intro hcontra
        have hup : (updPos (NN := NN) s u).act u = TwoStateNeuralNetwork.σ_pos (NN := NN) := by
          simp [updPos]
        have : s.act u = s'.act u := by
          simpa [hpos, hup] using hcontra.symm
        exact hneq this
    · have hset :
          diffSites (NN := NN) (updPos (NN := NN) s u) s'
            = (diffSites (NN := NN) s s').erase u := by
        ext v
        by_cases hvu : v = u
        · subst hvu
          simp [diffSites, updPos, Function.update, hpos]
        · simp [diffSites, updPos, Function.update, hvu]
      have hmem : u ∈ diffSites (NN := NN) s s' := hu
      have hcount :
          (diffSites (NN := NN) (updPos (NN := NN) s u) s').card
            = (diffSites (NN := NN) s s').card - 1 := by
        simpa [hset] using Finset.card_erase_of_mem hmem
      have hposCard : 0 < (diffSites (NN := NN) s s').card :=
        Finset.card_pos.mpr ⟨u, hu⟩
      have hge : 1 ≤ (diffSites (NN := NN) s s').card :=
        Nat.succ_le_of_lt hposCard
      have :
          (diffSites (NN := NN) (updPos (NN := NN) s u) s').card + 1
            = (diffSites (NN := NN) s s').card := by
        have := Nat.sub_add_cancel hge
        simpa [hcount] using this
      simpa using this
  · -- Target value is σ_neg: use updNeg
    refine ⟨updNeg (NN := NN) s u, ?_, ?_⟩
    · refine And.intro
        (by
          intro v hv
          simp [updNeg, Function.update, hv])
        (by
          intro hcontra
          have hup : (updNeg (NN := NN) s u).act u = TwoStateNeuralNetwork.σ_neg (NN := NN) := by
            simp [updNeg]
          have : s.act u = s'.act u := by
            simpa [hneg, hup] using hcontra.symm
          exact hneq this)
    · have hset :
          diffSites (NN := NN) (updNeg (NN := NN) s u) s'
            = (diffSites (NN := NN) s s').erase u := by
        ext v
        by_cases hvu : v = u
        · subst hvu
          simp [diffSites, updNeg, Function.update, hneg]
        · simp [diffSites, updNeg, Function.update, hvu]
      have hmem : u ∈ diffSites (NN := NN) s s' := hu
      have hcount :
          (diffSites (NN := NN) (updNeg (NN := NN) s u) s').card
            = (diffSites (NN := NN) s s').card - 1 := by
        simpa [hset] using Finset.card_erase_of_mem hmem
      have hposCard : 0 < (diffSites (NN := NN) s s').card :=
        Finset.card_pos.mpr ⟨u, hu⟩
      have hge : 1 ≤ (diffSites (NN := NN) s s').card :=
        Nat.succ_le_of_lt hposCard
      have :
          (diffSites (NN := NN) (updNeg (NN := NN) s u) s').card + 1
            = (diffSites (NN := NN) s s').card := by
        have := Nat.sub_add_cancel hge
        simpa [hcount] using this
      simpa using this

lemma A_nonneg : ∀ i j : NN.State, 0 ≤ (A (NN := NN) (p := p) (T := T)) i j := by
  intro i j
  -- entries are `ENNReal.toReal` of a PMF value
  dsimp [A, HopfieldBoltzmannR.randomScanMatrix, PMFMatrix.pmfToMatrix]
  exact ENNReal.toReal_nonneg

/-- Nonnegativity of all powers of `A`. -/
lemma A_pow_nonneg :
    ∀ n (i j : NN.State), 0 ≤ ((A (NN := NN) (p := p) (T := T)) ^ n) i j := by
  intro n; induction' n with n ih <;> intro i j
  · by_cases h : i = j
    · subst h; simp [pow_zero]
    · simp [pow_zero, h]
  · have hmul :
        ((A (NN := NN) (p := p) (T := T)) ^ (Nat.succ n)) i j
          = ∑ k, ((A (NN := NN) (p := p) (T := T)) ^ n) i k *
                  (A (NN := NN) (p := p) (T := T)) k j := by
      simp [pow_succ, Matrix.mul_apply]
    have hterm :
        ∀ k, 0 ≤ ((A (NN := NN) (p := p) (T := T)) ^ n) i k *
               (A (NN := NN) (p := p) (T := T)) k j := by
      intro k
      exact mul_nonneg (ih i k) (A_nonneg (NN := NN) (p := p) (T := T) k j)
    have hsum : 0 ≤ ∑ k, ((A (NN := NN) (p := p) (T := T)) ^ n) i k *
                          (A (NN := NN) (p := p) (T := T)) k j :=
      Finset.sum_nonneg (fun k _ => hterm k)
    simpa [hmul] using hsum

/-- Existence of a positive entry in some power between any two states. -/
lemma A_exists_positive_power (s s' : NN.State) :
    ∃ n : ℕ, 0 < ((A (NN := NN) (p := p) (T := T)) ^ n) s s' := by
  set A0 := (A (NN := NN) (p := p) (T := T))
  have hPow := A_pow_nonneg (NN := NN) (p := p) (T := T)
  have main :
      ∀ k, ∀ s s' : NN.State,
        (diffSites (NN := NN) s s').card = k →
        ∃ n, 0 < (A0 ^ n) s s' := by
    refine Nat.rec ?base ?step
    · intro s s' hcard
      have hs_eq : s = s' := diffSites_card_zero (NN := NN) (s:=s) (s':=s') hcard
      subst hs_eq
      refine ⟨0, ?_⟩
      simp [A0]
    · intro k IH s s' hcard
      have hpos : 0 < (diffSites (NN := NN) s s').card := by
        simpa [hcard] using Nat.succ_pos k
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨s₁, hDiffOnly, hreduce⟩ :=
        exists_single_flip_reduce (NN := NN) hu
      have hcard_s₁ :
          (diffSites (NN := NN) s₁ s').card = k := by
        have h1 :
            (diffSites (NN := NN) s₁ s').card + 1 = Nat.succ k := by
          simpa [hcard] using hreduce
        exact Nat.succ.inj h1
      -- one-step positivity: A0 s s₁ > 0
      have h_step : 0 < A0 s s₁ := by
        -- Let elaboration infer `s` and `s'` from `hDiffOnly : DiffOnly u s₁ s`.
        have h := HopfieldBoltzmannR.randomScanMatrix_pos_of_diffOnly NN p T f hDiffOnly
        simpa [A0, A] using h
      obtain ⟨n, hn_pos⟩ := IH s₁ s' hcard_s₁
      refine ⟨n.succ, ?_⟩
      have hsum :
          (A0 ^ (Nat.succ n)) s s'
            = ∑ j, A0 s j * (A0 ^ n) j s' := by
        -- we want the *left* multiplication form: `A^(n+1) = A * A^n`
        simp [pow_succ', Matrix.mul_apply]
      have hchosen : 0 < A0 s s₁ * (A0 ^ n) s₁ s' := mul_pos h_step hn_pos
      have hterm_nonneg :
          ∀ j, 0 ≤ A0 s j * (A0 ^ n) j s' := by
        intro j
        exact mul_nonneg (A_nonneg (NN := NN) (p := p) (T := T) s j) (hPow n j s')
      have hge :
          A0 s s₁ * (A0 ^ n) s₁ s'
            ≤ ∑ j, A0 s j * (A0 ^ n) j s' := by
        have hnonneg :
          ∀ j ∈ (Finset.univ : Finset NN.State), 0 ≤ A0 s j * (A0 ^ n) j s' := by
          intro j _; exact hterm_nonneg j
        have hmem : s₁ ∈ (Finset.univ : Finset NN.State) := by simp
        simpa [mul_comm, mul_left_comm, mul_assoc] using (Finset.single_le_sum hnonneg hmem)
      have hsum_pos :
          0 < ∑ j, A0 s j * (A0 ^ n) j s' :=
        lt_of_lt_of_le hchosen hge
      simpa [hsum] using hsum_pos
  exact main (diffSites (NN := NN) s s').card s s' rfl

lemma A_irreducible : Matrix.IsIrreducible (A (NN := NN) (p := p) (T := T)) := by
  set A0 := (A (NN := NN) (p := p) (T := T))
  letI : Quiver NN.State := Matrix.toQuiver A0
  refine ⟨A_nonneg (NN := NN) (p := p) (T := T), ?_⟩
  intro s s'
  obtain ⟨n, hpos⟩ := A_exists_positive_power (NN := NN) (p := p) (T := T) s s'
  by_cases hzero : n = 0
  · subst hzero
    have hs_eq : s = s' := by
      have h := hpos
      simp [pow_zero] at h
      by_contra hne
      simp [hne] at h
    subst hs_eq
    have hdiag : 0 < A0 s s := by
      simpa [A0, A] using
        (HopfieldBoltzmannR.randomScanMatrix_diag_pos NN p T f s)
    exact (Matrix.path_exists_of_pos_entry (A := A0) (i := s) (j := s) hdiag)
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hzero
    have hA_nonneg : ∀ i j, 0 ≤ A0 i j := A_nonneg (NN := NN) (p := p) (T := T)
    have hpath :
        Nonempty {q : Quiver.Path s s' // q.length = n} := by
      simpa using
        (Matrix.pow_apply_pos_iff_nonempty_path (A := A0) (hA := hA_nonneg) n s s').1 hpos
    rcases hpath with ⟨⟨q, hq_len⟩⟩
    have hq_len_pos : q.length > 0 := by
      simpa [hq_len] using hn_pos
    exact ⟨q, hq_len_pos⟩

/-- PF uniqueness of the stationary distribution for the random-scan Gibbs matrix. -/
theorem randomScan_unique_stationary :
    ∃! (π : stdSimplex ℝ NN.State),
      MCMC.Finite.IsStationary (A (NN := NN) (p := p) (T := T)) π := by
  classical
  have h_irred : Matrix.IsIrreducible (A (NN := NN) (p := p) (T := T)) :=
    A_irreducible (NN := NN) (p := p) (T := T)
  exact HopfieldBoltzmannR.randomScan_exists_unique_stationary_distribution_of_irreducible
    NN p T f h_irred

/-- Positive diagonal (aperiodicity): self-loop probability is strictly positive. -/
lemma A_diag_pos : ∀ s : NN.State, 0 < (A (NN := NN) (p := p) (T := T)) s s := by
  intro s
  -- this is a purely probabilistic fact about one-site Gibbs updates
  simpa [A] using
    (HopfieldBoltzmannR.randomScanMatrix_diag_pos NN p T f s)

/-- Primitivity: irreducible + positive diagonal implies some power has all entries positive. -/
theorem A_primitive : Matrix.IsPrimitive (A (NN := NN) (p := p) (T := T)) := by
  classical
  exact
    Matrix.IsPrimitive.of_irreducible_pos_diagonal
      (A := (A (NN := NN) (p := p) (T := T)))
      (hA_nonneg := A_nonneg (NN := NN) (p := p) (T := T))
      (hA_irred := A_irreducible (NN := NN) (p := p) (T := T))
      (hA_diag_pos := A_diag_pos (NN := NN) (p := p) (T := T))

/-!
## Convergence (finite Markov chain theory)

Now that we have:
- `IsStochastic A` (from the PMF construction),
- `IsIrreducible A` (PF connectivity),
- `IsPrimitive A` (irreducible + positive diagonal),

we can instantiate the general `MCMC.Finite` convergence theorem.
-/

noncomputable def πstationary : stdSimplex ℝ NN.State :=
  MCMC.Finite.stationaryDistribution
    (P := (A (NN := NN) (p := p) (T := T)))
    (h_irred := A_irreducible (NN := NN) (p := p) (T := T))
    (h_stoch := HopfieldBoltzmannR.randomScanMatrix_isStochastic (NN := NN) p T f)

theorem convergence_to_stationary_limit :
    Tendsto (fun k : ℕ => (A (NN := NN) (p := p) (T := T)) ^ k) atTop
      (𝓝 (MCMC.Finite.LimitMatrix (πstationary (NN := NN) (p := p) (T := T)))) := by
  classical
  let P : Matrix NN.State NN.State ℝ := (A (NN := NN) (p := p) (T := T))
  let π : stdSimplex ℝ NN.State := πstationary (NN := NN) (p := p) (T := T)
  have hMCMC : MCMC.Finite.IsMCMC P π :=
    MCMC.Finite.isMCMC_of_properties
      (P := P)
      (h_stoch := HopfieldBoltzmannR.randomScanMatrix_isStochastic (NN := NN) p T f)
      (h_irred := A_irreducible (NN := NN) (p := p) (T := T))
      (h_prim := A_primitive (NN := NN) (p := p) (T := T))
  simpa [P, π] using MCMC.Finite.convergence_to_stationarity P π hMCMC

theorem distribution_converges_to_stationary
    (μ₀ : stdSimplex ℝ NN.State) :
    Tendsto (MCMC.Finite.distributionAtTime (A (NN := NN) (p := p) (T := T)) μ₀)
      atTop (𝓝 (πstationary (NN := NN) (p := p) (T := T)).val) := by
  classical
  let P : Matrix NN.State NN.State ℝ := (A (NN := NN) (p := p) (T := T))
  let π : stdSimplex ℝ NN.State := πstationary (NN := NN) (p := p) (T := T)
  have hMCMC : MCMC.Finite.IsMCMC P π :=
    MCMC.Finite.isMCMC_of_properties
      (P := P)
      (h_stoch := HopfieldBoltzmannR.randomScanMatrix_isStochastic (NN := NN) p T f)
      (h_irred := A_irreducible (NN := NN) (p := p) (T := T))
      (h_prim := A_primitive (NN := NN) (p := p) (T := T))
  simpa [P, π] using MCMC.Finite.distribution_converges_to_stationarity P π hMCMC μ₀

end

end NeuralNetwork
