import NeuralNetwork.NeuralNetwork.TwoState
import NeuralNetwork.NeuralNetwork.TSAux
import NeuralNetwork.NeuralNetwork.ComputableRealsBridge
import NeuralNetwork.NeuralNetwork.PMFMatrix
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Hopfield/Boltzmann construction over a general scalar `R`

This module provides *finite-state* Boltzmann quantities (`CanonicalEnsemble`, Boltzmann
probability, and one-site Gibbs transition probabilities) for a neural network whose
energy is valued in an abstract scalar `R`.

The scalar `R` is linked to analysis/measure theory by a ring morphism
`toReal : R →+* ℝ` (via `NeuralNetwork.HasToReal`).

Design:
- **Proof layer** stays in `ℝ` (canonical ensemble, entropy, etc.).
- **Model layer** can use `R := Computable.CReal`, `R := CRealAQ Dyadic`, etc.
- This file assumes finite state space so measurability is trivial and the base measure is
  counting measure.
-/

namespace NeuralNetwork

open MeasureTheory
open scoped BigOperators Temperature CanonicalEnsemble

namespace HopfieldBoltzmannR

open CanonicalEnsemble ProbabilityTheory TwoState PMF
open scoped ENNReal NNReal

variable {R : Type} {U : Type} {σ : Type}

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

variable (NN : NeuralNetwork R U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN]
variable [HasToReal R]

variable (spec : TwoState.EnergySpec' (NN := NN))

-- For finite-state networks, use the trivial measurable space.
instance : MeasurableSpace NN.State := ⊤

-- With the trivial σ-algebra, every singleton is measurable.
instance : MeasurableSingletonClass NN.State := by
  classical
  refine ⟨?_⟩
  intro s
  -- `MeasurableSpace = ⊤` makes all sets measurable.
  trivial

@[simp] lemma measurable_of_fintype_state (f : NN.State → ℝ) : Measurable f := by
  unfold Measurable; intro s _; simp

/-- Energy as an `ℝ`-valued function, obtained by pushing `spec.E` through `toReal`. -/
def energyReal
    (NN : NeuralNetwork R U σ)
    [TwoStateNeuralNetwork NN]
    (spec : TwoState.EnergySpec' (NN := NN))
    (p : Params NN) : NN.State → ℝ :=
  fun s => (HasToReal.toRealRingHom (R := R)) (spec.E p s)

/-- Canonical ensemble induced by `spec.E`, interpreted in `ℝ`. -/
noncomputable def CEparams
    (NN : NeuralNetwork R U σ)
    [TwoStateNeuralNetwork NN]
    [Fintype NN.State]
    (spec : TwoState.EnergySpec' (NN := NN))
    (p : Params NN) : CanonicalEnsemble NN.State where
  energy := energyReal (NN := NN) (spec := spec) p
  dof := 0
  phaseSpaceunit := 1
  energy_measurable := by
    intro _
    simpa using (measurable_of_fintype_state (NN := NN)
      (f := energyReal (NN := NN) (spec := spec) p))
  μ := Measure.count
  μ_sigmaFinite := by
    classical
    -- Mathlib's `Measure.count` is σ-finite on countable types with measurable singletons.
    -- We derive `Countable` from `Fintype` explicitly (so we don't rely on a global instance).
    letI : Countable NN.State :=
      ⟨⟨fun s => (Fintype.equivFin NN.State s).val, by
        intro a b hab
        apply (Fintype.equivFin NN.State).injective
        -- `Fin.ext` turns equality of `val` into equality of `Fin`.
        exact Fin.ext hab⟩⟩
    letI : MeasurableSingletonClass NN.State := by infer_instance
    infer_instance

instance (p : Params NN) :
    CanonicalEnsemble.IsFinite (CEparams (NN := NN) (spec := spec) p) where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

/-- Boltzmann probability of state `s` at temperature `T`. -/
noncomputable def P (p : Params NN) (T : Temperature) (s : NN.State) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).probability T s

/-!
## One-site Gibbs transition probability in ℝ

Extracted from the discrete `PMF` kernel `TwoState.gibbsUpdate`.
-/

/-- One-site Gibbs transition probability, coerced to `ℝ` via `ENNReal.toReal`. -/
noncomputable def Kbm (p : Params NN) (T : Temperature) (f : R →+* ℝ)
    (u : U) (s s' : NN.State) : ℝ :=
  ((TwoState.gibbsUpdate (NN := NN) f p T s u) s').toReal

/-- The `ℝ`-matrix form of the one-site Gibbs kernel at site `u`. -/
noncomputable def KbmMatrix (p : Params NN) (T : Temperature) (f : R →+* ℝ) (u : U) :
    Matrix NN.State NN.State ℝ :=
  PMFMatrix.pmfToMatrix (κ := fun s : NN.State => TwoState.gibbsUpdate (NN := NN) f p T s u)

theorem KbmMatrix_isStochastic (p : Params NN) (T : Temperature) (f : R →+* ℝ) (u : U) :
    MCMC.Finite.IsStochastic (KbmMatrix (NN := NN) p T f u) := by
  classical
  simpa [KbmMatrix] using
    (PMFMatrix.pmfToMatrix_isStochastic (κ := fun s : NN.State => TwoState.gibbsUpdate (NN := NN) f p T s u))

/-- Random-scan (uniform-site) Gibbs update as a `PMF` on the next state. -/
noncomputable def randomScanPMF (p : Params NN) (T : Temperature) (f : R →+* ℝ) (s : NN.State) :
    PMF NN.State :=
  (PMF.uniformOfFintype U).bind (fun u => TwoState.gibbsUpdate (NN := NN) f p T s u)

/-- The `ℝ`-matrix form of the random-scan Gibbs kernel. -/
noncomputable def randomScanMatrix (p : Params NN) (T : Temperature) (f : R →+* ℝ) :
    Matrix NN.State NN.State ℝ :=
  PMFMatrix.pmfToMatrix (κ := randomScanPMF (NN := NN) (p := p) (T := T) f)

theorem randomScanMatrix_isStochastic (p : Params NN) (T : Temperature) (f : R →+* ℝ) :
    MCMC.Finite.IsStochastic (randomScanMatrix (NN := NN) p T f) := by
  classical
  simpa [randomScanMatrix] using
    (PMFMatrix.pmfToMatrix_isStochastic (κ := randomScanPMF (NN := NN) (p := p) (T := T) f))

/-!
### MCMC.Finite bridge (existence/uniqueness via PF)

`MCMC.Finite` gives uniqueness of a stationary distribution for **row-stochastic + irreducible**
matrices. We expose that API here for the random-scan Gibbs matrix.
-/

theorem randomScan_exists_unique_stationary_distribution_of_irreducible
    (p : Params NN) (T : Temperature) (f : R →+* ℝ)
    (h_irred : Matrix.IsIrreducible (randomScanMatrix (NN := NN) p T f)) :
    ∃! (π : stdSimplex ℝ NN.State),
      MCMC.Finite.IsStationary (randomScanMatrix (NN := NN) p T f) π := by
  classical
  exact MCMC.Finite.exists_unique_stationary_distribution_of_irreducible
    (n := NN.State)
    (h_stoch := randomScanMatrix_isStochastic (NN := NN) (p := p) (T := T) f)
    (h_irred := h_irred)

section KbmEval

variable {NN} {p : Params NN} {T : Temperature}

/-- Pointwise evaluation of `gibbsUpdate` at `updPos`. -/
lemma gibbsUpdate_apply_updPos
    (f : R →+* ℝ) (s : NN.State) (u : U) :
    (TwoState.gibbsUpdate (NN := NN) f p T s u) (TwoState.updPos (NN := NN) s u)
      = ENNReal.ofReal (TwoState.probPos (NN := NN) f p T s u) := by
  classical
  unfold TwoState.gibbsUpdate
  set pPos : ℝ := TwoState.probPos (NN := NN) f p T s u
  have h_nonneg : 0 ≤ pPos := TwoState.probPos_nonneg (NN := NN) f p T s u
  set pPosNN : ℝ≥0 := ⟨pPos, h_nonneg⟩
  have h_le_real : pPos ≤ 1 := TwoState.probPos_le_one (NN := NN) f p T s u
  have h_leNN : pPosNN ≤ 1 := by
    change (pPosNN : ℝ) ≤ 1
    simpa using h_le_real
  have hne : TwoState.updPos (NN := NN) s u ≠ TwoState.updNeg (NN := NN) s u := by
    intro h
    have h' := congrArg (fun st : NN.State => st.act u) h
    have : TwoStateNeuralNetwork.σ_pos (NN := NN) = TwoStateNeuralNetwork.σ_neg (NN := NN) := by
      simpa [TwoState.updPos, TwoState.updNeg] using h'
    exact TwoStateNeuralNetwork.h_pos_ne_neg (NN := NN) this
  have hcoe : ENNReal.ofReal pPos = (pPosNN : ENNReal) := by
    simp [pPosNN]; exact ENNReal.ofReal_eq_coe_nnreal h_nonneg
  simp [pPos, pPosNN, hcoe,
    PMF.bernoulli_bind_pure_apply_left_of_ne (α := NN.State) (p := pPosNN) h_leNN hne]

/-- Pointwise evaluation of `gibbsUpdate` at `updNeg`. -/
lemma gibbsUpdate_apply_updNeg
    (f : R →+* ℝ) (s : NN.State) (u : U) :
    (TwoState.gibbsUpdate (NN := NN) f p T s u) (TwoState.updNeg (NN := NN) s u)
      = ENNReal.ofReal (1 - TwoState.probPos (NN := NN) f p T s u) := by
  classical
  unfold TwoState.gibbsUpdate
  set pPos : ℝ := TwoState.probPos (NN := NN) f p T s u
  have h_nonneg : 0 ≤ pPos := TwoState.probPos_nonneg (NN := NN) f p T s u
  set pPosNN : ℝ≥0 := ⟨pPos, h_nonneg⟩
  have h_le_real : pPos ≤ 1 := TwoState.probPos_le_one (NN := NN) f p T s u
  have h_leNN : pPosNN ≤ 1 := by
    change (pPosNN : ℝ) ≤ 1
    simpa using h_le_real
  have hne : TwoState.updPos (NN := NN) s u ≠ TwoState.updNeg (NN := NN) s u := by
    intro h
    have h' := congrArg (fun st : NN.State => st.act u) h
    have : TwoStateNeuralNetwork.σ_pos (NN := NN) = TwoStateNeuralNetwork.σ_neg (NN := NN) := by
      simpa [TwoState.updPos, TwoState.updNeg] using h'
    exact TwoStateNeuralNetwork.h_pos_ne_neg (NN := NN) this
  have h_eval :=
    PMF.bernoulli_bind_pure_apply_right_of_ne (α := NN.State) (p := pPosNN) h_leNN hne
  have hsub : ENNReal.ofReal (1 - pPos) = 1 - (pPosNN : ENNReal) := by
    have : (pPosNN : ENNReal) = ENNReal.ofReal pPos := by
      simp [pPosNN]
      exact (ENNReal.ofReal_eq_coe_nnreal h_nonneg).symm
    simpa [this] using (ENNReal.ofReal_sub 1 h_nonneg)
  simp [pPos, pPosNN, h_eval, hsub]

lemma Kbm_apply_updPos (f : R →+* ℝ) (u : U) (s : NN.State) :
    Kbm (NN := NN) (p := p) (T := T) f u s (TwoState.updPos (NN := NN) s u)
      = TwoState.probPos (NN := NN) f p T s u := by
  unfold Kbm
  rw [gibbsUpdate_apply_updPos (NN := NN) (p := p) (T := T) (f := f)]
  exact ENNReal.toReal_ofReal (TwoState.probPos_nonneg (NN := NN) f p T s u)

lemma Kbm_apply_updNeg (f : R →+* ℝ) (u : U) (s : NN.State) :
    Kbm (NN := NN) (p := p) (T := T) f u s (TwoState.updNeg (NN := NN) s u)
      = 1 - TwoState.probPos (NN := NN) f p T s u := by
  unfold Kbm
  rw [gibbsUpdate_apply_updNeg (NN := NN) (p := p) (T := T) (f := f)]
  have h_nonneg : 0 ≤ 1 - TwoState.probPos (NN := NN) f p T s u :=
    sub_nonneg.mpr (TwoState.probPos_le_one (NN := NN) f p T s u)
  exact ENNReal.toReal_ofReal h_nonneg

lemma Kbm_apply_other (f : R →+* ℝ) (u : U) (s s' : NN.State)
    (h_pos : s' ≠ TwoState.updPos (NN := NN) s u)
    (h_neg : s' ≠ TwoState.updNeg (NN := NN) s u) :
    Kbm (NN := NN) (p := p) (T := T) f u s s' = 0 := by
  classical
  unfold Kbm TwoState.gibbsUpdate
  set pPos := TwoState.probPos (NN := NN) f p T s u
  have h_nonneg : 0 ≤ pPos := TwoState.probPos_nonneg (NN := NN) f p T s u
  set pPosNN : ℝ≥0 := ⟨pPos, h_nonneg⟩
  have h_leNN : pPosNN ≤ 1 := by
    change (pPosNN : ℝ) ≤ 1
    simpa [pPos, pPosNN] using TwoState.probPos_le_one (NN := NN) f p T s u
  have h_K := PMF.bernoulli_bind_pure_apply_other (α := NN.State)
      (p := pPosNN) h_leNN h_pos h_neg
  simp [h_K, pPos, pPosNN]

end KbmEval

/-!
## Irreducibility / primitivity of random-scan Gibbs (finite state space)

This is the `R`-valued analogue of the irreducibility argument in `Ergodicity.lean`,
but for the **row-stochastic** matrix `randomScanMatrix` (built from `randomScanPMF`).
-/

section RandomScanConnectivity

open scoped BigOperators

variable [DecidableEq NN.State]
variable [DecidableEq σ]
variable [TwoState.TwoStateExclusiveR (NN := NN)]

-- We work at fixed parameters/temperature/hom `f`.
variable (p : Params NN) (T : Temperature) (f : R →+* ℝ)

/-- States that differ only at `u`. -/
def DiffOnly (u : U) (s s' : NN.State) : Prop :=
  (∀ v ≠ u, s.act v = s'.act v) ∧ s.act u ≠ s'.act u

/-- Sites where two states differ (Hamming support). -/
noncomputable def diffSites (s s' : NN.State) : Finset U :=
  by
    classical
    exact Finset.univ.filter (fun u : U => s.act u ≠ s'.act u)

lemma diffSites_card_zero {s s' : NN.State} :
    (diffSites (NN:=NN) s s').card = 0 → s = s' := by
  intro h0
  ext u
  by_contra hneq
  have : u ∈ diffSites (NN:=NN) s s' := by
    classical
    simp [diffSites, hneq]
  have hpos : 0 < (diffSites (NN:=NN) s s').card :=
    Finset.card_pos.mpr ⟨u, this⟩
  simp [h0] at hpos

private lemma uniformOfFintype_pos (u : U) :
    0 < (PMF.uniformOfFintype U) u := by
  -- uniform probability is (card U)⁻¹, which is positive in ℝ≥0∞
  simpa [PMF.uniformOfFintype_apply] using
    (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top (Fintype.card U)))

private lemma randomScanPMF_apply (s t : NN.State) :
    randomScanPMF (NN := NN) p T f s t
      = ∑ u : U, (PMF.uniformOfFintype U) u *
          (TwoState.gibbsUpdate (NN := NN) f p T s u) t := by
  classical
  -- `PMF.bind_apply` gives a `tsum`; for `Fintype` it's a finite sum.
  simp [randomScanPMF, PMF.bind_apply, tsum_fintype]

private lemma randomScanPMF_pos_of_term
    {s t : NN.State} (u : U)
    (hterm : 0 < (PMF.uniformOfFintype U) u *
      (TwoState.gibbsUpdate (NN := NN) f p T s u) t) :
    0 < randomScanPMF (NN := NN) p T f s t := by
  classical
  -- the sum is ≥ the positive `u`-term
  have hsum :
      randomScanPMF (NN := NN) p T f s t
        = ∑ v : U, (PMF.uniformOfFintype U) v *
            (TwoState.gibbsUpdate (NN := NN) f p T s v) t :=
    randomScanPMF_apply (NN := NN) (p := p) (T := T) (f := f) s t
  -- nonnegativity of all terms
  have hnonneg :
      ∀ v : U, 0 ≤ (PMF.uniformOfFintype U) v *
          (TwoState.gibbsUpdate (NN := NN) f p T s v) t := by
    intro v
    exact mul_nonneg (by exact le_of_lt (uniformOfFintype_pos (U:=U) v))
      (by simpa using (zero_le ((TwoState.gibbsUpdate (NN := NN) f p T s v) t)))
  have hmem : u ∈ (Finset.univ : Finset U) := by simp
  have hle : (PMF.uniformOfFintype U) u *
        (TwoState.gibbsUpdate (NN := NN) f p T s u) t
      ≤ ∑ v : U, (PMF.uniformOfFintype U) v *
          (TwoState.gibbsUpdate (NN := NN) f p T s v) t := by
    simpa using (Finset.single_le_sum (fun v hv => hnonneg v) hmem)
  have : 0 < ∑ v : U, (PMF.uniformOfFintype U) v *
          (TwoState.gibbsUpdate (NN := NN) f p T s v) t :=
    lt_of_lt_of_le hterm hle
  simpa [hsum] using this

private lemma toReal_pos_of_pmf_pos {s t : NN.State}
    (hpos : 0 < randomScanPMF (NN := NN) p T f s t) :
    0 < (randomScanPMF (NN := NN) p T f s t).toReal := by
  -- PMF values are ≤ 1, hence < ⊤
  have hle : randomScanPMF (NN := NN) p T f s t ≤ 1 :=
    (randomScanPMF (NN := NN) p T f s).coe_le_one t
  have hlt_top : randomScanPMF (NN := NN) p T f s t < ⊤ :=
    lt_of_le_of_lt hle (by simp)
  exact (ENNReal.toReal_pos_iff).2 ⟨hpos, hlt_top⟩

lemma randomScanMatrix_pos_of_diffOnly
    {u : U} {s s' : NN.State} (h : DiffOnly (NN:=NN) u s s') :
    0 < randomScanMatrix (NN := NN) p T f s' s := by
  classical
  -- classify the source value at `u`
  rcases (TwoState.TwoStateExclusiveR.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u) with hpos' | hneg'
  · -- s'.act u = σ_pos, so s.act u = σ_neg, hence s = updNeg s' u
    have hs_neg : s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN) := by
      rcases (TwoState.TwoStateExclusiveR.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hspos | hsneg
      · exact (False.elim (h.2 (by simpa [hpos'] using hspos)))
      · simpa using hsneg
    have hs_eq : s = TwoState.updNeg (NN := NN) s' u := by
      ext v
      by_cases hvu : v = u
      · subst hvu; simpa [TwoState.updNeg, Function.update, hs_neg]
      · have hoff := h.1 v hvu
        simp [TwoState.updNeg, Function.update, hvu, hoff]
    -- positive contribution from choosing u and taking the `updNeg` branch
    have hsite_pos : 0 < (PMF.uniformOfFintype U) u :=
      uniformOfFintype_pos (U:=U) u
    have hprob_pos : 0 < (1 - TwoState.probPos (NN := NN) f p T s' u) :=
      sub_pos.2 (TwoState.probPos_lt_one (NN := NN) f p T s' u)
    have hstep_pos :
        0 < (TwoState.gibbsUpdate (NN := NN) f p T s' u) s := by
      -- rewrite using `gibbsUpdate_apply_updNeg` and `hs_eq`
      subst hs_eq
      simpa [gibbsUpdate_apply_updNeg (NN:=NN) (p:=p) (T:=T) (f:=f) s' u] using
        (ENNReal.ofReal_pos.2 hprob_pos)
    have hterm :
        0 < (PMF.uniformOfFintype U) u *
            (TwoState.gibbsUpdate (NN := NN) f p T s' u) s :=
      by
        have hne : (PMF.uniformOfFintype U) u *
            (TwoState.gibbsUpdate (NN := NN) f p T s' u) s ≠ 0 := by
          intro h0
          rcases mul_eq_zero.mp h0 with h0u | h0step
          · exact (ne_of_gt hsite_pos) h0u
          · exact (ne_of_gt hstep_pos) h0step
        exact (pos_iff_ne_zero).2 hne
    have hpmf_pos :
        0 < randomScanPMF (NN := NN) p T f s' s :=
      randomScanPMF_pos_of_term (NN:=NN) (p:=p) (T:=T) (f:=f) u hterm
    -- matrix entry is toReal of the PMF entry
    simpa [randomScanMatrix, PMFMatrix.pmfToMatrix] using
      toReal_pos_of_pmf_pos (NN:=NN) (p:=p) (T:=T) (f:=f) hpmf_pos
  · -- s'.act u = σ_neg, so s.act u = σ_pos, hence s = updPos s' u
    have hs_pos : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN) := by
      rcases (TwoState.TwoStateExclusiveR.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hspos | hsneg
      · simpa using hspos
      · exact (False.elim (h.2 (by simpa [hneg'] using hsneg)))
    have hs_eq : s = TwoState.updPos (NN := NN) s' u := by
      ext v
      by_cases hvu : v = u
      · subst hvu; simpa [TwoState.updPos, Function.update, hs_pos]
      · have hoff := h.1 v hvu
        simp [TwoState.updPos, Function.update, hvu, hoff]
    have hsite_pos : 0 < (PMF.uniformOfFintype U) u :=
      uniformOfFintype_pos (U:=U) u
    have hprob_pos : 0 < TwoState.probPos (NN := NN) f p T s' u :=
      TwoState.probPos_pos (NN := NN) f p T s' u
    have hstep_pos :
        0 < (TwoState.gibbsUpdate (NN := NN) f p T s' u) s := by
      subst hs_eq
      simpa [gibbsUpdate_apply_updPos (NN:=NN) (p:=p) (T:=T) (f:=f) s' u] using
        (ENNReal.ofReal_pos.2 hprob_pos)
    have hterm :
        0 < (PMF.uniformOfFintype U) u *
            (TwoState.gibbsUpdate (NN := NN) f p T s' u) s :=
      by
        have hne : (PMF.uniformOfFintype U) u *
            (TwoState.gibbsUpdate (NN := NN) f p T s' u) s ≠ 0 := by
          intro h0
          rcases mul_eq_zero.mp h0 with h0u | h0step
          · exact (ne_of_gt hsite_pos) h0u
          · exact (ne_of_gt hstep_pos) h0step
        exact (pos_iff_ne_zero).2 hne
    have hpmf_pos :
        0 < randomScanPMF (NN := NN) p T f s' s :=
      randomScanPMF_pos_of_term (NN:=NN) (p:=p) (T:=T) (f:=f) u hterm
    simpa [randomScanMatrix, PMFMatrix.pmfToMatrix] using
      toReal_pos_of_pmf_pos (NN:=NN) (p:=p) (T:=T) (f:=f) hpmf_pos

lemma randomScanMatrix_diag_pos (s : NN.State) :
    0 < randomScanMatrix (NN := NN) p T f s s := by
  classical
  -- pick any site u0 (U is nonempty)
  let u0 : U := Classical.choice (by infer_instance : Nonempty U)
  rcases (TwoState.TwoStateExclusiveR.pact_iff (NN:=NN) (a:=s.act u0)).1 (s.hp u0) with hspos | hsneg
  · -- act u0 = σ_pos, so updPos s u0 = s and that branch has probPos > 0
    have h_eq : TwoState.updPos (NN:=NN) s u0 = s :=
      TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u0 hspos
    have hsite_pos : 0 < (PMF.uniformOfFintype U) u0 :=
      uniformOfFintype_pos (U:=U) u0
    have hprob_pos : 0 < TwoState.probPos (NN := NN) f p T s u0 :=
      TwoState.probPos_pos (NN := NN) f p T s u0
    have hstep_pos :
        0 < (TwoState.gibbsUpdate (NN := NN) f p T s u0) s := by
      -- use updPos evaluation
      have : (TwoState.gibbsUpdate (NN := NN) f p T s u0) (TwoState.updPos (NN := NN) s u0)
          = ENNReal.ofReal (TwoState.probPos (NN := NN) f p T s u0) :=
        gibbsUpdate_apply_updPos (NN:=NN) (p:=p) (T:=T) (f:=f) s u0
      -- rewrite `updPos` to `s`
      have h_ofReal : 0 < ENNReal.ofReal (TwoState.probPos (NN := NN) f p T s u0) :=
        (ENNReal.ofReal_pos.2 hprob_pos)
      have hval : (TwoState.gibbsUpdate (NN := NN) f p T s u0) s
            = ENNReal.ofReal (TwoState.probPos (NN := NN) f p T s u0) := by
        simpa [h_eq] using this
      -- avoid `simp` rewriting `ENNReal.ofReal_pos`; just rewrite and close
      rw [hval]
      exact h_ofReal
    have hterm :
        0 < (PMF.uniformOfFintype U) u0 *
            (TwoState.gibbsUpdate (NN := NN) f p T s u0) s :=
      by
        have hne : (PMF.uniformOfFintype U) u0 *
            (TwoState.gibbsUpdate (NN := NN) f p T s u0) s ≠ 0 := by
          intro h0
          rcases mul_eq_zero.mp h0 with h0u | h0step
          · exact (ne_of_gt hsite_pos) h0u
          · exact (ne_of_gt hstep_pos) h0step
        exact (pos_iff_ne_zero).2 hne
    have hpmf_pos :
        0 < randomScanPMF (NN := NN) p T f s s :=
      randomScanPMF_pos_of_term (NN:=NN) (p:=p) (T:=T) (f:=f) u0 hterm
    simpa [randomScanMatrix, PMFMatrix.pmfToMatrix] using
      toReal_pos_of_pmf_pos (NN:=NN) (p:=p) (T:=T) (f:=f) hpmf_pos
  · -- act u0 = σ_neg, so updNeg s u0 = s and that branch has (1-probPos) > 0
    have h_eq : TwoState.updNeg (NN:=NN) s u0 = s :=
      TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u0 hsneg
    have hsite_pos : 0 < (PMF.uniformOfFintype U) u0 :=
      uniformOfFintype_pos (U:=U) u0
    have hprob_pos : 0 < (1 - TwoState.probPos (NN := NN) f p T s u0) :=
      sub_pos.2 (TwoState.probPos_lt_one (NN := NN) f p T s u0)
    have hstep_pos :
        0 < (TwoState.gibbsUpdate (NN := NN) f p T s u0) s := by
      have : (TwoState.gibbsUpdate (NN := NN) f p T s u0) (TwoState.updNeg (NN := NN) s u0)
          = ENNReal.ofReal (1 - TwoState.probPos (NN := NN) f p T s u0) :=
        gibbsUpdate_apply_updNeg (NN:=NN) (p:=p) (T:=T) (f:=f) s u0
      have h_ofReal : 0 < ENNReal.ofReal (1 - TwoState.probPos (NN := NN) f p T s u0) :=
        (ENNReal.ofReal_pos.2 hprob_pos)
      have hval : (TwoState.gibbsUpdate (NN := NN) f p T s u0) s
            = ENNReal.ofReal (1 - TwoState.probPos (NN := NN) f p T s u0) := by
        simpa [h_eq] using this
      rw [hval]
      exact h_ofReal
    have hterm :
        0 < (PMF.uniformOfFintype U) u0 *
            (TwoState.gibbsUpdate (NN := NN) f p T s u0) s :=
      by
        have hne : (PMF.uniformOfFintype U) u0 *
            (TwoState.gibbsUpdate (NN := NN) f p T s u0) s ≠ 0 := by
          intro h0
          rcases mul_eq_zero.mp h0 with h0u | h0step
          · exact (ne_of_gt hsite_pos) h0u
          · exact (ne_of_gt hstep_pos) h0step
        exact (pos_iff_ne_zero).2 hne
    have hpmf_pos :
        0 < randomScanPMF (NN := NN) p T f s s :=
      randomScanPMF_pos_of_term (NN:=NN) (p:=p) (T:=T) (f:=f) u0 hterm
    simpa [randomScanMatrix, PMFMatrix.pmfToMatrix] using
      toReal_pos_of_pmf_pos (NN:=NN) (p:=p) (T:=T) (f:=f) hpmf_pos

end RandomScanConnectivity

end HopfieldBoltzmannR

end NeuralNetwork
