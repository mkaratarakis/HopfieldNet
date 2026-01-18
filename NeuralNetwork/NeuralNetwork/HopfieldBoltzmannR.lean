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
noncomputable def energyReal
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

section KbmEval

variable {NN} {p : Params NN} {T : Temperature}

/-- Pointwise evaluation of `gibbsUpdate` at `updPos`. -/
private lemma gibbsUpdate_apply_updPos
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
private lemma gibbsUpdate_apply_updNeg
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

end HopfieldBoltzmannR

end NeuralNetwork
