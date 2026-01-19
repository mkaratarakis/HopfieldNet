import NeuralNetwork.NeuralNetwork.HopfieldBoltzmannR

/-!
# Thermodynamics for Hopfield/Boltzmann models (R-generic energy, ℝ thermodynamics)

This file exposes entropy / free energy for finite-state `NeuralNetwork` models whose energy
is valued in a scalar `R` with a bridge `HasToReal R`. The thermodynamic quantities themselves
live in `ℝ` via `HopfieldBoltzmannR.CEparams`, so we can directly reuse PhysLean’s canonical
ensemble theory.
-/

set_option linter.unusedSectionVars false

namespace NeuralNetwork

open MeasureTheory
open scoped BigOperators Temperature CanonicalEnsemble

namespace HopfieldBoltzmannR

open CanonicalEnsemble

variable {R : Type} {U : Type} {σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork R U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN]
variable [HasToReal R]
variable (spec : TwoState.EnergySpec' (NN := NN))

/-- Partition function \(Z\) (dimensionless, finite/counting case). -/
noncomputable abbrev Z (p : Params NN) (T : Temperature) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).partitionFunction T

/-- Mean energy \(U\). -/
noncomputable abbrev meanEnergy (p : Params NN) (T : Temperature) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).meanEnergy T

/-- Helmholtz free energy \(F\). -/
noncomputable abbrev helmholtzFreeEnergy (p : Params NN) (T : Temperature) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).helmholtzFreeEnergy T

/-- Shannon entropy \(S = -k_B \sum p_i \log p_i\) (finite/counting case). -/
noncomputable abbrev shannonEntropy (p : Params NN) (T : Temperature) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).shannonEntropy T

/-- Thermodynamic entropy \(S\) (absolute entropy); coincides with Shannon entropy in the
finite/counting case. -/
noncomputable abbrev thermodynamicEntropy (p : Params NN) (T : Temperature) : ℝ :=
  (CEparams (NN := NN) (spec := spec) p).thermodynamicEntropy T

theorem thermodynamicEntropy_eq_shannonEntropy (p : Params NN) (T : Temperature) :
    thermodynamicEntropy (NN := NN) (spec := spec) p T
      = shannonEntropy (NN := NN) (spec := spec) p T := by
  simpa [thermodynamicEntropy, shannonEntropy] using
    (CanonicalEnsemble.thermodynamicEntropy_eq_shannonEntropy
      (𝓒 := CEparams (NN := NN) (spec := spec) p) T)

/-- Fundamental identity \(F = U - T \cdot S\) for finite Hopfield/Boltzmann models. -/
theorem helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
    (p : Params NN) (T : Temperature) (hT : 0 < T.val) :
    helmholtzFreeEnergy (NN := NN) (spec := spec) p T
      = meanEnergy (NN := NN) (spec := spec) p T
        - T.val * thermodynamicEntropy (NN := NN) (spec := spec) p T := by
  have hE :
      MeasureTheory.Integrable (CEparams (NN := NN) (spec := spec) p).energy
        ((CEparams (NN := NN) (spec := spec) p).μProd T) :=
    MeasureTheory.Integrable.of_finite
  simpa [helmholtzFreeEnergy, meanEnergy, thermodynamicEntropy] using
    (CanonicalEnsemble.helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy
      (𝓒 := CEparams (NN := NN) (spec := spec) p) T hT (hE := hE))

end HopfieldBoltzmannR

end NeuralNetwork
