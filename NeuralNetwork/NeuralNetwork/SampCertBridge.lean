import HopfieldNet.Attic.SampCert.SLang
import NeuralNetwork.NeuralNetwork.HopfieldBoltzmannR

/-!
# NeuralNetwork ↔ SampCert bridge (minimal)

SampCert’s core `SLang α` is a simple model of discrete distributions: `α → ℝ≥0∞`.

For our purposes, the key observation is that Mathlib’s `PMF α` is also (morally) a function
`α → ℝ≥0∞` together with a normalization proof. So we can convert **any** `PMF` into `SLang`
by forgetting the normalization proof.

This gives an integration path without committing to the full SampCert DP/Gaussian stack,
which currently lives in `HopfieldNet/Attic/SampCert` and needs a port to the current Mathlib.
-/

namespace NeuralNetwork
namespace SampCertBridge

open scoped BigOperators
open Classical
open ENNReal

/-! ## PMF → SLang -/

def pmfToSLang {α : Type} (p : PMF α) : SLang α := fun a => p a

@[simp] theorem pmfToSLang_apply {α : Type} (p : PMF α) (a : α) :
    pmfToSLang p a = p a := rfl

theorem pmfToSLang_hasSum_one {α : Type} (p : PMF α) :
    HasSum (pmfToSLang p) 1 := p.property

/-! ## Random-scan Gibbs as SLang transition kernels -/

namespace HopfieldBoltzmannR

open ProbabilityTheory

variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork R U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN]
variable [HasToReal R]

noncomputable def randomScanSLang
    (p : Params NN) (T : Temperature) (f : R →+* ℝ) (s : NN.State) : SLang NN.State :=
  pmfToSLang (HopfieldBoltzmannR.randomScanPMF (NN := NN) p T f s)

@[simp] theorem randomScanSLang_apply
    (p : Params NN) (T : Temperature) (f : R →+* ℝ) (s s' : NN.State) :
    randomScanSLang (NN := NN) p T f s s' =
      HopfieldBoltzmannR.randomScanPMF (NN := NN) p T f s s' := rfl

end HopfieldBoltzmannR

end SampCertBridge
end NeuralNetwork
