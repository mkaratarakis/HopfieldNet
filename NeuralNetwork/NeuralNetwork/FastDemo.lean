import NeuralNetwork.NeuralNetwork.FastHopfieldEnergy
import NeuralNetwork.NeuralNetwork.FastRandomScan
import NeuralNetwork.NeuralNetwork.FastBoltzmannEval
import NeuralNetwork.NeuralNetwork.FastMarkovMatrix
import NeuralNetwork.NeuralNetwork.FastChecks
import NeuralNetwork.NeuralNetwork.FastCertificates

/-!
# Demo: end-to-end executable Gibbs probabilities (FastReal)

This file instantiates a tiny `SymmetricBinary ℚ (Fin 2)` Hopfield net and evaluates:

- one-site Gibbs probability intervals (`probPos?`), and
- a random-scan transition entry interval (`randomScanEntry?`),

at a chosen precision.
-/

namespace NeuralNetwork
namespace FastDemo

open Finset Matrix TwoState
open Computable.Fast

abbrev U : Type := Fin 2

instance : Nonempty U := ⟨0⟩

abbrev NN : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

def w : Matrix U U ℚ := fun i j => if i = j then 0 else 1

lemma w_isSymm : w.IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [w]
  · have hji : j ≠ i := by
      intro h
      exact hij h.symm
    simp [w, hij, hji]

def p : Params NN :=
{ w := w
  hw := by
    intro u v huv
    have h : u = v := by
      -- for `SymmetricBinary`, `NN.Adj u v` is definitionaly `u ≠ v`
      simpa using (not_ne_iff.mp huv)
    subst h
    simp [w]
  hw' := by
    refine And.intro ?_ ?_
    · exact w_isSymm
    · intro u
      simp [w]
  σ := fun _ => Vector.ofFn (fun _ => (0 : ℚ))
  θ := fun _ => Vector.ofFn (fun _ => (0 : ℚ)) }

def s : (NN).State :=
{ act := fun u => if u = (0 : U) then (1 : ℚ) else (-1 : ℚ)
  hp := by
    intro u
    by_cases hu : u = (0 : U)
    · simp [NN, TwoState.SymmetricBinary, hu]
    · simp [NN, TwoState.SymmetricBinary, hu] }

def β : FastReal := Computable.Fast.FastReal.ofRat 1

def sPos : (NN).State := TwoState.updPos (NN := NN) s (0 : U)

-- One-site Gibbs probability interval at precision `n = 10`.
#eval (NeuralNetwork.FastTwoStateGibbs.probPos? (NN := NN) β p s (0 : U)) 10

-- Random-scan entry interval P(s → sPos) at precision `n = 10`.
#eval (NeuralNetwork.FastRandomScan.randomScanEntry? (NN := NN) β p s sPos) 10

-- Boltzmann probability interval π(s) at precision `n = 10`.
#eval (NeuralNetwork.FastBoltzmannEval.probability? (U := U) β p s) 10

-- Full random-scan transition matrix (4x4 for `Fin 2`) at precision `n = 10`.
#eval (NeuralNetwork.FastMarkovMatrix.randomScanMatrix? (U := U) β p) 10

-- Full Boltzmann vector (length 4) at precision `n = 10`.
#eval (NeuralNetwork.FastMarkovMatrix.boltzmannVec? (U := U) β p) 10

-- Row-sum sanity check: each row sum should enclose 1.
#eval (do
  let M ← (NeuralNetwork.FastMarkovMatrix.randomScanMatrix? (U := U) β p 10)
  pure (NeuralNetwork.FastChecks.rowSumsContainOne M 10))

-- Stationarity sanity check: compute enclosures for (πP - π).
#eval (do
  let π ← (NeuralNetwork.FastMarkovMatrix.boltzmannVec? (U := U) β p 10)
  let P ← (NeuralNetwork.FastMarkovMatrix.randomScanMatrix? (U := U) β p 10)
  pure (NeuralNetwork.FastChecks.invarianceDelta π P 10))

-- Automatic precision search certificates (tolerance = 2^{-12}, search n in [6, 6+10]).
#eval (NeuralNetwork.FastChecks.findRowSumPrecision?
  (fun n => NeuralNetwork.FastMarkovMatrix.randomScanMatrix? (U := U) β p n) 6 10 12)

#eval (NeuralNetwork.FastChecks.findStationaryPrecision?
  (fun n => NeuralNetwork.FastMarkovMatrix.boltzmannVec? (U := U) β p n)
  (fun n => NeuralNetwork.FastMarkovMatrix.randomScanMatrix? (U := U) β p n)
  6 10 12)

-- Pack everything into a witness object (and verify it).
#eval (NeuralNetwork.FastCertificates.findWitness? (U := U) β p 6 20 12)

end FastDemo
end NeuralNetwork
