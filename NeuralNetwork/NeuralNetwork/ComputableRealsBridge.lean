import NeuralNetwork.NeuralNetwork.toCanonicalEnsemble
import HopfieldNet.CReals.CRealCCLOF
import HopfieldNet.CReals.CRealRealEquiv

/-!
# Computable reals bridge (principled theorem-transfer layer)

This module provides a *minimal* interface to run a `NeuralNetwork R U σ` "over computable reals"
while still reusing Mathlib / PhysLean results stated over `ℝ`.

Core idea:
- Keep the network (weights, dynamics, energy proof obligations) valued in a scalar `R`
  (e.g. `Computable.CReal`).
- Provide a ring morphism `toReal : R →+* ℝ` (and, optionally, monotonicity for `≤`).
- When you need analysis/measure-theory (canonical ensembles, `Real.exp`, etc.), push the
  scalar-valued energy through `toReal` to obtain an `ℝ`-valued energy.

This is *theorem-transfer friendly*, but not intended to be executable when `toReal` is
noncomputable (as it is for `CReal`).
-/

namespace NeuralNetwork

universe uR

-- NOTE: `PhysLean.StatisticalMechanics.CanonicalEnsemble` is currently `Type`-based (universe 0),
-- so for the canonical-ensemble bridge we keep `U` and `σ` in `Type`.
variable {R : Type uR} {U : Type} {σ : Type}

/-- A scalar type that can be mapped into `ℝ` as a ring homomorphism. -/
class HasToReal (R : Type uR) [NonAssocSemiring R] : Type (max uR 1) where
  toRealRingHom : R →+* ℝ

/--
Optional strengthening: the map to `ℝ` is monotone for the order on `R`.

This is what you need to transport Lyapunov (energy non-increase) inequalities.
-/
class HasToRealOrder (R : Type uR) [NonAssocSemiring R] [LE R] extends HasToReal R where
  mono_toReal : ∀ {a b : R}, a ≤ b → toRealRingHom a ≤ toRealRingHom b

namespace HasToRealOrder

variable [NonAssocSemiring R] [LE R] [HasToRealOrder R]

lemma toReal_mono {a b : R} (h : a ≤ b) :
    HasToReal.toRealRingHom (R := R) a ≤ HasToReal.toRealRingHom (R := R) b :=
  HasToRealOrder.mono_toReal (R := R) h

end HasToRealOrder

/-- Instance: `Computable.CReal` maps to `ℝ` via the existing ring hom. -/
instance : HasToReal Computable.CReal where
  toRealRingHom := Computable.CReal.toRealRingHom

/-- Instance: `Computable.CReal` order is compatible with `toReal`. -/
instance : HasToRealOrder Computable.CReal where
  toRealRingHom := Computable.CReal.toRealRingHom
  mono_toReal := by
    intro a b hab
    exact Computable.CReal.toReal_mono hab

/-- Trivial instance: `ℝ` maps to itself. -/
instance : HasToReal ℝ where
  toRealRingHom := RingHom.id ℝ

instance : HasToRealOrder ℝ where
  toRealRingHom := RingHom.id ℝ
  mono_toReal := by
    intro a b hab
    simpa using hab

/--
Hamiltonian structure where the energy is valued in a scalar `R` (e.g. `CReal`),
but can be pushed to `ℝ` via `HasToReal`.

This is the most direct way to keep the *model* in `R` while reusing `ℝ`-theory.
-/
class IsHamiltonianR [NonAssocSemiring R] [LE R] (NN : NeuralNetwork R U σ) [DecidableEq U] where
  energy : Params NN → NN.State → R
  energy_is_lyapunov :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      energy p ((NeuralNetwork.State.Up s p u)) ≤ energy p s

namespace IsHamiltonianR

variable [NonAssocSemiring R] [LE R] [HasToRealOrder R] [DecidableEq U]
variable (NN : NeuralNetwork R U σ)
variable [IsHamiltonianR (R := R) (U := U) (σ := σ) NN]

/-- The induced `ℝ`-valued energy function obtained by pushing through `toReal`. -/
noncomputable def energyToReal (p : Params NN) : NN.State → ℝ :=
  fun s => (HasToReal.toRealRingHom (R := R)) (IsHamiltonianR.energy (NN := NN) p s)

lemma energyToReal_is_lyapunov (p : Params NN) (s : NN.State) (u : U) :
    energyToReal (NN := NN) p (NeuralNetwork.State.Up s p u) ≤ energyToReal (NN := NN) p s := by
  dsimp [energyToReal]
  exact HasToRealOrder.toReal_mono (R := R)
    (IsHamiltonianR.energy_is_lyapunov (NN := NN) p s u)

end IsHamiltonianR

/-!
## Canonical ensemble bridge (finite state)

For finite-state networks, measurability is trivial, so we can directly build a
`CanonicalEnsemble NN.State` with `ℝ`-valued energy given by `energyToReal`.
-/

open MeasureTheory

namespace BridgeToCanonicalEnsemble

variable [NonAssocSemiring R] [LE R] [HasToRealOrder R]
variable (NN : NeuralNetwork R U σ)
variable [Fintype NN.State]
variable [DecidableEq U]
variable [IsHamiltonianR (R := R) (U := U) (σ := σ) NN]

-- Reuse the trivial measurable space instance from the existing `ℝ`-specialized bridge.
instance : MeasurableSpace NN.State := ⊤

@[simp] lemma measurable_of_fintype_state (f : NN.State → ℝ) : Measurable f := by
  unfold Measurable; intro s _; simp

/--
Lift a scalar-valued Hamiltonian network (energy in `R`) into a `CanonicalEnsemble`
by converting the energy to `ℝ`.
-/
@[simps!]
noncomputable def toCanonicalEnsemble
    (p : Params NN) : CanonicalEnsemble NN.State where
  energy := IsHamiltonianR.energyToReal (NN := NN) p
  dof := 0
  phaseSpaceunit := 1
  energy_measurable := by
    intro _; simpa using (measurable_of_fintype_state (NN := NN) (f := IsHamiltonianR.energyToReal (NN := NN) p))
  μ := Measure.count
  μ_sigmaFinite := by infer_instance

end BridgeToCanonicalEnsemble

end NeuralNetwork
