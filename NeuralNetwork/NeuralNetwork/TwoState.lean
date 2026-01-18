import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Data.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import NeuralNetwork.NeuralNetwork.NeuralNetwork
import PhysLean.Thermodynamics.Temperature.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Two-state Hopfield networks: Gibbs update and zero-temperature limit

This file builds a general interface for two-state neural networks, provides
three concrete Hopfield-style instances, develops a one-site Gibbs update
kernel, and proves convergence of this kernel to a deterministic zero-temperature
limit as `β → ∞` (equivalently, `T → 0+`).

## Overview

- Abstract typeclass `TwoStateNeuralNetwork` for two-valued activations:
  it exposes distinguished states `σ_pos`, `σ_neg`, a canonical index `θ0` for the
  single threshold parameter, and order data connecting the numeric embedding `m`
  of the two states (`m σ_neg < m σ_pos`).

- Three concrete encodings of (symmetric) Hopfield parameters:
  * `SymmetricBinary R U` with σ = R and activations in {-1, 1}.
  * `SymmetricSignum R U` with σ = Signum (a type-level two-point type).
  * `ZeroOne R U` with σ = R and activations in {0, 1}.

- A scale parameter, pushed along a ring hom `f`:
  * `scale f : ℝ` and its ring-generalization `scaleS f : S`.
    These quantify the numeric gap between `σ_pos` and `σ_neg` in the image of `f`.

- Probabilistic update at positive temperature:
  * `logisticProb x := 1 / (1 + exp(-x))` with basic bounds
    `logisticProb_nonneg` and `logisticProb_le_one`.
  * `probPos f p T s u : ℝ` gives `P(σ_u = σ_pos)` for one Gibbs update, formed from
    logisticProb with argument `(scale f) * f(local field) * β(T)`.

- One-site PMF update (and sweeps):
  * `updPos`, `updNeg`: force a single site to `σ_pos`/`σ_neg`.
  * `gibbsUpdate f p T s u : PMF State` is the one-site Gibbs update.
  * `zeroTempDet p s u` is the deterministic threshold update at `T = 0`.
  * `gibbsSweepAux`, `gibbsSweep`: sequential composition over a list of sites.

- Energy specification abstraction:
  * `EnergySpec` and a simplified `EnergySpec'` bundle together a global energy
    `E` and a local-field `localField` satisfying:
      `f (E p (updPos s u) - E p (updNeg s u))
        = - (scale f) * f (localField p s u)`.
    It follows that:
      `probPos f p T s u = logisticProb (- f(ΔE) * β(T))`
    where `ΔE := E p (updPos s u) - E p (updNeg s u)`.

- Zero-temperature limit:
  * `scale_pos f` shows `scale f > 0` for an injective order-embedding `f`.
  * `zeroTempLimitPMF p s u` is the limiting one-step kernel at `T = 0+`, which:
    - moves deterministically to `updPos` if local field is positive,
    - to `updNeg` if negative,
    - and splits 1/2–1/2 between them on a tie.
  * Main theorem:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`
    states the PMF `gibbsUpdate f p (tempOfBeta b) s u` converges (as `b → ∞`)
    to `zeroTempLimitPMF p s u`, pointwise on states.

## Key definitions and lemmas

- Interfaces and instances:
  * `class TwoStateNeuralNetwork NN`:
    exposes `σ_pos`, `σ_neg`, `θ0`, and ordering data `m σ_neg < m σ_pos`.
  * Instances:
    - `instTwoStateSymmetricBinary` for `SymmetricBinary`,
    - `instTwoStateSignum` for `SymmetricSignum`,
    - `instTwoStateZeroOne` for `ZeroOne`.

- Scaling tools:
  * `scale f : ℝ`, `scaleS f : S`:
    gap between the numeric images of `σ_pos` and `σ_neg`.
    Specializations:
      - `scale_binary f = f 2` on `SymmetricBinary`,
      - `scale_zeroOne f = f 1` on `ZeroOne`.

- Gibbs probability and PMFs:
  * `logisticProb` with bounds:
      `logisticProb_nonneg`, `logisticProb_le_one`.
  * `probPos f p T s u`:
      `= logisticProb ((scale f) * f(localField) * β(T))`.
  * `updPos`, `updNeg`: single-site state updates.
  * `gibbsUpdate f p T s u : PMF State`: one-site Gibbs step.
  * `gibbsSweepAux`, `gibbsSweep`: sequential composition over a list of sites.

- Energy view:
  * `EnergySpec`, `EnergySpec'` and the fundamental relation
      `f (E p (updPos s u) - E p (updNeg s u))
        = - (scale f) * f (localField p s u)`.
  * `EnergySpec.probPos_eq_of_energy`:
      re-express `probPos` via the energy difference `ΔE`.

- Convergence to zero temperature:
  * `scale_pos f`: positivity of `scale f` under an injective order embedding.
  * `zeroTempLimitPMF p s u : PMF State`: the `T → 0+` limit kernel.
  * Pointwise convergence on the only two reachable states:
      - `gibbs_update_tends_to_zero_temp_limit_apply_updPos`
      - `gibbs_update_tends_to_zero_temp_limit_apply_updNeg`
    and zero limit on any other target state
      - `gibbs_update_tends_to_zero_temp_limit_apply_other`.
  * Main PMF convergence:
      `gibbs_update_tends_to_zero_temp_limit f hf p s u`.

## Typeclass and notation prerequisites

- Base field and order:
  `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`.
- Sites:
  `[DecidableEq U] [Fintype U] [Nonempty U]` for finite networks and
  decidable equality on sites.
- Embeddings for the scale and probabilities:
  - For `scale` and `probPos` we use a typeclass-driven `f` that is simultaneously
    a ring hom (`[RingHomClass F R ℝ]`) and (when needed for convergence)
    an order embedding (`[OrderHomClass F R ℝ]`) with `Function.Injective f`.

- Probability monad:
  uses `PMF` from Mathlib. The constructions are purely discrete.

## Design notes

- The class `TwoStateNeuralNetwork` abstracts the parts of a network used by a
  two-site threshold update: a canonical scalar threshold index `θ0`, the result
  of `fact` at or above threshold (`σ_pos`) and strictly below (`σ_neg`), and
  numeric ordering `m σ_neg < m σ_pos`.
- The concrete Hopfield instances share the same adjacency and `κ2 = 1` setup,
  but differ in the activation alphabet and decoding map `m`.
- The scaling `scale f` is a thin adapter that makes formulas uniform across
  different encodings, so that Gibbs updates depending on `f(local field)` and
  `β(T)` can be stated once for all `NN`.

## Usage

- To run one Gibbs update at site `u`:
  ```
  gibbsUpdate f p T s u : PMF _
  ```
- To sweep a list of sites in order:
  ```
  gibbsSweep order p T f s0 : PMF _
  ```
- If you can provide an `EnergySpec`, then:
  ```
  probPos f p T s u = logisticProb (- f(ΔE) * β(T))
  ```
  where `ΔE = E p (updPos s u) - E p (updNeg s u)`.

- The zero-temperature limit theorem applies once you supply an `f` that is both
  a ring hom and an injective order embedding (via the corresponding typeclasses).

-/

open Finset Matrix NeuralNetwork State Constants Temperature Filter Topology
open scoped ENNReal NNReal BigOperators

--variable {R U σ : Type}
--variable {R U σ : Type*}
universe uR uU uσ

-- We can also parametrize earlier variables with these universes if desired:
variable {R : Type uR} {U : Type uU} {σ : Type uσ}

--variable {R U σ : Type}

/-- A minimal two-point activation alphabet.

This class specifies:
- `σ_pos`: the distinguished “positive” activation,
- `σ_neg`: the distinguished “negative” activation,
- `embed`: a numeric embedding `σ → R` used to interpret activations in the ambient ring `R`.
-/
class TwoPointActivation (R : Type) (σ : Type) where
  /-- Distinguished “positive” activation state. -/
  σ_pos : σ
  /-- Distinguished “negative” activation state. -/
  σ_neg : σ
  /-- Numeric embedding of activation states into the ambient ring `R`. -/
  embed : σ → R

/-- Scale between the two distinguished activations in `σ`, computed in `R` via the embedding.
It is defined as `embed σ_pos - embed σ_neg`. -/
@[simp] def twoPointScale {R σ} [Sub R] [TwoPointActivation R σ] : R :=
  TwoPointActivation.embed (R:=R) (σ:=σ) (TwoPointActivation.σ_pos (R:=R) (σ:=σ)) -
    TwoPointActivation.embed (R:=R) (σ:=σ) (TwoPointActivation.σ_neg (R:=R) (σ:=σ))

/-- Two–state neural networks (abstract interface).

This exposes:
- `σ_pos`, `σ_neg`: the two distinguished activation states,
- `θ0`: a canonical index into the `κ2`-vector of thresholds extracting the scalar threshold,
- facts that `fact` returns `σ_pos` at or above `θ0`, and `σ_neg` strictly below,
- that both `σ_pos` and `σ_neg` satisfy `pact`,
- and an order gap on the numeric embedding `m` (`m σ_neg < m σ_pos`). -/
class TwoStateNeuralNetwork {R U σ}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (NN : NeuralNetwork R U σ) where
  /-- Distinguished “positive” activation state. -/
  σ_pos : σ
  /-- Distinguished “negative” activation state. -/
  σ_neg : σ
  /-- Proof that the two distinguished activation states are distinct. -/
  h_pos_ne_neg : σ_pos ≠ σ_neg
  /-- Canonical index in `κ2 u` selecting the scalar threshold used by `fact`. -/
  θ0 : ∀ u : U, Fin (NN.κ2 u)
  /-- At or above threshold `θ0 u`, `fact` returns `σ_pos`. -/
  h_fact_pos :
    ∀ u (σcur : σ) (net : R) (θ : Vector R (NN.κ2 u)),
      (θ.get (θ0 u)) ≤ net → NN.fact u σcur net θ = σ_pos
  /-- Strictly below threshold `θ0 u`, `fact` returns `σ_neg`. -/
  h_fact_neg :
    ∀ u (σcur : σ) (net : R) (θ : Vector R (NN.κ2 u)),
      net < (θ.get (θ0 u)) → NN.fact u σcur net θ = σ_neg
  /-- `σ_pos` satisfies the activation predicate `pact`. -/
  h_pact_pos : NN.pact σ_pos
  /-- `σ_neg` satisfies the activation predicate `pact`. -/
  h_pact_neg : NN.pact σ_neg
  /-- Numeric embedding separates the two states: `m σ_neg < m σ_pos`. -/
  m_order : NN.m σ_neg < NN.m σ_pos

namespace TwoState
variable {R U σ : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! Concrete network families (three encodings). -/

/-- Helper canonical index for all concrete networks with κ2 = 1. -/
@[inline] def fin0 : Fin 1 := ⟨0, by decide⟩

/-- Standard symmetric Hopfield parameters with activations in {-1,1} (σ = R). -/
def SymmetricBinary (R : Type uR) (U : Type uU) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U R :=
{ Adj := fun u v => u ≠ v
  Ui := Set.univ
  Uo := Set.univ
  Uh := ∅
  hUi := by simp
  hUo := by simp
  hU := by simp
  hhio := by simp
  κ1 := fun _ => 1
  κ2 := fun _ => 1
  pw := fun W => W.IsSymm ∧ ∀ u, W u u = 0
  pact := fun a => a = 1 ∨ a = -1
  fnet := fun u row pred _ => ∑ v, if v ≠ u then row v * pred v else 0
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then 1 else -1
  fout := fun _ a => a
  m := id
  hpact := by
    classical
    intro W _ _ _ θ cur hcur u
    by_cases hth :
        (θ u).get fin0 ≤ ∑ v, if v ≠ u then W u v * cur v else 0
    · aesop
    · aesop }

/-- Type level two-value signum variant. -/
inductive Signum | pos | neg deriving DecidableEq

instance : Fintype Signum where
  elems := {Signum.pos, Signum.neg}
  complete := by intro x; cases x <;> simp

/-- Symmetric Hopfield parameters with σ = Signum. -/
def SymmetricSignum (R : Type uR) (U : Type uU) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U Signum :=
{ Adj := fun u v => u ≠ v
  Ui := Set.univ
  Uo := Set.univ
  Uh := ∅
  hUi := by simp
  hUo := by simp
  hU := by simp
  hhio := by simp
  κ1 := fun _ => 1
  κ2 := fun _ => 1
  pw := fun W => W.IsSymm ∧ ∀ u, W u u = 0
  fnet := fun u row pred _ => ∑ v, if v ≠ u then row v * pred v else 0
  pact := fun _ => True
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then Signum.pos else Signum.neg
  fout := fun _ s => match s with | .pos => (1 : R) | .neg => (-1 : R)
  m := fun s => match s with | .pos => (1 : R) | .neg => (-1 : R)
  hpact := by intro; simp }

/-- Zero / one network (σ ∈ {0,1}). -/
def ZeroOne (R : Type uR) (U : Type uU) [Field R] [LinearOrder R]
    [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U R :=
{ (SymmetricBinary R U) with
  pact := fun a => a = 0 ∨ a = 1
  fact := fun _ _ net θ => if θ.get fin0 ≤ net then 1 else 0
  hpact := by
    intro W _ _ σ θ cur hcur u
    by_cases hth :
        (θ u).get fin0 ≤ ∑ v, if v ≠ u then W u v * cur v else 0
    · simp [SymmetricBinary]; aesop
    · simp [SymmetricBinary]; aesop }

variable [DecidableEq U] [Fintype U] [Nonempty U]

instance instTwoStateSymmetricBinary :
  TwoStateNeuralNetwork (SymmetricBinary R U) where
  σ_pos := (1 : R); σ_neg := (-1 : R)
  h_pos_ne_neg := by
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    have hlt : (-1 : R) < 1 := hneg.trans h0
    exact (ne_of_lt hlt).symm
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hle; simp [SymmetricBinary, hle]
  h_fact_neg := by
    intro u σcur net θ hlt
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [SymmetricBinary, this]
  h_pact_pos := by left; rfl
  h_pact_neg := by right; rfl
  m_order := by
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    exact hneg.trans h0

instance instTwoStateSignum :
  TwoStateNeuralNetwork (SymmetricSignum R U) where
  σ_pos := Signum.pos; σ_neg := Signum.neg
  h_pos_ne_neg := by intro h; cases h
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hn
    change (if θ.get fin0 ≤ net then Signum.pos else Signum.neg) = Signum.pos
    simp [hn]
  h_fact_neg := by
    intro u σcur net θ hlt
    change (if θ.get fin0 ≤ net then Signum.pos else Signum.neg) = Signum.neg
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [this]
  h_pact_pos := by trivial
  h_pact_neg := by trivial
  m_order := by
    -- `m` maps pos ↦ 1, neg ↦ -1
    have h0 : (0 : R) < 1 := zero_lt_one
    have hneg : (-1 : R) < 0 := by simp
    simp [SymmetricSignum]

instance instTwoStateZeroOne :
  TwoStateNeuralNetwork (ZeroOne R U) where
  σ_pos := (1 : R); σ_neg := (0 : R)
  h_pos_ne_neg := one_ne_zero
  θ0 := fun _ => fin0
  h_fact_pos := by
    intro u σcur net θ hn
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 1
    simp [hn]
  h_fact_neg := by
    intro u σcur net θ hlt
    change (if θ.get fin0 ≤ net then (1 : R) else 0) = 0
    have : ¬ θ.get fin0 ≤ net := not_le.mpr hlt
    simp [this]
  h_pact_pos := by right; rfl
  h_pact_neg := by left; rfl
  m_order := by
    -- m = id, so goal is 0 < 1
    simp [ZeroOne, SymmetricBinary]

/-- Scale between numeric embeddings of the two states (pushed along f). -/
def scale
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) : ℝ :=
  f (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))) -
    f (NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN)))

/-- Generalized scale in an arbitrary target ring S. -/
def scaleS
    {S} [Ring S] {F} [FunLike F R S]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] (f : F) : S :=
  f (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))) -
    f (NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN)))

@[simp] lemma scaleS_apply_ℝ
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN] (f : F) :
    scaleS (NN:=NN) (f:=f) = scale (NN:=NN) (f:=f) := rfl

@[simp] lemma scale_binary (f : R →+* ℝ) :
    scale (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) (f:=f) = f 2 := by
  -- σ_pos = 1, σ_neg = -1, m = id
  unfold scale
  simp [instTwoStateSymmetricBinary, SymmetricBinary, sub_neg_eq_add, one_add_one_eq_two]
  rw [@map_ofNat]

@[simp] lemma scale_zeroOne (f : R →+* ℝ) :
    scale (R:=R) (U:=U) (σ:=R) (NN:=ZeroOne R U) (f:=f) = f 1 := by
  -- σ_pos = 1, σ_neg = 0, m = id
  unfold scale
  simp [instTwoStateZeroOne, ZeroOne, SymmetricBinary]

/-- Logistic function used for Gibbs probabilities. -/
noncomputable def logisticProb (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

lemma logisticProb_nonneg (x : ℝ) : 0 ≤ logisticProb x := by
  unfold logisticProb
  have hx : 0 < Real.exp (-x) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-x) := by linarith
  exact div_nonneg zero_le_one hden.le

lemma logisticProb_le_one (x : ℝ) : logisticProb x ≤ 1 := by
  unfold logisticProb
  have hx : 0 < Real.exp (-x) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-x) := by linarith
  have : 1 ≤ 1 + Real.exp (-x) := by
    linarith
  simpa using (div_le_one hden).mpr this

/-- Probability P(σ_u = σ_pos) for one Gibbs update. -/
noncomputable def probPos
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) : ℝ :=
  let L := (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  let κ := scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)
  logisticProb (κ * (f L) * (β T))

lemma probPos_nonneg
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    0 ≤ probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u := by
  unfold probPos; apply logisticProb_nonneg

lemma probPos_le_one
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u ≤ 1 := by
  unfold probPos; apply logisticProb_le_one

/-- Force neuron u to σ_pos. -/
def updPos {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U) : NN.State :=
{ act := Function.update s.act u (TwoStateNeuralNetwork.σ_pos (NN:=NN))
, hp := by
    intro v
    by_cases h : v = u
    · subst h; simpa using TwoStateNeuralNetwork.h_pact_pos (NN:=NN)
    · simpa [Function.update, h] using s.hp v }

/-- Force neuron u to σ_neg. -/
def updNeg {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U) : NN.State :=
{ act := Function.update s.act u (TwoStateNeuralNetwork.σ_neg (NN:=NN))
, hp := by
    intro v
    by_cases h : v = u
    · subst h; simpa using TwoStateNeuralNetwork.h_pact_neg (NN:=NN)
    · simpa [Function.update, h] using s.hp v }

/-- One–site Gibbs update kernel (PMF). -/
noncomputable def gibbsUpdate
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    PMF (NN.State) := by
  let pPos := probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u      -- probability in ℝ
  have h_nonneg : 0 ≤ pPos :=
    probPos_nonneg (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u
  have h_le : pPos ≤ 1 :=
    probPos_le_one (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u
  -- Cast to ℝ≥0 for PMF.bernoulli
  let pPosNN : ℝ≥0 := ⟨pPos, h_nonneg⟩
  have h_le' : pPosNN ≤ 1 := by
    change (pPosNN : ℝ) ≤ 1
    simpa using h_le
  exact
    PMF.bernoulli pPosNN h_le' >>= fun b =>
      if b then PMF.pure (updPos (s:=s) (u:=u)) else PMF.pure (updNeg (s:=s) (u:=u))

/-- Zero–temperature deterministic (threshold) update at site u. -/
def zeroTempDet
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (s : NN.State) (u : U) : NN.State :=
  let net := s.net p u
  let θ := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  if h : θ ≤ net then
    (have _ := h; updPos (s:=s) (u:=u))
  else
    (have _ := h; updNeg (s:=s) (u:=u))

/-- Gibbs sweep auxiliary function. -/
noncomputable def gibbsSweepAux
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) :
    List U → NN.State → PMF NN.State
  | [],       s => PMF.pure s
  | u :: us, s =>
      gibbsUpdate (NN:=NN) f p T s u >>= fun s' =>
        gibbsSweepAux f p T us s'

@[simp] lemma gibbsSweepAux_nil
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (s : NN.State) :
    gibbsSweepAux (NN:=NN) f p T [] s = PMF.pure s := rfl

@[simp] lemma gibbsSweepAux_cons
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (f : F) (p : Params NN) (T : Temperature) (u : U) (us : List U) (s : NN.State) :
    gibbsSweepAux (NN:=NN) f p T (u :: us) s =
      gibbsUpdate (NN:=NN) f p T s u >>= fun s' =>
        gibbsSweepAux (NN:=NN) f p T us s' := rfl

/-- Sequential Gibbs sweep over a list of sites, head applied first. -/
noncomputable def gibbsSweep
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (order : List U) (p : Params NN) (T : Temperature) (f : F)
    (s0 : NN.State) : PMF NN.State :=
  gibbsSweepAux (NN:=NN) f p T order s0

@[simp] lemma gibbsSweep_nil
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (T : Temperature) (f : F) (s0 : NN.State) :
    gibbsSweep (NN:=NN) ([] : List U) p T f s0 = PMF.pure s0 := rfl

lemma gibbsSweep_cons
    {F} [FunLike F R ℝ]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (u : U) (us : List U) (p : Params NN) (T : Temperature) (f : F) (s0 : NN.State) :
    gibbsSweep (NN:=NN) (u :: us) p T f s0 =
      (gibbsUpdate (NN:=NN) f p T s0 u) >>= fun s =>
        gibbsSweep (NN:=NN) us p T f s := rfl

@[simp] lemma probPos_nonneg_apply_binary
    (f : R →+* ℝ) (p : Params (SymmetricBinary R U)) (T : Temperature)
    (s : (SymmetricBinary R U).State) (u : U) :
    0 ≤ probPos (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u :=
  probPos_nonneg (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u

@[simp] lemma probPos_le_one_apply_binary
    (f : R →+* ℝ) (p : Params (SymmetricBinary R U)) (T : Temperature)
    (s : (SymmetricBinary R U).State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u ≤ 1 :=
  probPos_le_one (R:=R) (U:=U) (σ:=R) (NN:=SymmetricBinary R U) f p T s u

/-- **Energy specification bundling a global energy and a local field**.

This abstracts the thermodynamic view at the `R` level :
- `E p s` is the global energy of state `s` under parameters `p`;
- `localField p s u` is the local field at site `u` in state `s`.
-  The specification `localField_spec` connects the local field to the
  network primitives, and `flip_energy_relation` states the fundamental
  relation between energy differences and local fields.
Together these properties connect energy differences
to local fields and underpin the Gibbs/zero–temperature analysis. -/
structure EnergySpec
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] where
  /-- Global energy function `E p s`. -/
  E : Params NN → NN.State → R
  /-- Local field `L = localField p s u` at site `u`. -/
  localField : Params NN → NN.State → U → R
  /-- Specification tying the abstract `localField` to the network primitives:
      `localField p s u = s.net p u - (p.θ u).get (θ0 u)`. -/
  localField_spec :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      localField p s u =
        (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  /-- Fundamental flip–energy relation: the energy difference between the
      `updPos` and `updNeg` flips at `u` equals `- scale f * f(localField p s u)`,
      when pushed along a ring hom `f : R →+* ℝ`. -/
  flip_energy_relation :
    ∀ (f : R →+* ℝ)
      (p : Params NN) (s : NN.State) (u : U),
      let sPos := updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let sNeg := updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      f (E p sPos - E p sNeg) =
        - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
          f (localField p s u)

/-- A simplified energy specification carrying the same data as `EnergySpec`,
with the flip relation stated using inlined `updPos`/`updNeg`. -/
structure EnergySpec'
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq U]
    (NN : NeuralNetwork R U σ) [TwoStateNeuralNetwork NN] where
  /-- Global energy function `E p s`. -/
  E : Params NN → NN.State → R
  /-- Local field `L = localField p s u` at site `u`. -/
  localField : Params NN → NN.State → U → R
  /-- Specification tying `localField` to the network primitives:
      `localField p s u = s.net p u - (p.θ u).get (θ0 u)`. -/
  localField_spec :
    ∀ (p : Params NN) (s : NN.State) (u : U),
      localField p s u =
        (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  /-- Fundamental flip–energy relation pushed along a ring hom `f : R →+* ℝ`:
      `f (E p (updPos s u) - E p (updNeg s u))
        = - scale f * f (localField p s u)`. -/
  flip_energy_relation :
    ∀ (f : R →+* ℝ) (p : Params NN) (s : NN.State) (u : U),
      f (E p (updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u))
           - E p (updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u))) =
        - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) * f (localField p s u)

namespace EnergySpec
variable {NN : NeuralNetwork R U σ}
variable [TwoStateNeuralNetwork NN]

lemma flip_energy_rel'
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : TwoState.EnergySpec (NN := NN)) (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  -- we build a bundled ring hom from f; its coercion is definitionally f
  let f_hom : R →+* ℝ :=
  { toMonoidHom :=
    { toFun := f
      map_one' := map_one f
      map_mul' := map_mul f }
    map_zero' := map_zero f
    map_add' := map_add f }
  have h := ES.flip_energy_relation f_hom p s u
  simpa [ES.localField_spec] using h

lemma probPos_eq_of_energy
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : EnergySpec (NN := NN)) (f : F) (p : Params NN) (T : Temperature)
    (s : NN.State) (u : U) :
    probPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) f p T s u =
      let sPos := updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let sNeg := updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) (s:=s) (u:=u)
      let Δ := f (ES.E p sPos - ES.E p sNeg)
      logisticProb (- Δ * (β T)) := by
  unfold probPos
  have hΔ :=
    ES.flip_energy_rel' (f:=f) p s u
  simp [hΔ, logisticProb]

end EnergySpec

namespace EnergySpec'
variable {NN : NeuralNetwork R U σ}
variable [TwoStateNeuralNetwork NN]

/-- Convert an `EnergySpec` to an `EnergySpec'`. -/
def ofOld
    (ES : TwoState.EnergySpec (NN := NN)) : EnergySpec' (NN:=NN) :=
{ E := ES.E
, localField := ES.localField
, localField_spec := ES.localField_spec
, flip_energy_relation := by
    intro f p s u
    simpa using (ES.flip_energy_relation f p s u) }

lemma flip_energy_rel'
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ]
    (ES : EnergySpec' (NN := NN)) (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  -- Build a bundled ring hom from f; its coercion is definitionally f
  let f_hom : R →+* ℝ :=
  { toMonoidHom :=
    { toFun := f
      map_one' := map_one f
      map_mul' := map_mul f }
    map_zero' := map_zero f
    map_add' := map_add f }
  have h := ES.flip_energy_relation f_hom p s u
  simpa [ES.localField_spec] using h

end EnergySpec'

lemma EnergySpec.flip_energy_rel''
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (ES : TwoState.EnergySpec (NN := NN))
    {F} [FunLike F R ℝ] [RingHomClass F R ℝ] (f : F)
    (p : Params NN) (s : NN.State) (u : U) :
    f (ES.E p (updPos (NN:=NN) s u) - ES.E p (updNeg (NN:=NN) s u)) =
      - (scale (R:=R) (U:=U) (σ:=σ) (NN:=NN) (f:=f)) *
        f ((s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)) := by
  refine (EnergySpec'.flip_energy_rel'
            (EnergySpec'.ofOld (NN:=NN) ES) (f:=f) p s u)

end TwoState

open Finset Matrix NeuralNetwork State Constants Temperature Filter Topology
open scoped ENNReal NNReal BigOperators
open NeuralNetwork
namespace TwoState


lemma updPos_eq_self_of_act_pos
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U)
    (h : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN)) :
    updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updPos, Function.update, h]
  · simp [updPos, Function.update, hv]

/-- Helper: if the current activation at `u` is already `σ_neg`, `updNeg` is identity. -/
lemma updNeg_eq_self_of_act_neg
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (s : NN.State) (u : U)
    (h : s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN)) :
    updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updNeg, Function.update, h]
  · simp [updNeg, Function.update, hv]

/-- Classification of a single asynchronous update at site `u`:
`Up` equals `updPos` if `θ ≤ net`, else `updNeg`. (Explicit parameters to
stabilize elaboration.) -/
lemma Up_eq_updPos_or_updNeg
    {R U σ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork NN]
    (p : Params NN) (s : NN.State) (u : U) :
    let net := s.net p u
    let θ   := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
    s.Up p u =
      (if θ ≤ net then updPos (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u
       else updNeg (R:=R) (U:=U) (σ:=σ) (NN:=NN) s u) := by
  intro net θ
  ext v
  by_cases hv : v = u
  · subst hv
    unfold NeuralNetwork.State.Up
    simp only
    by_cases hθle : θ ≤ net
    · have hpos :=
        TwoStateNeuralNetwork.h_fact_pos (NN:=NN) v (s.act v) net (p.θ v) hθle
      have : NN.fact v (s.act v)
          (NN.fnet v (p.w v) (fun w => s.out w) (p.σ v))
          (p.θ v) = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
        simpa [NeuralNetwork.State.net] using hpos
      simp [updPos, Function.update, this, hθle]
      aesop
    · have hlt : net < θ := lt_of_not_ge hθle
      have hneg :=
        TwoStateNeuralNetwork.h_fact_neg (NN:=NN) v (s.act v) net (p.θ v) hlt
      have : NN.fact v (s.act v)
          (NN.fnet v (p.w v) (fun w => s.out w) (p.σ v))
          (p.θ v) = TwoStateNeuralNetwork.σ_neg (NN:=NN) := by
        simpa [NeuralNetwork.State.net] using hneg
      simp [updNeg, Function.update, this, hθle]
      aesop
  · unfold NeuralNetwork.State.Up
    simp_rw [hv, updPos, updNeg]; simp [Function.update]
    aesop

end TwoState
namespace TwoState.EnergySpec'

/-- Given an energy difference identity
  E sPos - E sNeg = - κ * L   with κ ≥ 0,
we deduce the two directional inequalities depending on the sign of L. -/
lemma energy_order_from_flip_id
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (NN := NN))
    {p : Params NN}
    {κ L : ℝ} {sPos sNeg : NN.State}
    (hdiff : spec.E p sPos - spec.E p sNeg = -κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → spec.E p sPos ≤ spec.E p sNeg) ∧
    (L ≤ 0 → spec.E p sNeg ≤ spec.E p sPos) := by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hDiffLe : spec.E p sPos - spec.E p sNeg ≤ 0 := by
      rw [hdiff]; simp only [neg_mul, Left.neg_nonpos_iff]; exact hκL
    exact sub_nonpos.mp hDiffLe
  · intro hL
    have hrev : spec.E p sNeg - spec.E p sPos = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have : spec.E p sNeg - spec.E p sPos ≤ 0 := by simpa [hrev] using hκL
    exact sub_nonpos.mp this

end EnergySpec'
end TwoState
namespace TwoState

section ConcreteLyapunov
variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

-- Note: The following lemmas are specialized for `SymmetricBinary ℝ U`
-- to simplify the proof development by avoiding universe polymorphism.

lemma updPos_eq_self_of_act_pos_binary
    (s : (SymmetricBinary ℝ U).State) (u : U)
    (h : s.act u = 1) :
    updPos (NN:=SymmetricBinary ℝ U) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updPos, Function.update, h, instTwoStateSymmetricBinary]
  · simp [updPos, Function.update, hv]

lemma updNeg_eq_self_of_act_neg_binary
    (s : (SymmetricBinary ℝ U).State) (u : U)
    (h : s.act u = -1) :
    updNeg (NN:=SymmetricBinary ℝ U) s u = s := by
  ext v
  by_cases hv : v = u
  · subst hv; simp [updNeg, Function.update, h, instTwoStateSymmetricBinary]
  · simp [updNeg, Function.update, hv]

lemma Up_eq_updPos_or_updNeg_binary
    (p : Params (SymmetricBinary ℝ U)) (s : (SymmetricBinary ℝ U).State) (u : U) :
    let net := s.net p u
    let θ   := (p.θ u).get fin0
    s.Up p u =
      (if θ ≤ net
       then updPos (NN:=SymmetricBinary ℝ U) s u
       else updNeg (NN:=SymmetricBinary ℝ U) s u) := by
  intro net θ
  simpa [net, θ] using
    (TwoState.Up_eq_updPos_or_updNeg
        (R:=ℝ) (U:=U) (σ:=ℝ)
        (NN:=SymmetricBinary ℝ U) p s u)

lemma energy_order_from_flip_id_binary
    (spec : EnergySpec' (NN := SymmetricBinary ℝ U))
    {p : Params (SymmetricBinary ℝ U)}
    {κ L : ℝ} {sPos sNeg : (SymmetricBinary ℝ U).State}
    (hdiff : spec.E p sPos - spec.E p sNeg = -κ * L)
    (hκ : 0 ≤ κ) :
    (0 ≤ L → spec.E p sPos ≤ spec.E p sNeg) ∧
    (L ≤ 0 → spec.E p sNeg ≤ spec.E p sPos) := by
  constructor
  · intro hL
    have hκL : 0 ≤ κ * L := mul_nonneg hκ hL
    have hsub : spec.E p sPos - spec.E p sNeg ≤ 0 := by
      rw [hdiff, neg_mul]
      exact neg_nonpos.mpr hκL
    exact sub_nonpos.mp hsub
  · intro hL
    have hκL : κ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ hL
    have hrev : spec.E p sNeg - spec.E p sPos = κ * L := by
      have := congrArg Neg.neg hdiff
      simpa [neg_sub, neg_mul, neg_neg] using this
    have hsub : spec.E p sNeg - spec.E p sPos ≤ 0 := by
      rw [hrev]; exact hκL
    exact sub_nonpos.mp hsub

/-- Lyapunov (energy non‑increase) at a single site for `SymmetricBinary` networks. -/
lemma energy_is_lyapunov_at_site_binary
    (spec : EnergySpec' (NN := SymmetricBinary ℝ U))
    (p : Params (SymmetricBinary ℝ U)) (s : (SymmetricBinary ℝ U).State) (u : U)
    (hcur : s.act u = 1 ∨ s.act u = -1) :
    spec.E p (s.Up p u) ≤ spec.E p s := by
  set sPos := updPos (NN:=SymmetricBinary ℝ U) s u
  set sNeg := updNeg (NN:=SymmetricBinary ℝ U) s u
  set net := s.net p u
  set θ   := (p.θ u).get fin0
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  -- Get the energy difference relation from the spec
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by simp [L, net, θ, spec.localField_spec]; rfl
  have hdiff : spec.E p sPos - spec.E p sNeg =
      - (scale (NN := SymmetricBinary ℝ U) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  -- Define κ and prove it's non-negative
  set κ := scale (NN:=SymmetricBinary ℝ U) (f:=fid)
  have hκ_pos : 0 < κ := by aesop--simp [scale_binary, map_ofNat]
  have hκ_nonneg : 0 ≤ κ := hκ_pos.le
  -- Get the ordering implications from the energy difference
  have hOrder := energy_order_from_flip_id_binary spec hdiff hκ_nonneg
  -- Relate the abstract update `Up` to concrete `updPos`/`updNeg`
  have hUp_cases := Up_eq_updPos_or_updNeg_binary p s u
  -- Case split on the threshold condition
  by_cases hθle : θ ≤ net
  · -- Case 1: net ≥ θ, so update goes to sPos
    have hUp_cases_eval := hUp_cases
    simp [net, θ, hθle, sPos, sNeg] at hUp_cases_eval
    rw [hUp_cases_eval]
    cases hcur with
    | inl h_is_pos =>
      rw [updPos_eq_self_of_act_pos_binary s u h_is_pos]
    | inr h_is_neg =>
      have hL_nonneg : 0 ≤ L := by simpa [L] using sub_nonneg.mpr hθle
      have hs : s = sNeg := (updNeg_eq_self_of_act_neg_binary s u h_is_neg).symm
      have hLE : spec.E p sPos ≤ spec.E p sNeg := hOrder.left hL_nonneg
      simp_rw [hs]
      exact
        le_of_eq_of_le (congrArg (spec.E p) (congrFun (congrArg updPos (id (Eq.symm hs))) u)) hLE
  · -- Case 2: net < θ, so update goes to sNeg
    have hUp_cases_eval := hUp_cases
    simp [net, θ, hθle, sPos, sNeg] at hUp_cases_eval
    rw [hUp_cases_eval]
    cases hcur with
    | inl h_is_pos =>
      have hL_nonpos : L ≤ 0 := by simpa [L] using (lt_of_not_ge hθle).le
      have hs : s = sPos := (updPos_eq_self_of_act_pos_binary s u h_is_pos).symm
      have hLE : spec.E p sNeg ≤ spec.E p sPos := hOrder.2 hL_nonpos
      simp_rw [hs]
      exact
        le_of_eq_of_le (congrArg (spec.E p) (congrFun (congrArg updNeg (id (Eq.symm hs))) u)) hLE
    | inr h_is_neg =>
      rw [updNeg_eq_self_of_act_neg_binary s u h_is_neg]

end ConcreteLyapunov
namespace EnergySpec'
open TwoState

/-- General (non-binary–specialized) Lyapunov single–site energy descent lemma. -/
lemma energy_is_lyapunov_at_site
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R := ℝ) (NN := NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN)) :
    spec.E p (s.Up p u) ≤ spec.E p s := by
  set sPos := updPos (NN:=NN) s u
  set sNeg := updNeg (NN:=NN) s u
  set net  := s.net p u
  set θ    := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by
    simp [L, net, θ, spec.localField_spec]
  have hdiff :
      spec.E p sPos - spec.E p sNeg
        = - (scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  set κ := scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)
  have hm := TwoStateNeuralNetwork.m_order (NN:=NN)
  have hκpos : 0 < κ := by
    simp [κ, scale]
    aesop
  have hκ : 0 ≤ κ := hκpos.le
  have hOrder :=
    TwoState.EnergySpec'.energy_order_from_flip_id
      (NN:=NN) (spec:=spec) (p:=p) (κ:=κ) (L:=L)
      (sPos:=sPos) (sNeg:=sNeg) hdiff hκ
  have hup := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
  by_cases hθle : θ ≤ net
  · have hUpPos : s.Up p u = sPos := by
      simpa [net, θ, hθle] using hup
    cases hcur with
    | inl hpos =>
        have hFixed : sPos = s := by
          have h := TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hpos
          simpa [sPos] using h
        simp [hUpPos, hFixed]
    | inr hneg =>
        have hEqNeg : sNeg = s := by
          have h := TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hneg
          simpa [sNeg] using h
        have hL : 0 ≤ L := by
          have : θ ≤ net := hθle
          simpa [L] using sub_nonneg.mpr this
        have hLE := hOrder.left hL
        simp [hUpPos, hEqNeg]
        aesop
  · have hnetlt : net < θ := lt_of_not_ge hθle
    have hLle : L ≤ 0 := by
      have : net - θ < 0 := sub_lt_zero.mpr hnetlt
      exact this.le
    have hUpNeg : s.Up p u = sNeg := by
      have hnot : ¬ θ ≤ net := hθle
      simpa [net, θ, hnot] using hup
    cases hcur with
    | inl hpos =>
        have hEqPos : sPos = s := by
          have h := TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hpos
          simpa [sPos] using h
        have hLE := hOrder.right hLle
        simp [hUpNeg, hEqPos]
        aesop
    | inr hneg =>
        have hFixed : sNeg = s := by
          have h := TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hneg
          simpa [sNeg] using h
        simp [hUpNeg, hFixed]

/-- Wrapper (argument order variant). -/
lemma energy_is_lyapunov_at_site'
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R := ℝ) (NN := NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN)) :
    spec.E p (s.Up p u) ≤ spec.E p s :=
  energy_is_lyapunov_at_site (NN:=NN) (spec:=spec) p s u hcur

/-- Lyapunov (energy non‑increase) at a single site (completed proof).
Uses `energy_order_from_flip_id` and the flip relation with the identity hom. -/
lemma energy_is_lyapunov_at_site''
    {U σ} [Fintype U] [DecidableEq U]
    (NN : NeuralNetwork ℝ U σ) [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R := ℝ) (NN := NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN)) :
    spec.E p (NeuralNetwork.State.Up s p u) ≤ spec.E p s := by
  set sPos := updPos (NN:=NN) s u
  set sNeg := updNeg (NN:=NN) s u
  set net  := s.net p u
  set θ    := (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN:=NN) u)
  set L : ℝ := net - θ
  let fid : ℝ →+* ℝ := RingHom.id _
  have hflip := spec.flip_energy_relation fid p s u
  have hlocal : spec.localField p s u = L := by
    simp [L, net, θ, spec.localField_spec]
  have hdiff :
      spec.E p sPos - spec.E p sNeg =
        - (scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)) * L := by
    simpa [sPos, sNeg, hlocal] using hflip
  set κ := scale (R:=ℝ) (U:=U) (σ:=σ) (NN:=NN) (f:=fid)
  have hκpos : 0 < κ := by
    have hmo := TwoStateNeuralNetwork.m_order (NN:=NN)
    have : 0 < (NN.m (TwoStateNeuralNetwork.σ_pos (NN:=NN))
              - NN.m (TwoStateNeuralNetwork.σ_neg (NN:=NN))) := sub_pos.mpr hmo
    simpa [κ, scale, fid, RingHom.id_apply]
  have hκ : 0 ≤ κ := hκpos.le
  have hOrder :=
    energy_order_from_flip_id
      (NN:=NN) (spec:=spec) (p:=p) (κ:=κ) (L:=L)
      (sPos:=sPos) (sNeg:=sNeg) hdiff hκ
  have hup := TwoState.Up_eq_updPos_or_updNeg (NN:=NN) p s u
  by_cases hθle : θ ≤ net
  · have hUpPos : s.Up p u = sPos := by
      simpa [net, θ, hθle] using hup
    cases hcur with
    | inl hPos =>
        have hs : sPos = s :=
          TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hPos
        have htriv : spec.E p sPos ≤ spec.E p sPos := le_rfl
        simp [hUpPos, hs]
    | inr hNeg =>
        have hs : sNeg = s :=
          TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hNeg
        have hL : 0 ≤ L := by
          have : θ ≤ net := hθle
          simpa [L] using sub_nonneg.mpr this
        have hLE : spec.E p sPos ≤ spec.E p sNeg := hOrder.left hL
        simp [hUpPos, hs]
        aesop
  · have hLt : net < θ := lt_of_not_ge hθle
    have hLle : L ≤ 0 := (sub_lt_zero.mpr hLt).le
    have hUpNeg : s.Up p u = sNeg := by
      have hnot : ¬ θ ≤ net := hθle
      simpa [net, θ, hnot] using hup
    cases hcur with
    | inl hPos =>
        have hs : sPos = s :=
          TwoState.updPos_eq_self_of_act_pos (NN:=NN) s u hPos
        have hLE : spec.E p sNeg ≤ spec.E p sPos := hOrder.right hLle
        simp [hUpNeg, hs]
        aesop
    | inr hNeg =>
        have hs : sNeg = s :=
          TwoState.updNeg_eq_self_of_act_neg (NN:=NN) s u hNeg
        have htriv : spec.E p sNeg ≤ spec.E p sNeg := le_rfl
        simp [hUpNeg, hs]

/-- Restated helper with identical conclusion (wrapper). -/
lemma energy_is_lyapunov_at_site'''
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : EnergySpec' (R := ℝ) (NN := NN))
    (p : Params NN) (s : NN.State) (u : U)
    (hcur : s.act u = TwoStateNeuralNetwork.σ_pos (NN := NN) ∨
            s.act u = TwoStateNeuralNetwork.σ_neg (NN := NN)) :
    spec.E p (NeuralNetwork.State.Up s p u) ≤ spec.E p s :=
  energy_is_lyapunov_at_site (NN:=NN) (spec:=spec) p s u hcur

end EnergySpec'
end TwoState
