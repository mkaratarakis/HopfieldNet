# Hopfield Network Formalization API

## Core Architecture

### Base Structures
```lean
-- Universe polymorphic neural network
NeuralNetwork (R : Type uR) (U : Type uU) (σ : Type uσ) [Zero R] extends Digraph U
  - Ui/Uo/Uh: Set U (input/output/hidden neurons)
  - κ1/κ2: U → ℕ (vector dimensions)
  - fnet: ∀u, (U→R) → (U→R) → Vector R (κ1 u) → R
  - fact: ∀u, σ → R → Vector R (κ2 u) → σ
  - fout: ∀_, σ → R; m: σ → R; pact: σ → Prop; pw: Matrix U U R → Prop
  - hpact: closure under updates

Params (NN) := {w: Matrix U U R, hw: adjacency constraint, hw': pw w, σ/θ: parameter vectors}

State (NN) := {act: U → σ, hp: ∀u, pact (act u)}
  - out/net: derived functions
  - Up: single-site update s.Up p u
  - seqStates: iterated updates following useq: ℕ → U
  - isStable: ∀u, (Up s p u).act u = s.act u
```


## Core.lean -the certified specification

### Original computable Hopfield instance
```lean
-- Universe-polymorphic definition (the root specification)
HopfieldNetwork (R : Type uR) (U : Type uU) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq U] [Fintype U] [Nonempty U] : NeuralNetwork R U R
  := { Adj := λu v => u ≠ v                    -- fully connected
     , Ui/Uo := Set.univ; Uh := ∅              -- no hidden layer
     , κ1 := λ_ => 1; κ2 := λ_ => 1            -- scalar parameters
     , pact := λa => a = 1 ∨ a = -1            -- binary activations {±1}
     , fnet := λu row pred _ => ∑v, if v ≠ u then row v * pred v else 0  -- local field
     , fact := λ_ _ net θ => if θ.get fin0 ≤ net then 1 else -1          -- threshold
     , fout := id; m := id                     -- identity output/embedding
     , pw := λW => W.IsSymm ∧ ∀u, W u u = 0   -- symmetric, zero diagonal
     , hpact := ... }                          -- closure proof

-- Core energy function (the original Hamiltonian)
E (s : HopfieldNetwork.State) : R := s.Ew wθ + s.Eθ wθ
  where Ew := -1/2 * (∑u, ∑v∈{v|v≠u}, s.Wact wθ u v)    -- interaction energy
        Eθ := ∑u, θ'(wθ.θ u) * s.act u                    -- field energy
        Wact u v := wθ.w u v * s.act u * s.act v          -- pairwise interaction

-- Fundamental energy difference lemma (the flip-energy formula)
E_final_Form : (s.Up wθ u).E wθ - s.E wθ =
  (s.act u - (s.Up wθ u).act u) * ((∑v∈{v|v≠u}, wθ.w u v * s.act v) - θ'(wθ.θ u))
```

### Certified Convergence
```lean
-- Well-founded lexicographic ordering on (Energy, Pluses)
stateLt (s1 s2 : State' wθ) : Prop :=
  s1.E wθ < s2.E wθ ∨ (s1.E wθ = s2.E wθ ∧ s2.pluses < s1.pluses)

instance StatePartialOrder : PartialOrder (State' wθ) := ...
instance wellFoundedRelation [Fintype State] : WellFounded (InvImage ...) :=
  Finite.wellFounded_of_trans_of_irrefl

-- monotonicity lemmas
energy_diff_leq_zero (hc : (s.Up wθ u).act u ≠ s.act u) : (s.Up wθ u).E wθ ≤ s.E wθ
energy_lt_zero_or_pluses_increase (hc : change) :
  (s.Up wθ u).E wθ < s.E wθ ∨ ((s.Up wθ u).E wθ = s.E wθ ∧ s.pluses < (s.Up wθ u).pluses)

update_less' (s : State' wθ) : Up' s u ≠ s → Up' s u < s   -- strict descent
update_le (s : State' wθ) : Up' s u ≤ s                   -- weak monotonicity

-- Main convergence theorem
HopfieldNet_convergence_fair : ∀ (useq : ℕ → U), fair useq →
  ∃ N, (seqStates' s useq N).isStable wθ

HopfieldNet_convergence_cyclic : ∀ (useq : ℕ → U), cyclic useq →
  ∃ N, N ≤ cardU * (2^cardU) ∧ (seqStates' s useq N).isStable wθ

-- Computable stabilization functions
HopfieldNet_stabilize (wθ : Params) (s : State' wθ) (useq : ℕ → U) (hf : fair useq) : State' wθ
  := seqStates' s useq (Nat.find (HopfieldNet_convergence_fair s useq hf))

HopfieldNet_conv_time_steps : ℕ := Nat.find (HopfieldNet_convergence_cyclic ...)
```

### Matrix lemmas
```lean
-- Quadratic form manipulation (core algebraic engine)
quadraticForm (M : Matrix ι ι R) (x : ι → R) : R := ∑j, x j * (M.mulVec x) j

mulVec_update_single (M : Matrix) (x : ι → R) (i : ι) (v : R) :
  (M.mulVec (update x i v)) j = (M.mulVec x) j + M j i * (v - x i)

quadratic_form_update_diag_zero {M : Matrix} (hSymm : M.IsSymm) (hDiag : ∀j, M j j = 0)
  (x : ι → R) (i : ι) (v : R) :
  quadraticForm M (update x i v) - quadraticForm M x = (v - x i) * 2 * (M.mulVec x) i

-- Sum splitting utilities
sum_split_at (f : ι → R) (i : ι) : (∑j, f j) = f i + ∑j∈(univ.erase i), f j
```

### Hebbian learning (Certified pattern storage)
```lean
Hebbian {m} (ps : Fin m → HopfieldNetwork.State) : Params HopfieldNetwork :=
  { w := ∑k, outerProduct (ps k) (ps k) - (m : R) • (1 : Matrix U U R)
  , θ u := ⟨#[0], rfl⟩
  , σ _ := Vector.emptyWithCapacity 0
  , hw := ... -- diagonal constraint satisfied
  , hw' := ... } -- symmetry satisfied

-- Hebbian property (exact storage for orthogonal patterns)
patterns_pairwise_orthogonal {m} (ps : Fin m → State)
  (horth : ∀{i j}, i ≠ j → dotProduct (ps i).act (ps j).act = 0) :
  ∀j, ((Hebbian ps).w).mulVec (ps j).act = ((cardU : R) - (m : R)) • (ps j).act

-- Stability theorem (stored patterns are fixed points)
Hebbian_stable {m} (hm : m < cardU) (ps : Fin m → State) (j : Fin m)
  (horth : orthogonality condition) : isStable (Hebbian ps) (ps j)
```

### Computable verification framework
```lean
-- Decidable instances for algorithmic verification
instance decidableEqState : DecidableEq HopfieldNetwork.State := ...
instance (s : State' wθ) : Decidable (isStable wθ s) := Fintype.decidableForallFintype

-- Finite state space (enables exhaustive analysis)
stateToNeurActMap_equiv' : HopfieldNetwork.State ≃ (U → ({1,-1} : Finset R))
instance : Fintype HopfieldNetwork.State := Fintype.ofEquiv _ (equiv.symm)

-- Cardinality bound (exponential in network size)
num_of_states_card : card HopfieldNetwork.State = 2^(cardU)

-- Convergence time bounds (polynomial in state space)
initial_state_bound : num_of_states_less (seqStates' s useq 0) ≤ 2^(cardU)
```

### Core vs Generalized Relationship
```lean
-- The generalization hierarchy:
HopfieldNetwork R U                              -- Core: computable {±1} networks
  ↓ (abstraction)
TwoStateNeuralNetwork NN                         -- General: abstract two-state interface
  ↓ (concrete instances)
SymmetricBinary R U ≃ HopfieldNetwork R U        -- Equivalence to original
SymmetricSignum R U, ZeroOne R U                 -- Additional encodings
  ↓ (energy specification)
EnergySpec' NN                                   -- Abstract: energy-field relation
  ↓ (Hamiltonian bridge)
IsHamiltonian NN                                 -- Physics: statistical mechanics
  ↓ (canonical ensemble)
CanonicalEnsemble NN.State                       -- Thermodynamics: full statistical theory

-- All generalizations inherit correctness from this certified specification:
instance IsStrictlyHamiltonian_of_TwoState_EnergySpec :
  Core convergence proof ⟹ Abstract convergence framework

instance IsHamiltonian_of_EnergySpec' :
  Core energy manipulation ⟹ General statistical mechanics

symmetricBinaryEnergySpec : EnergySpec' (SymmetricBinary R U) :=
  Core Hamiltonian ⟹ Abstract energy specification
```


### Two-State Framework
```lean
class TwoStateNeuralNetwork (NN) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  - σ_pos/σ_neg: distinguished states
  - θ0: ∀u, Fin (κ2 u) (threshold index)
  - h_fact_pos/neg: threshold behavior
  - h_pact_pos/neg: validity of states
  - m_order: m σ_neg < m σ_pos

-- Concrete instances:
SymmetricBinary R U: σ=R, {1,-1} activations
SymmetricSignum R U: σ=Signum.{pos,neg}
ZeroOne R U: σ=R, {0,1} activations

class TwoStateExclusive (NN) [TwoStateNeuralNetwork NN]
  - pact_iff: ∀a, pact a ↔ (a = σ_pos ∨ a = σ_neg)
```

## Probabilistic Dynamics

### Core Functions
```lean
scale {F} [FunLike F R ℝ] {NN} [TwoStateNeuralNetwork NN] (f: F): ℝ
  := f(m σ_pos) - f(m σ_neg)

logisticProb (x: ℝ): ℝ := 1/(1 + exp(-x))

probPos {F} [FunLike F R ℝ] {NN} [TwoStateNeuralNetwork NN]
  (f: F) (p: Params NN) (T: Temperature) (s: State) (u: U): ℝ
  := logisticProb(scale f * f(localField) * β(T))

updPos/updNeg: force single site to σ_pos/σ_neg

gibbsUpdate: PMF State := bernoulli(probPos) >>= {updPos if true, updNeg if false}
```

### Energy specifications
```lean
structure EnergySpec' {NN} [TwoStateNeuralNetwork NN]
  - E: Params NN → State → R
  - localField: Params NN → State → U → R
  - localField_spec: localField p s u = s.net p u - θ_u
  - flip_energy_relation: f(E p (updPos s u) - E p (updNeg s u)) = -scale f * f(localField p s u)

-- Lyapunov property: energy decreases
energy_is_lyapunov_at_site: spec.E p (s.Up p u) ≤ spec.E p s
```

## Specific Implementations

### Hopfield Energy (SymmetricBinary)
```lean
hamiltonian (p: Params (SymmetricBinary R U)) (s: State): R
  := -(1/2) * quadratic_form p.w s.act + dot_product θ_vec s.act

-- Matrix utilities for quadratic forms:
quadraticForm (M: Matrix ι ι R) (x: ι → R): R := ∑i, x i * (M.mulVec x) i
quadratic_form_update_diag_zero: handles single-site flips with M_ii = 0

-- Flip relation proof:
hamiltonian_flip_relation: hamiltonian p sPos - hamiltonian p sNeg = -2*L
  where L = s.net p u - θ_u
```

### Boltzmann Machine Core
```lean
abbrev BoltzmannMachine R U := SymmetricBinary R U

structure ParamsBM R U
  - params: Params (BoltzmannMachine R U)
  - T: R; hT_pos: T > 0

energy (p: ParamsBM ℝ U) (s: StateBM ℝ U): ℝ := hamiltonian p.params s
probNeuronIsOne/gibbsSamplingStep: convenience wrappers
```

## Convergence Analysis

### Strict Hamiltonian Dynamics
```lean
class IsStrictlyHamiltonian (NN)
  - energy: Params NN → State → R
  - auxPotential: Params NN → State → ℕ
  - energy_is_lyapunov: energy p (s.Up p u) ≤ energy p s
  - aux_strictly_decreases_on_tie: energy tie + state change ⇒ aux decreases

-- For two-state networks:
twoStateAuxPotential: magnetization rank (finite well-founded)
instance IsStrictlyHamiltonian_of_TwoState_EnergySpec

-- Main convergence theorem:
convergence_of_hamiltonian [Fintype State] [IsStrictlyHamiltonian NN]:
  ∃N, (seqStates s₀ p useq N).isStable p
```

### Zero-Temperature Limit
```lean
zeroTempLimitPMF (p: Params NN) (s: State) (u: U): PMF State
  := if θ < net then pure(updPos s u)
     else if net < θ then pure(updNeg s u)
     else bernoulli(1/2) >>= {updPos, updNeg}

-- Main limit theorem:
gibbs_update_tends_to_zero_temp_limit
  {F} [OrderHomClass F R ℝ] (f: F) (hf: Injective f):
  ∀state, Tendsto (λb, gibbsUpdate f p (ofβ b) s u state) atTop
    (𝓝 (zeroTempLimitPMF p s u state))
```

## Statistical mechanics

### Hamiltonian systems
```lean
class IsHamiltonian (NN) [MeasurableSpace State]
  - energy: Params NN → State → ℝ
  - energy_measurable: ∀p, Measurable (energy p)
  - energy_is_lyapunov: energy p (s.Up p u) ≤ energy p s

-- Bridge to canonical ensemble:
toCanonicalEnsemble (NN) [Fintype State] [IsHamiltonian NN] (p: Params NN):
  CanonicalEnsemble State := {energy := IsHamiltonian.energy p, μ := count, ...}

-- Automatic instance:
instance IsHamiltonian_of_EnergySpec'
  (spec: EnergySpec') [TwoStateExclusive NN]: IsHamiltonian NN
```

### Detailed balance & ergodicity
```lean
-- Boltzmann distribution probabilities:
P (p: Params NN) (T: Temperature) (s: State): ℝ := CE.probability T s

-- Transition kernels:
Kbm (u: U) (s s': State): ℝ := (gibbsUpdate ... s u s').toReal

-- Main detailed balance:
detailed_balance (u: U) (s s': State): P s * K u s s' = P s' * K u s' s

-- Random-scan kernel:
randomScanKernel: uniform mixture over single-site updates
randomScanKernel_reversible: reversible w.r.t. Boltzmann measure

-- Ergodicity via Perron-Frobenius:
RScol: column-stochastic transition matrix
RScol_irreducible: positive communication between all states
RScol_unique_stationary_simplex: unique stationary distribution
```

## Computable examples & tests
```lean
-- Concrete networks:
test: 3-neuron rational network with custom topology
HopfieldNetwork ℚ (Fin 4): standard 4-neuron Hopfield

-- Hebbian learning:
Hebbian {m} (ps: Fin m → State): Params := {w := ∑k, outerProduct(ps k)(ps k) - m•I, ...}
patterns_pairwise_orthogonal: w.mulVec(ps j) = (cardU - m)•(ps j)

-- Stability & convergence:
HopfieldNet_convergence_fair/cyclic: existence of stable points
HopfieldNet_stabilize: computes stable state
convergence bounds: ≤ cardU * 2^cardU steps for cyclic updates
```

## Main theorems & properties

1. **Energy monotonicity**: All single-site updates decrease energy (Lyapunov)
2. **Convergence**: Fair update sequences reach stable points (finite time)
3. **Zero-T limit**: Gibbs updates → deterministic threshold dynamics
4. **Detailed balance**: Gibbs kernel reversible w.r.t. Boltzmann distribution
5. **Ergodicity**: Random-scan kernel irreducible + aperiodic
6. **Hebbian stability**: Stored patterns are stable under learned weights
7. **Bridge theorem**: EnergySpec' ⟹ IsHamiltonian ⟹ CanonicalEnsemble

## File structure & dependencies
```
Core.lean: basic Hopfield dynamics & convergence
TwoState.lean: two-state abstraction & Gibbs updates
ZeroTemp.lean: zero-temperature limit theorems
BoltzmannMachine/: specific BM implementation
DetailedBalance*.lean: reversibility proofs
Convergence.lean: strict Hamiltonian framework
Ergodicity.lean: Perron-Frobenius spectral analysis
toCanonicalEnsemble.lean: statistical mechanics bridge
test.lean: computational examples & verification
```

**Usage Pattern**: Define network → prove EnergySpec' → get IsHamiltonian → access CanonicalEnsemble → detailed balance & ergodicity → computational analysis
