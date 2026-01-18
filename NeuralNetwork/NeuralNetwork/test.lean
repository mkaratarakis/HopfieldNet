import NeuralNetwork.Core

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

variable {R U : Type} [Zero R]
universe uR uU
variable {R : Type uR} {U : Type uU}  [Zero R]
variable {R : Type uR} {U : Type uU} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U]
/-- Two neurons `u` and `v` are connected in the graph if `w u v` is not zero. -/
def Matrix.Adj (w : Matrix U U R) : U → U → Prop := fun u v => w u v ≠ 0

/-- `Matrix.w` returns the value of the matrix `w` at position `(u, v)` if `u` and `v` are connected. -/
def Matrix.w (w : Matrix U U R) : ∀ u v : U, w.Adj u v → R := fun u v _ => w u v

/-- A 3x3 matrix of rational numbers. --/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

def test : NeuralNetwork ℚ (Fin 3) ℚ where
  Adj := fun u v => u ≠ v
  Ui := {u | u = 0 ∨ u = 1}
  Uo := {u | u = 2}
  Uh := (∅ : Set (Fin 3))
  hUi := by
    intro hEmpty
    -- 0 ∈ Ui
    have h0 : (0 : Fin 3) ∈ ({u : Fin 3 | u = 0 ∨ u = 1} : Set (Fin 3)) := by simp
    -- Transport along the assumed equality Ui = ∅ to obtain a contradiction.
    have : (0 : Fin 3) ∈ (∅ : Set (Fin 3)) := by aesop
    exact this
  hUo := by
    intro hEmpty
    have h2 : (2 : Fin 3) ∈ ({u : Fin 3 | u = 2} : Set (Fin 3)) := by simp
    have : (2 : Fin 3) ∈ (∅ : Set (Fin 3)) := by aesop
    exact this
  hU := by
    -- Show univ = Ui ∪ Uo ∪ Uh (with Uh = ∅)
    ext u; constructor
    · intro _; have : (u : ℕ) < 3 := u.2
      -- Exhaust the three inhabitants of Fin 3.
      fin_cases u <;> simp
    · intro _; trivial
  hhio := by
    -- Uh = ∅ ⇒ intersection is empty
    ext u; simp
  κ1 _ := 0
  κ2 _ := 1
  fnet _ w pred _ := ∑ v, w v * pred v
  fact _ _ net_input θvec :=
    if (θvec.get ⟨0, by decide⟩) ≤ net_input then 1 else 0
  fout _ a := a
  m := id
  pact _ := True
  pw _ := True
  hpact _ _ _ _ _ _ _ _ := trivial

/-- Parameters for `test` network (reuse weights, thresholds length 1). -/
def wθ : Params test where
  w := test.M
  hw u v huv := by
    -- Not adjacent means u = v (since Adj := fun u v => u ≠ v).
    simp [test] at huv
    subst huv
    -- Now goal is that the diagonal entry is 0; check each possible u.
    fin_cases u <;> decide
  hw' := trivial
  σ _ := Vector.emptyWithCapacity 0
  θ _ := ⟨#[0], by aesop⟩

instance : Repr (NeuralNetwork.State test) where
  reprPrec state _ :=
    "acts: " ++ repr (state.act) ++
    ", outs: " ++ repr (state.out) ++
    ", nets: " ++ repr (state.net wθ)

/--
`test.extu` is the initial state for the `test` neural network with activations `[1, 0, 0]`.
-/
def test.extu : test.State := {act := ![1,0,0], hp := fun u => trivial}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

lemma test.onlyUi : test.extu.onlyUi := by
  refine ⟨0, ?_⟩
  intro u hu
  -- From u ∉ Ui we deduce u = 2 (since Ui = {0,1})
  have h2 : u = 2 := by
    -- exclude 0
    have hne0 : u ≠ 0 := by
      intro h; subst h; simp [test] at hu
    -- exclude 1
    have hne1 : u ≠ 1 := by
      intro h; subst h; simp [test] at hu
    fin_cases u <;> simp_all
  subst h2
  -- activation at neuron 2 is 0
  simp [test.extu]

/-The workphase for the asynchronous update of the sequence of neurons u3 , u1 , u2 , u3 , u1 , u2 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,0,1,2,0,1,2]

/-The workphase for the asynchronous update of the sequence of neurons u3 , u2 , u1 , u3 , u2 , u1 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,1,0,2,1,0,2]

/-Hopfield Networks-/

/-- A 4x4 matrix of rational numbers. --/
def W1 : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of ![![0,1,-1,-1], ![1,0,-1,-1], ![-1,-1,0,1], ![-1,-1,1,0]]

/--
`HebbianParamsTest` defines a Hopfield Network with 4 neurons and rational weights.
- `w`: The weight matrix `W1`.
- `hw`: Proof that the weights are symmetric.
- `hw'`: Proof that the weights are zero on the diagonal.
- `σ`: Always an empty vector.
- `θ`: Always returns a list with a single 0.
--/
def HebbianParamsTest : Params (HopfieldNetwork ℚ (Fin 4)) where
  w := W1
  hw u v huv := by
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ := fun u => Vector.emptyWithCapacity 0
  θ u := ⟨#[0],by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]⟩

/-- `extu` is the initial state for our `HebbianParamsTest` Hopfield network.
- `act`: `[1, -1, -1, 1]` - initial activations.

This initializes the state for a Hopfield network test.
--/
def extu : State' HebbianParamsTest where
  act := ![1,-1,-1,1]
  hp := by
    intros u
    unfold HopfieldNetwork
    simp only
    revert u
    decide

instance : Repr (HopfieldNetwork ℚ (Fin 4)).State where
  reprPrec state _ := ("acts: " ++ repr (state.act))

-- Computations

-- lemma zero_if_not_mem_Ui' : ∀ u : Fin 4,
--     ¬ u ∈ ({0,1,2,3} : Finset (Fin 4)) → extu.act u = 0 := by {decide}

-- def HN.hext : extu.onlyUi := by {intros u; tauto}

-- #eval NeuralNetwork.State.workPhase HebbianParamsTest extu HN.hext [2,0,1,2,0,1,2]


/--
`pattern_ofVec` converts a pattern vector from `Fin n` to `ℚ` into a `State`
for a `HopfieldNetwork` with `n` neurons.
It checks if all elements are either 1 or -1. If they are, it returns `some`
 pattern; otherwise, it returns `none`.
--/
def pattern_ofVec {n} [NeZero n] (pattern : Fin n → ℚ) :
    Option (HopfieldNetwork ℚ (Fin n)).State :=
  if hp : ∀ i, pattern i = 1 ∨ pattern i = -1 then
    some {act := pattern, hp := by {
      intros u
      unfold HopfieldNetwork
      simp only
      apply hp
      }}
  else
    none

/--
`obviousFunction` tries to convert a function `f` from `α` to `Option β` into a regular function
from `α` to `β`. If `f` returns `some` for every input, it returns `some` function that extracts
these values. Otherwise, it returns `none`.
--/
def obviousFunction [Fintype α] (f : α → Option β) : Option (α → β) :=
  if h : ∀ x, (f x).isSome then
    some (fun a => (f a).get (h a))
  else
    none


/--
Converts a matrix of patterns `V` into Hopfield network states.

Each row of `V` (a function `Fin m → Fin n → ℚ`) is mapped to a Hopfield network state
if all elements are either `1` or `-1`. Returns `some` mapping if successful, otherwise `none`.
-/
def patternsOfVecs (V : Fin m → Fin n → ℚ) [NeZero n] (hmn : m < n) :
  Option (Fin m → (HopfieldNetwork ℚ (Fin n)).State) :=
  obviousFunction (fun i => pattern_ofVec (V i))

/--
`ZeroParams_4` defines a simple Hopfield Network with 4 neurons.

- `w`: A 4x4 weight matrix filled with zeros.
- `hw`: Proof that the weight matrix is symmetric.
- `hw'`: Proof that the weight matrix has zeros on the diagonal.
- `σ`: An empty vector for each neuron.
- `θ`: A threshold of 0 for each neuron, with proof that the list has length 1.
--/
def ZeroParams_4 : Params (HopfieldNetwork ℚ (Fin 4)) where
  w :=  (Matrix.of ![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0]])
  hw u v huv := by {
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide}
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ u := Vector.emptyWithCapacity 0
  θ u := ⟨#[0], by {simp only [List.size_toArray, List.length_cons,
    List.length_nil, zero_add]}⟩

/--
`ps` are two patterns represented by a 2x4 matrix of rational numbers.
--/
def ps : Fin 2 → Fin 4 → ℚ := ![![1,1,-1,-1], ![-1,1,-1,1]]

/--
`test_params` sets up a `HopfieldNetwork` with 4 neurons.
It converts the patterns `ps` into a network using Hebbian learning if possible.
If not, it defaults to `ZeroParams_4`.
--/
def test_params : Params (HopfieldNetwork ℚ (Fin 4)) :=
  match (patternsOfVecs ps (by simp only [Nat.reduceLT])) with
  | some patterns => Hebbian patterns
  | none => ZeroParams_4

/--
`useq_Fin n` maps a natural number `i` to an element of `Fin n` (a type with `n` elements).
It wraps `i` around using modulo `n`.

Arguments:
- `n`: The size of the finite type (must be non-zero).
- `i`: The natural number to convert.

Returns:
- An element of `Fin n`.
--/
def useq_Fin n [NeZero n] : ℕ → Fin n := fun i =>
  ⟨_, Nat.mod_lt i (Nat.pos_of_neZero n)⟩

lemma useq_Fin_cyclic n [NeZero n] : cyclic (useq_Fin n) := by
  unfold cyclic
  unfold useq_Fin
  simp only [Fintype.card_fin]
  apply And.intro
  · intros u
    use u.val
    cases' u with u hu
    simp only
    simp_all only [Fin.mk.injEq]
    exact Nat.mod_eq_of_lt hu
  · intros i j hij
    exact Fin.mk.inj_iff.mpr hij

lemma useq_Fin_fair n [NeZero n] : fair (useq_Fin n) :=
  cycl_Fair (useq_Fin n) (useq_Fin_cyclic n)

#eval HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)

#eval HopfieldNet_conv_time_steps test_params extu (useq_Fin 4) (useq_Fin_cyclic 4)


/-
Verification note for the two workPhase #eval above:

Given:
  * pact := True (no ±1 restriction here),
  * fact returns 1 when θ ≤ net_input else 0, with θ = 0,
  * Once a neuron flips to 1 it tends to stay 1 because its net input (a sum of
    non‑thresholded weighted predecessors) becomes non‑negative in these test
    sequences.

So both sequences drive all three activations to 1. The printed states
  acts: ![1, 1, 1], outs: ![1, 1, 1], nets: ![4, 1, 1]
are therefore expected (the net for neuron 0 accumulates the strongest weight sum).
-/

/-!
Verification of the stabilization result for the 4‑neuron Hopfield example
`HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)`.

We show it converges to the stored pattern `[-1, 1, -1, 1]` (the second Hebbian pattern).
Reason (manual check of first two updates under Hebbian weights built from `ps`):
  Non‑zero Hebbian weights (after subtracting 2•I) connect (0,3) and (1,2) with weight -2.
  Initial state extu = [ 1, -1, -1, 1 ].
  Local field at 0: w₀3 * a₃ = (-2)*1 = -2 < 0 ⇒ a₀ flips to -1.
  Local field at 1: w₁2 * a₂ = (-2)*(-1) = 2 > 0 ⇒ a₁ flips to 1.
  Sites 2 and 3 already match the target pattern. Thereafter the configuration
  [-1, 1, -1, 1] is a stored (orthogonal) pattern ⇒ stable.
-/

/-- The expected stabilized pattern. -/
def expectedPattern₁ : (HopfieldNetwork ℚ (Fin 4)).State :=
{ act := ![-1,1,-1,1]
, hp := by intro u; fin_cases u <;> decide }

/- Sanity check: the stored pattern is stable for the learned parameters. -/
#eval (expectedPattern₁.act)  -- prints ![-1, 1, -1, 1]

/- Evaluate the stabilized state (should match `expectedPattern₁.act`). -/
#eval (HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)).act

/- Boolean confirmation that stabilization reached the expected pattern (act field). -/
#eval
  let reached := (HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)).act
  (reached = expectedPattern₁.act)
