import Mathlib.Data.Matrix.Basic
--
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import MCMC.Finite.MetropolisHastings

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace MCMC.Finite

open Matrix Finset --Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Formalization of the Gibbs Sampler
We formalize Gibbs for a bivariate finite state space (α × β), ensuring rigor when marginals are zero.
-/

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The marginal distribution on β. π_β(b) = ∑_a π(a, b). -/
def marginal_β (π : stdSimplex ℝ (α × β)) (b : β) : ℝ :=
  ∑ a : α, π.val (a, b)

lemma marginal_β_nonneg (π : stdSimplex ℝ (α × β)) (b : β) : 0 ≤ marginal_β π b :=
  sum_nonneg (fun a _ => π.property.1 (a, b))

open Classical in
/--
  The conditional distribution π(a | b). Rigorously defined.
  If the marginal probability of b is 0 (an impossible event under π), we choose an arbitrary
  distribution (here, uniform over α) to ensure the resulting kernel is stochastic.
-/
noncomputable def gibbs_conditional_α (π : stdSimplex ℝ (α × β)) (b : β) (a : α) : ℝ :=
  let marg_b := marginal_β π b
  if h : marg_b = 0 then
    -- Default to uniform distribution if α is non-empty.
    if Nonempty α then (1 : ℝ) / Fintype.card α else 0
  else
    -- Standard definition: π(a, b) / π_β(b).
    π.val (a, b) / marg_b

/-- The Gibbs kernel K_α that updates the first component α while leaving β fixed. -/
noncomputable def gibbs_kernel_α (π : stdSimplex ℝ (α × β)) : Matrix (α × β) (α × β) ℝ :=
  fun x y =>
    if x.2 = y.2 then gibbs_conditional_α π x.2 y.1 else 0

/- TODO: MK?
  Theorem: The Gibbs kernel K_α is stochastic.

theorem gibbs_kernel_α_is_stochastic (π : stdSimplex ℝ (α × β)) :
  IsStochastic (gibbs_kernel_α π) := by
  constructor
  · -- 1. Non-negativity.
    sorry
  · -- 2. Rows sum to 1.
    · -- Case: marg_b > 0.
      sorry
-/
/-!
### The Gibbs as a special case of Metropolis-Hastings
-/

/- TODO: MK?
  Theorem: The acceptance probability of a Gibbs step, viewed as an MH step
  where the proposal is the Gibbs kernel itself, is always 1.

theorem gibbs_as_mh_acceptance_is_one (π : stdSimplex ℝ (α × β)) :
  ∀ x y, mh_acceptance_prob π (gibbs_kernel_α π) x y = 1 := by
  intro x y
  let Q := gibbs_kernel_α π
  simp only [mh_acceptance_prob]
  -- Num = π(y) * Q(y, x), Den = π(x) * Q(x, y).
  -- Case 1: x.2 ≠ y.2.
  by_cases h_eq : x.2 = y.2
  swap
  · -- Q(x, y) = 0. Den = 0. Acceptance is 1.
    -- Case 2a: marg_b = 0.
    sorry
  sorry
-/
/- TODO: MK?
  Corollary: The Gibbs kernel is identical to the MH kernel when the proposal
  is the Gibbs kernel itself.

theorem gibbs_kernel_eq_metropolisHastings (π : stdSimplex ℝ (α × β)) :
  gibbs_kernel_α π = metropolisHastingsKernel π (gibbs_kernel_α π) := by
  ext x y
  let Q := gibbs_kernel_α π
  let A := mh_acceptance_prob π Q
  have hA_one : A x y = 1 := gibbs_as_mh_acceptance_is_one π x y
  simp only [metropolisHastingsKernel]
  -- Show the rejection mass R(x) is 0. R(x) = 1 - ∑_z Q(x, z).
  have hR_zero : (1 - ∑ z, Q x z * A x z) = 0 := by
    sorry
  -- P(x, y) = Q(x, y) + δ(x, y) * 0 = Q(x, y).
  sorry
-/

/-!
### MH Usability
We provide sufficient conditions for the MH kernel to be Irreducible and Primitive.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {π : stdSimplex ℝ n} {Q : Matrix n n ℝ}

/-- The target distribution π is strictly positive if π(i) > 0 for all i. -/
def StrictlyPositive (π : stdSimplex ℝ n) : Prop := ∀ i, π.val i > 0

/-- A matrix is strictly positive if all its entries are strictly greater than 0. -/
def IsStrictlyPositive (M : Matrix n n ℝ) : Prop := ∀ i j, M i j > 0

/-! ### Scenario 1: Strict Positivity -/

/- TODO: MK?
  Theorem: If the proposal Q and the target distribution π are strictly positive,
  then the resulting Metropolis-Hastings kernel P is also strictly positive.

theorem metropolisHastings_is_strictly_positive
  (hQ_stoch : IsStochastic Q)
  (hQ_pos : IsStrictlyPositive Q)
  (hπ_pos : StrictlyPositive π) :
  IsStrictlyPositive (metropolisHastingsKernel π Q) := by
  intro x y
  let A := mh_acceptance_prob π Q
  let P := metropolisHastingsKernel π Q
  -- 1. Acceptance probability A(x, y) > 0.
  have hA_pos : A x y > 0 := by
    --simp only [mh_acceptance_prob]
    -- Denominator > 0 and Numerator > 0.
    have h_den_pos : π.val x * Q x y > 0 := mul_pos (hπ_pos x) (hQ_pos x y)
    have h_num_pos : π.val y * Q y x > 0 := mul_pos (hπ_pos y) (hQ_pos y x)
    simp
    sorry
  -- 2. P_proposal(x, y) = Q(x, y) * A(x, y) > 0.
  have hP_prop_pos : Q x y * A x y > 0 := mul_pos (hQ_pos x y) hA_pos
  -- 3. RejectionTerm ≥ 0 (Rejection Mass R(x) ≥ 0).
  sorry
  -- P(x, y) = Positive + Non-negative > 0.
-/

/- TODO: MK?
-- Connection to underlying theory:
theorem IsStrictlyPositive.is_primitive {P : Matrix n n ℝ} (hP_pos : IsStrictlyPositive P) :
  IsPrimitive P := sorry -- k=1 works.

theorem IsStrictlyPositive.is_irreducible [Nonempty n] {P : Matrix n n ℝ} (hP_pos : IsStrictlyPositive P) :
  Matrix.Irreducible P := sorry -- Graph is complete.
-/

/-! ### General Irreducibility and Primitivity -/

/--
  The proposal kernel Q has symmetric connectivity if Q(i, j) > 0 implies Q(j, i) > 0.
-/
def SymmetricConnectivity (Q : Matrix n n ℝ) : Prop :=
  ∀ i j, Q i j > 0 → Q j i > 0

/- TODO: MK?
  Theorem: Irreducibility of MH Kernel.
  If π > 0, and Q is irreducible with symmetric connectivity, then P_MH is irreducible.
theorem metropolisHastings_irreducible
  (hQ_stoch : IsStochastic Q)
  (hQ_irred : Matrix.Irreducible Q)
  (hπ_pos : StrictlyPositive π)
  (hQ_symm : SymmetricConnectivity Q) :
  Matrix.Irreducible (metropolisHastingsKernel π Q) := by
  let P := metropolisHastingsKernel π Q
  let A := mh_acceptance_prob π Q
  -- Strategy: Show that the connectivity graph of P contains the graph of Q.
  have h_P_pos_of_Q_pos : ∀ x y, Q x y > 0 → P x y > 0 := by
    intro x y hQxy_pos
    -- Show A(x, y) > 0.
    have hA_pos : A x y > 0 := by
      sorry
    -- P_proposal > 0.
    have hP_prop_pos : Q x y * A x y > 0 := mul_pos hQxy_pos hA_pos
    -- P(x, y) ≥ proposal mass since the rejection term is ≥ 0.
    simp only [P, metropolisHastingsKernel]
    refine lt_of_lt_of_le hP_prop_pos ?_
    have h_nonneg : 0 ≤ (if x = y then 1 - ∑ z, Q x z * A x z else 0) := by
      classical
      by_cases hxy : x = y
      · subst hxy
        -- Show ∑ Q*A ≤ 1 using A ≤ 1 and stochasticity of Q.
        sorry
      · simp [hxy]
    exact le_add_of_nonneg_right h_nonneg
  -- Connection to underlying theory (W4):
  -- Since P dominates Q in connectivity, and Q is irreducible, P is irreducible.
  sorry
-/

/--
  The proposal Q is "imperfect" if it does not already satisfy detailed balance w.r.t. π.
  This ensures that rejections occur, which introduces self-loops and aids primitivity.
-/
def ProposalIsImperfect (π : stdSimplex ℝ n) (Q : Matrix n n ℝ) : Prop :=
  ∃ i j, π.val i * Q i j ≠ π.val j * Q j i

/- TODO: MK?
  Theorem: Primitivity (Aperiodicity) of MH Kernel.
  If P_MH is irreducible, π > 0, and Q is imperfect, then P_MH is primitive.

theorem metropolisHastings_primitive
  (hQ_stoch : IsStochastic Q)
  -- (hP_irred : Irreducible (metropolisHastingsKernel π Q)) -- Needed for final connection
  (hπ_pos : StrictlyPositive π)
  (h_imperfect : ProposalIsImperfect π Q) :
  IsPrimitive (metropolisHastingsKernel π Q) := by
  let A := mh_acceptance_prob π Q
  let P := metropolisHastingsKernel π Q
  -- Strategy: Show that P has a self-loop (P(x, x) > 0) by showing a rejection occurs.
  -- 1. Find a state x and a move y such that rejection is possible (A(x, y) < 1 and Q(x, y) > 0).
  have h_exists_rejection : ∃ x y, Q x y > 0 ∧ A x y < 1 := by
    obtain ⟨i, j, h_imbalance⟩ := h_imperfect
    -- Case 1: πᵢQᵢⱼ > πⱼQⱼᵢ.
    by_cases h_gt : π.val i * Q i j > π.val j * Q j i
    · use i, j
      -- Q(i, j) > 0 because πᵢQᵢⱼ > 0 and πᵢ > 0.
      have hQij_pos : Q i j > 0 := by sorry
      -- A(i, j) < 1 because the ratio (Num/Den) < 1.
      have hA_lt_one : A i j < 1 := by
        simp [A, mh_acceptance_prob, ne_of_gt (mul_pos (hπ_pos i) hQij_pos)]
        sorry
      exact ⟨hQij_pos, hA_lt_one⟩
    · -- Case 2: πᵢQᵢⱼ < πⱼQⱼᵢ (since ≠ by h_imbalance).
      have h_lt : π.val i * Q i j < π.val j * Q j i := lt_of_le_of_ne (by sorry) h_imbalance
      -- Symmetric argument using j, i.
      use j, i
      have hQji_pos : Q j i > 0 := by sorry
      have hA_lt_one : A j i < 1 := by
        simp [A, mh_acceptance_prob, ne_of_gt (mul_pos (hπ_pos j) hQji_pos)]
        sorry
      exact ⟨hQji_pos, hA_lt_one⟩
  -- 2. Show this implies RejectionMass(x) > 0.
  obtain ⟨x, y, hQ_pos, hA_lt_one⟩ := h_exists_rejection
  have hR_pos : 1 - ∑ z, Q x z * A x z > 0 := by
    apply sub_pos_of_lt
    -- We need ∑ Q*A < 1. We know ∑ Q = 1.
    -- Use the strict inequality sum theorem.
    let f := fun z => Q x z * A x z
    let g := fun z => Q x z
    -- f(z) ≤ g(z) since A ≤ 1.
    have h_le : ∀ z, f z ≤ g z := by
      intro z
      apply mul_le_of_le_one_right (hQ_stoch.1 x z)
      exact (mh_acceptance_prob_bounds hQ_stoch.1 x z).2
    -- Strict inequality at y: f(y) < g(y).
    have h_lt : f y < g y := mul_lt_of_lt_one_right hQ_pos hA_lt_one
    sorry
  -- 3. P(x, x) ≥ R(x) > 0.
  have hPxx_pos : P x x > 0 := by
    simp [P, metropolisHastingsKernel]
    apply lt_of_lt_of_le hR_pos
    sorry
  -- Connection to underlying theory (W4):
  -- We have shown P has a self-loop. Irreducible + self-loop => Primitive.
  sorry
-/

/-!
### W4: Spectral Properties of Reversible Kernels
Connecting reversible Markov chains to the spectral theory of symmetric matrices.
This is essential for proving convergence.
-/

/--
  For a reversible transition kernel `P` with a positive stationary distribution `π`,
  we can define a symmetrized kernel `S`. The spectral properties of `S` (which is
  symmetric) determine the convergence rate of the chain.

  Let `D_sqrt_π` be the diagonal matrix with `sqrt(π_i)` on the diagonal.
  The symmetrized kernel is `S = D_sqrt_π * P * D_sqrt_π⁻¹`.
-/
noncomputable def symmetrizedKernel (π : stdSimplex ℝ n) (P : Matrix n n ℝ) : Matrix n n ℝ :=
  let D_sqrt_π := diagonal (fun i => Real.sqrt (π.val i))
  let D_sqrt_π_inv := diagonal (fun i => 1 / Real.sqrt (π.val i))
  D_sqrt_π * P * D_sqrt_π_inv

/- TODO: MK?
  Theorem: The symmetrized kernel of a reversible matrix is symmetric (self-adjoint).
  This allows leveraging the spectral theorem for symmetric matrices.

theorem symmetrizedKernel_is_hermitian_of_reversible
  (hπ_pos : StrictlyPositive π)
  (hP_rev : IsReversible P π) :
  IsHermitian (symmetrizedKernel π P) := by
  -- For real matrices, IsHermitian is equivalent to being symmetric (Aᵀ = A).
  sorry
-/
end MCMC.Finite
