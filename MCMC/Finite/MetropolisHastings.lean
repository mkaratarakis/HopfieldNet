import MCMC.Finite.Core


namespace MCMC.Finite

open Matrix Finset-- Real

variable {n : Type*} [Fintype n] --[DecidableEq n]

-- here we need to make the defs consistent with the one in Kernel by creating a Matrix.toKernel API

def IsReversible (P : Matrix n n ℝ) (π : stdSimplex ℝ n) : Prop :=
  ∀ i j, π.val i * P i j = π.val j * P j i

theorem IsReversible.is_stationary {P : Matrix n n ℝ} {π : stdSimplex ℝ n}
  (hP_stoch : IsStochastic P) (h_rev : IsReversible P π) :
  IsStationary P π := by
  ext i
  dsimp [IsStationary, transpose_apply]
  calc
    ∑ j, P j i * π.val j
      = ∑ j, π.val i * P i j := by
        congr; ext j
        rw [mul_comm, h_rev i j, mul_comm]
    _ = π.val i * ∑ j, P i j := by rw [Finset.mul_sum]
    _ = π.val i := by rw [hP_stoch.2 i, mul_one]

class IsMCMC' [DecidableEq n] (P : Matrix n n ℝ) (π : stdSimplex ℝ n) where
  stochastic : IsStochastic P
  stationary : IsStationary P π
  irreducible : Matrix.IsIrreducible P
  primitive : IsPrimitive P

/-!
### Algorithm Definitions - Metropolis-Hastings
-/

/--
  The acceptance probability for a Metropolis-Hastings step.
  A(x, y) = min(1, (π(y) * Q(y, x)) / (π(x) * Q(x, y))).

  If the denominator is 0, the move is impossible to propose from x (if π(x)>0),
  or x is unreachable under π. We define the acceptance probability as 1 in this case.
-/
noncomputable def mh_acceptance_prob (π : stdSimplex ℝ n) (Q : Matrix n n ℝ) (x y : n) : ℝ :=
  let num := π.val y * Q y x
  let den := π.val x * Q x y
  if den = 0 then
    1
  else
    min 1 (num / den)

/--
  The Metropolis-Hastings transition kernel (matrix).
  It is constructed by calculating the probability of proposal and acceptance (P_proposal),
  and then adding the remaining "rejection mass" (R) back to the diagonal to ensure stochasticity.
  P(x, y) = P_proposal(x, y) + δ(x, y) * R(x).
-/
noncomputable def metropolisHastingsKernel [DecidableEq n] (π : stdSimplex ℝ n) (Q : Matrix n n ℝ) : Matrix n n ℝ :=
  let A := mh_acceptance_prob π Q
  -- P_proposal(x, y) = Q(x, y) * A(x, y).
  let P_proposal := fun x y => Q x y * A x y
  -- Rejection mass R(x) = 1 - ∑_y P_proposal(x, y).
  let rejection_mass := fun x => 1 - ∑ y, P_proposal x y
  -- The final kernel.
  fun x y => P_proposal x y + (if x = y then rejection_mass x else 0)

variable {π : stdSimplex ℝ n} {Q : Matrix n n ℝ}

/-- Helper lemma: The acceptance probability is bounded between 0 and 1. -/
lemma mh_acceptance_prob_bounds [DecidableEq n]
    (hQ_nonneg : ∀ i j, 0 ≤ Q i j) (x y : n) :
  0 ≤ mh_acceptance_prob π Q x y ∧ mh_acceptance_prob π Q x y ≤ 1 := by
  simp only [mh_acceptance_prob]
  split_ifs
  · simp
  ·
    -- Set the ratio r to type expressions and avoid type inference issues.
    set r : ℝ := (π.val y * Q y x) / (π.val x * Q x y) with hr
    have h_nonneg_ratio : 0 ≤ r := by
      -- The ratio is non-negative since π (from stdSimplex) and Q are non-negative.
      have hr_nonneg : 0 ≤ (π.val y * Q y x) / (π.val x * Q x y) := by
        apply div_nonneg
        · exact mul_nonneg (π.property.1 y) (hQ_nonneg y x)
        · exact mul_nonneg (π.property.1 x) (hQ_nonneg x y)
      simpa [hr] using hr_nonneg
    -- Upper bound: min 1 r ≤ 1.
    have h_le_one : min (1 : ℝ) r ≤ (1 : ℝ) := min_le_left _ _
    exact ⟨le_min zero_le_one h_nonneg_ratio, h_le_one⟩

/-- The MH kernel is stochastic. -/
theorem metropolisHastings_is_stochastic [DecidableEq n]
    (hQ_stoch : IsStochastic Q) :
  IsStochastic (metropolisHastingsKernel π Q) := by
  classical
  let A := mh_acceptance_prob π Q
  have hA_bounds :
      ∀ i j, 0 ≤ mh_acceptance_prob π Q i j ∧ mh_acceptance_prob π Q i j ≤ 1 :=
    fun i j => mh_acceptance_prob_bounds (π:=π) (Q:=Q) (x:=i) (y:=j) hQ_stoch.1
  constructor
  · -- 1. Non-negativity.
    intro x y
    -- P_proposal(x, y) ≥ 0.
    have hP_prop_nonneg : 0 ≤ Q x y * A x y :=
      mul_nonneg (hQ_stoch.1 x y) (hA_bounds x y).1
    -- Rejection mass R(x) ≥ 0. We must show ∑ P_proposal ≤ 1.
    have h_rej_nonneg : 0 ≤ 1 - ∑ j, Q x j * A x j := by
      apply sub_nonneg_of_le
      -- ∑ Q*A ≤ ∑ Q = 1 (since A ≤ 1 and Q ≥ 0).
      calc
        ∑ j, Q x j * A x j
            ≤ ∑ j, Q x j := by
              apply sum_le_sum; intro j _hj
              exact mul_le_of_le_one_right (hQ_stoch.1 x j) (hA_bounds x j).2
        _ = 1 := hQ_stoch.2 x
    -- P(x, y) is the sum of two non-negative terms.
    simp only [metropolisHastingsKernel]
    apply add_nonneg hP_prop_nonneg
    split_ifs with hxy
    · exact h_rej_nonneg
    · simp
  · -- 2. Rows sum to 1 (by construction).
    intro x
    classical
    simp only [metropolisHastingsKernel, sum_add_distrib]
    -- The second term simplifies to R(x).
    have h_second_term :
        (∑ y, (if x = y then (1 - ∑ z, Q x z * A x z) else 0))
          = (1 - ∑ z, Q x z * A x z) := by
      simp [sum_ite_eq]
    rw [h_second_term]
    -- (∑ P_proposal) + (1 - ∑ P_proposal) = 1.
    ring

/--
  Helper lemma: For a > 0 and b ≥ 0: a * min(1, b/a) = min(a, b).
  This identity is central to the proof of detailed balance.
-/
lemma mul_min_one_div_eq_min {a b : ℝ} (ha_pos : 0 < a) (_hn_in : 0 ≤ b) :
  a * min 1 (b / a) = min a b := by
  by_cases h_le : b ≤ a
  · -- If b ≤ a, then b/a ≤ 1.
    have h_div_le_one : b / a ≤ 1 := (div_le_one ha_pos).mpr h_le
    have hne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
    have hmul_div : a * (b / a) = b := by
      have h1 : a * (b / a) = (a * b) / a := (mul_div_assoc a b a).symm
      have h2 : (a * b) / a = (b * a) / a := by simp [mul_comm]
      have h3 : (b * a) / a = b := by exact mul_div_cancel_right₀ b hne
      exact h1.trans (h2.trans h3)
    simp [min_eq_right h_div_le_one, hmul_div, min_eq_right h_le]
  · -- If b > a, then b/a > 1.
    have h_lt : a < b := lt_of_not_ge h_le
    have h_one_lt_div : 1 < b / a := (one_lt_div ha_pos).mpr h_lt
    rw [min_eq_left (le_of_lt h_one_lt_div), mul_one, min_eq_left (le_of_lt h_lt)]

set_option linter.unusedVariables false in
/--
  Theorem: The MH kernel satisfies the detailed balance condition (reversibility)
  with respect to π. This proof is robust and does not require π to be strictly positive.
-/
theorem metropolisHastings_is_reversible [DecidableEq n] (hQ_nonneg : ∀ i j, 0 ≤ Q i j) :
  IsReversible (metropolisHastingsKernel π Q) π := by
  intro x y
  let P := metropolisHastingsKernel π Q
  let A := mh_acceptance_prob π Q
  by_cases h_eq : x = y
  · simp [metropolisHastingsKernel, h_eq]
  ·
    have hyx : y ≠ x := ne_comm.mp h_eq
    simp [metropolisHastingsKernel, h_eq, hyx]
    let a := π.val x * Q x y
    let b := π.val y * Q y x
    have ha_nonneg : 0 ≤ a := mul_nonneg (π.property.1 x) (hQ_nonneg x y)
    have hb_nonneg : 0 ≤ b := mul_nonneg (π.property.1 y) (hQ_nonneg y x)
    have hL : π.val x * (Q x y * A x y) = a * A x y := by
      dsimp [a]; ac_rfl
    have hR : π.val y * (Q y x * A y x) = b * A y x := by
      dsimp [b]; ac_rfl
    rw [hL, hR]
    by_cases ha_zero : a = 0
    · have hAxy : A x y = 1 := by
        have : π.val x * Q x y = a := rfl
        simp [A, mh_acceptance_prob, this, ha_zero]
      have LHS_zero : a * A x y = 0 := by simp [hAxy, ha_zero]
      by_cases hb_zero : b = 0
      · simp [hb_zero, LHS_zero]
      · have hAyx : A y x = 0 := by
          have hb' : π.val y * Q y x = b := rfl
          have ha' : π.val x * Q x y = a := rfl
          simp [A, mh_acceptance_prob, hb', ha', hb_zero, ha_zero]
        simp [LHS_zero, hAyx]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (ne_comm.mp ha_zero)
      have hAxy : A x y = min 1 (b / a) := by
        have : π.val x * Q x y = a := rfl
        simp [A, mh_acceptance_prob, this, ha_zero, b]
      have LHS_min : a * A x y = min a b := by
        rw [hAxy]; exact mul_min_one_div_eq_min ha_pos hb_nonneg
      by_cases hb_zero : b = 0
      · simp [LHS_min, hb_zero, min_eq_right ha_nonneg]
      · have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (ne_comm.mp hb_zero)
        have hAyx : A y x = min 1 (a / b) := by
          have hb' : π.val y * Q y x = b := rfl
          have ha' : π.val x * Q x y = a := rfl
          simp [A, mh_acceptance_prob, hb', ha', hb_zero, a]
        have RHS_min : b * A y x = min b a := by
          rw [hAyx]; exact mul_min_one_div_eq_min hb_pos ha_nonneg
        calc
          a * A x y = min a b := LHS_min
          _ = min b a := min_comm _ _
          _ = b * A y x := RHS_min.symm

/-- The Metropolis-Hastings kernel has π as its stationary distribution. -/
theorem metropolisHastings_is_stationary [DecidableEq n] (hQ_stoch : IsStochastic Q) :
  IsStationary (metropolisHastingsKernel π Q) π := by
  let P := metropolisHastingsKernel π Q
  have hP_stoch : IsStochastic P := metropolisHastings_is_stochastic hQ_stoch
  have hP_rev : IsReversible P π := metropolisHastings_is_reversible hQ_stoch.1
  -- Reversibility implies stationarity.
  exact hP_rev.is_stationary hP_stoch

/--
  The IsMCMC instance for the Metropolis-Hastings algorithm.
  Stochasticity and Stationarity are guaranteed by construction. Irreducibility and
  Primitivity depend on the properties of Q and π and must be supplied.
-/
def isMCMC_MetropolisHastings [DecidableEq n]
    (hQ_stoch : IsStochastic Q)
    (hP_irred : Matrix.IsIrreducible (metropolisHastingsKernel π Q))
    (hP_prim : IsPrimitive (metropolisHastingsKernel π Q)) :
    IsMCMC (metropolisHastingsKernel π Q) π where
  stochastic := metropolisHastings_is_stochastic hQ_stoch
  stationary := metropolisHastings_is_stationary hQ_stoch
  irreducible := hP_irred
  primitive := hP_prim

end MCMC.Finite
