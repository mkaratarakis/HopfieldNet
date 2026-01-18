import Riemann.PhysLean.SpinGlass.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP

open scoped ContDiff

namespace SpinGlass

variable {N : ℕ}

/-!
## Calculus bridge for the free energy (Talagrand)

This file packages the **calculus layer** needed to connect:

- the *abstract* Fréchet-derivative API used by the Gaussian IBP library; and
- the *explicit* Gibbs-average / covariance formulas used in the SK algebra.

The key statement is `hessian_free_energy_eq_variance`, asserting that the (abstract)
Hessian of the free energy density is exactly the Gibbs covariance bilinear form.

### References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3 (differentiation of
  \(\log Z\) and the Gibbs covariance/Hessian identity used in the Guerra interpolation).
-/

section Derivatives

/-!
### Smoothness of the partition function and free energy

These are the (finite-dimensional) smoothness facts used to justify the Fréchet derivatives.
They correspond to standard computations in Talagrand’s Appendix on differentiation of
the free energy functional.
-/

/--
`Z` is smooth (`C^∞`) as a finite sum of exponentials of linear forms.

This is the finite-volume regularity input behind Talagrand’s differentiation of the free energy
functional (Vol. I, Ch. 1, §1.3).
-/
lemma contDiff_Z (N : ℕ) : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := by
  classical
  -- `Z(H) = ∑σ exp(-H σ)`. Each summand is smooth and the index set is finite.
  have hterm :
      ∀ σ : Config N, ContDiff ℝ (∞) (fun H : EnergySpace N => Real.exp (-H σ)) := by
    intro σ
    -- `H ↦ H σ` is smooth (continuous linear), so `H ↦ exp(-H σ)` is smooth by composition.
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (N := N) σ).contDiff))
  simpa [Z] using
    (ContDiff.sum (𝕜 := ℝ) (n := (∞))
      (s := (Finset.univ : Finset (Config N)))
      (f := fun σ : Config N => fun H : EnergySpace N => Real.exp (-H σ))
      (fun σ hσ => hterm σ))

/--
`gibbs_pmf` is smooth (`C^∞`) as a quotient of smooth functions, since `Z(H) ≠ 0`.
-/
lemma contDiff_gibbs_pmf (N : ℕ) (σ : Config N) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => gibbs_pmf N H σ) := by
  classical
  have hnum :
      ContDiff ℝ (∞) (fun H : EnergySpace N => Real.exp (-H σ)) := by
    -- `H ↦ exp(-H σ)` is smooth as in `contDiff_Z`.
    simpa using (contDiff_exp.comp (contDiff_neg.comp (evalCLM (N := N) σ).contDiff))
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := contDiff_Z (N := N)
  have hZne : ∀ H : EnergySpace N, Z N H ≠ 0 := fun H =>
    (Z_pos (N := N) (H := H)).ne'
  simpa [gibbs_pmf] using hnum.div hZ hZne

/--
`Z(H) > 0` for every Hamiltonian `H`.

This is the positivity condition needed to differentiate `log (Z H)` (as in Talagrand, Vol. I,
Ch. 1, §1.3).
-/
lemma Z_pos_everywhere (H : EnergySpace N) : 0 < Z N H :=
  Z_pos (N := N) (H := H)

/--
The free energy density `H ↦ (1/N) log Z(H)` is smooth.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (differentiation of the free energy).
-/
lemma contDiff_free_energy_density (N : ℕ) :
    ContDiff ℝ (∞) (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  classical
  -- Smoothness of `log ∘ Z` uses that `Z` never vanishes.
  have hZ : ContDiff ℝ (∞) (fun H : EnergySpace N => Z N H) := contDiff_Z (N := N)
  have hlog : ContDiff ℝ (∞) (fun H : EnergySpace N => Real.log (Z N H)) :=
    (hZ.log (fun H => (Z_pos_everywhere (N := N) (H := H)).ne'))
  -- Multiply by the constant `1/N`.
  simpa [free_energy_density, smul_eq_mul, mul_assoc] using
    (ContDiff.const_smul (𝕜 := ℝ) (n := (∞)) (R := ℝ) (c := (1 / (N : ℝ))) hlog)

/-!
### First and second Fréchet derivatives (Talagrand: Gibbs averages and covariances)

These are the formal counterparts of the standard identities:

* \(D(\log Z)(h) = -\langle h \rangle\),
* \(D^2(\log Z)(h,k) = \langle hk \rangle - \langle h \rangle \langle k \rangle\).
-/

/--
**First derivative of the free energy density.**

This is Talagrand’s “\(D\log Z = -\langle \cdot\rangle\)” identity for the Gibbs measure,
with the extra \(1/N\) normalization of the free energy density.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (first derivative of \(\log Z\)).
-/
lemma fderiv_free_energy_apply (H h : EnergySpace N) :
    fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H h =
      -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
  fderiv_free_energy_density_apply (N := N) (H := H) (h := h)

/--
**Second derivative / Hessian equals Gibbs covariance** (Talagrand).

This is the key “bridge” identity: the abstract Hessian (Fréchet second derivative)
agrees with the explicit Gibbs covariance formula.

In Talagrand’s notation, this is the identification of \(D^2 \log Z\) with the Gibbs
variance/covariance (used implicitly throughout the Guerra interpolation).

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (second derivative of \(\log Z\) as a covariance).
-/
lemma hessian_free_energy_eq_variance (H h k : EnergySpace N) :
    (hessian_logZ (N := N) H) h k
      = (1 / (N : ℝ)) *
          ((∑ σ : Config N, gibbs_pmf N H σ * h σ * k σ) -
            (∑ σ : Config N, gibbs_pmf N H σ * h σ) * (∑ τ : Config N, gibbs_pmf N H τ * k τ)) := by
  -- This is exactly `hessian_eq_covariance` plus unfolding the explicit covariance definition.
  simpa [gibbs_covariance, hessian_free_energy] using
    (hessian_eq_covariance (N := N) (H := H) (h := h) (k := k))

end Derivatives

/-!
### Moderate growth / integrability package (for Gaussian IBP)

The Gaussian IBP library expects test functions to have “moderate growth” in the sense of
`PhysLean.Probability.GaussianIBP.HasModerateGrowth`. For the SK free energy this is elementary:
`free_energy_density` grows at most linearly and its Fréchet derivative is uniformly bounded
(in fact Lipschitz with constant `1/N`).

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (finite-volume free energy is smooth and has controlled
derivatives, justifying Gaussian IBP manipulations).
-/

section ModerateGrowth

open scoped BigOperators

open PhysLean.Probability.GaussianIBP

variable (N)

lemma abs_apply_le_norm (H : EnergySpace N) (σ : Config N) : |H σ| ≤ ‖H‖ := by
  -- `PiLp` evaluation is 1-Lipschitz: `‖H σ‖ ≤ ‖H‖`.
  simpa [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (p := (2 : ENNReal)) (x := H) σ)

lemma Z_le_card_mul_exp_norm (H : EnergySpace N) :
    Z N H ≤ (Fintype.card (Config N) : ℝ) * Real.exp (‖H‖) := by
  classical
  -- Termwise bound: `exp(-H σ) ≤ exp(‖H‖)`.
  have hterm : ∀ σ : Config N, Real.exp (-H σ) ≤ Real.exp (‖H‖) := by
    intro σ
    have hlin : -H σ ≤ ‖H‖ :=
      (neg_le_abs (H σ)).trans (abs_apply_le_norm (N := N) H σ)
    simpa using (Real.exp_le_exp.2 hlin)
  -- Sum the bounds.
  -- `Z(H) = ∑σ exp(-H σ) ≤ ∑σ exp(‖H‖) = card(Config N) * exp(‖H‖)`.
  simpa [Z] using
    (calc
      (∑ σ : Config N, Real.exp (-H σ))
          ≤ ∑ σ : Config N, Real.exp (‖H‖) := by
              -- rewrite the `Fintype` sum as a `Finset.univ` sum to use `sum_le_sum`
              simpa using
                (Finset.sum_le_sum (s := (Finset.univ : Finset (Config N)))
                  (fun σ _hσ => hterm σ))
      _ = (Fintype.card (Config N) : ℝ) * Real.exp (‖H‖) := by
            simp)

lemma Z_ge_exp_neg_norm (H : EnergySpace N) :
    Real.exp (-‖H‖) ≤ Z N H := by
  classical
  -- Pick any configuration; its Boltzmann weight is a lower bound for the partition function.
  let σ₀ : Config N := fun _ => false
  have hlin0 : H σ₀ ≤ ‖H‖ :=
    (le_abs_self (H σ₀)).trans (abs_apply_le_norm (N := N) H σ₀)
  have hlin : -‖H‖ ≤ -H σ₀ := by
    simpa using (neg_le_neg hlin0)
  have hexp : Real.exp (-‖H‖) ≤ Real.exp (-H σ₀) := by
    simpa using (Real.exp_le_exp.2 hlin)
  have hterm_le_Z : Real.exp (-H σ₀) ≤ Z N H := by
    -- `f σ₀ ≤ ∑σ f σ` for nonnegative terms.
    have hnonneg : ∀ σ : Config N, 0 ≤ Real.exp (-H σ) := fun σ => (Real.exp_pos _).le
    -- Use the finset version explicitly, then simplify back to the `Fintype` sum defining `Z`.
    have :
        Real.exp (-H σ₀) ≤
          ∑ σ ∈ (Finset.univ : Finset (Config N)), Real.exp (-H σ) := by
      exact Finset.single_le_sum (fun σ _hσ => hnonneg σ) (Finset.mem_univ σ₀)
    simpa [Z] using this
  exact le_trans hexp hterm_le_Z

/-- `free_energy_density` has moderate growth (polynomial of degree 1) in the IBP sense. -/
noncomputable def hasModerateGrowth_free_energy_density :
    HasModerateGrowth (fun H : EnergySpace N => free_energy_density (N := N) H) := by
  classical
  let C : ℝ := Real.log (Fintype.card (Config N)) + 1
  refine ⟨C, 1, ?_, ?_, ?_⟩
  · -- `C > 0`.
    have hcard_pos : 0 < Fintype.card (Config N) := by
      classical
      have : Nonempty (Config N) := ⟨fun _ => false⟩
      exact Fintype.card_pos
    have h1le : (1 : ℝ) ≤ (Fintype.card (Config N) : ℝ) := by
      -- `1 ≤ card` for a nonempty finite type.
      exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
    have hlog_nonneg : 0 ≤ Real.log (Fintype.card (Config N) : ℝ) :=
      Real.log_nonneg h1le
    nlinarith
  · -- Value bound.
    intro H
    have hcard_pos : 0 < Fintype.card (Config N) := by
      classical
      have : Nonempty (Config N) := ⟨fun _ => false⟩
      exact Fintype.card_pos
    have hlog_nonneg : 0 ≤ Real.log (Fintype.card (Config N) : ℝ) := by
      have h1le : (1 : ℝ) ≤ (Fintype.card (Config N) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
      exact Real.log_nonneg h1le
    have hZpos : 0 < Z N H := Z_pos (N := N) (H := H)
    have hZ_le := Z_le_card_mul_exp_norm (N := N) H
    have hZ_ge := Z_ge_exp_neg_norm (N := N) H
    have hlog_upper :
        Real.log (Z N H) ≤ Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
      -- `log Z ≤ log(card * exp(‖H‖)) = log(card) + ‖H‖`.
      have hlog_le :
          Real.log (Z N H) ≤ Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖)) :=
        Real.log_le_log hZpos hZ_le
      have hcard_ne : (Fintype.card (Config N) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcard_pos)
      have : Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖))
            = Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
        -- avoid `simp` rewriting `card (Config N)` (which can trigger `log_pow`)
        have hexp_ne : Real.exp (‖H‖) ≠ 0 := Real.exp_ne_zero _
        calc
          Real.log ((Fintype.card (Config N) : ℝ) * Real.exp (‖H‖))
              = Real.log (Fintype.card (Config N) : ℝ) + Real.log (Real.exp (‖H‖)) := by
                  simpa using (Real.log_mul hcard_ne hexp_ne)
          _ = Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ := by
                  rw [Real.log_exp]
      rw [this] at hlog_le
      exact hlog_le
    have hlog_lower : -(Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ Real.log (Z N H) := by
      -- `log Z ≥ log(exp(-‖H‖)) = -‖H‖ ≥ -(log(card)+‖H‖)`.
      have h1 : -‖H‖ ≤ Real.log (Z N H) := by
        have hlog_le : Real.log (Real.exp (-‖H‖)) ≤ Real.log (Z N H) := by
          -- monotonicity of `log`
          have hexp_pos : 0 < Real.exp (-‖H‖) := Real.exp_pos _
          exact Real.log_le_log hexp_pos hZ_ge
        simpa using hlog_le
      have h2 : -(Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ -‖H‖ := by
        nlinarith [hlog_nonneg]
      exact le_trans h2 h1
    have habs_log :
        |Real.log (Z N H)| ≤ Real.log (Fintype.card (Config N) : ℝ) + ‖H‖ :=
      (abs_le.2 ⟨hlog_lower, hlog_upper⟩)
    -- Finally, scale by `1/N` and absorb into `C * (1 + ‖H‖)`.
    have hN : 0 ≤ (1 / (N : ℝ)) := by
      exact one_div_nonneg.2 (by exact_mod_cast (Nat.cast_nonneg N))
    have hscale :
        |free_energy_density (N := N) H|
          ≤ (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
      -- `| (1/N) * log Z | ≤ (1/N) * |log Z|`.
      have : |free_energy_density (N := N) H|
            = |(1 / (N : ℝ)) * Real.log (Z N H)| := by
                simp [free_energy_density]
      -- use `abs_mul` and the bound on `|log Z|`
      calc
        |free_energy_density (N := N) H|
            = |(1 / (N : ℝ)) * Real.log (Z N H)| := this
        _ = |(1 / (N : ℝ))| * |Real.log (Z N H)| := by simp [abs_mul]
        _ = (1 / (N : ℝ)) * |Real.log (Z N H)| := by simp
        _ ≤ (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
              exact mul_le_mul_of_nonneg_left habs_log (by linarith)
    -- Bound `(1/N) * (...) ≤ C * (1 + ‖H‖)`.
    have hC_ge1 : (1 : ℝ) ≤ C := by
      have : 0 ≤ Real.log (Fintype.card (Config N) : ℝ) := hlog_nonneg
      dsimp [C]
      nlinarith
    have hone_le : (1 : ℝ) ≤ 1 + ‖H‖ := by nlinarith [norm_nonneg H]
    have hone_div_le : (1 / (N : ℝ)) ≤ 1 := by
      -- for `N : ℕ`, `1/N ≤ 1`
      cases N with
      | zero =>
          simp
      | succ n =>
          have : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by exact_mod_cast (Nat.succ_pos n)
          simpa [one_div] using (one_div_le_one_div_of_le (by linarith) this)
    have hpoly :
        (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖)
          ≤ C * (1 + ‖H‖) := by
      -- Coarse: drop the prefactor `1/N`, and use `(a + x) ≤ (a+1)(1+x)` with `a = log(card)`.
      have h1 :
          (1 / (N : ℝ)) * (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖)
            ≤ (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
        have hnonneg : 0 ≤ (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) := by
          nlinarith [hlog_nonneg, norm_nonneg H]
        exact (mul_le_mul_of_nonneg_right hone_div_le hnonneg).trans_eq (by simp)
      have h2 :
          (Real.log (Fintype.card (Config N) : ℝ) + ‖H‖) ≤ C * (1 + ‖H‖) := by
        -- `(a+x) ≤ (a+1)(1+x)` for `a,x ≥ 0`.
        dsimp [C]
        nlinarith [hlog_nonneg, norm_nonneg H]
      exact le_trans h1 h2
    -- Match the `HasModerateGrowth` normal form with `m = 1`.
    simpa [C, pow_one] using le_trans hscale hpoly
  · -- Derivative bound.
    intro H
    -- It suffices to bound the operator norm by `1`, then absorb into `C * (1+‖H‖)`.
    have hN : 0 ≤ (1 / (N : ℝ)) := by
      exact one_div_nonneg.2 (by exact_mod_cast (Nat.cast_nonneg N))
    have h_op :
        ‖fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H‖ ≤ (1 / (N : ℝ)) := by
      -- Use the explicit directional derivative formula and a convexity bound.
      refine ContinuousLinearMap.opNorm_le_bound _ hN ?_
      intro h
      -- Evaluate the `fderiv` on `h` and bound it by `‖h‖`.
      have h_eval :
          (fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H) h =
            -(1 / (N : ℝ)) * ∑ σ : Config N, (gibbs_pmf N H σ) * h σ :=
        fderiv_free_energy_density_apply (N := N) (H := H) (h := h)
      -- Bound the weighted sum by `‖h‖` using `|h σ| ≤ ‖h‖` and `∑ g = 1`.
      have hs1 : (∑ σ : Config N, gibbs_pmf N H σ) = 1 := sum_gibbs_pmf (N := N) (H := H)
      have hsum_bound :
          |∑ σ : Config N, gibbs_pmf N H σ * h σ| ≤ ‖h‖ := by
        -- `|∑ gσ hσ| ≤ ∑ gσ |hσ| ≤ ‖h‖ * ∑ gσ = ‖h‖`.
        have h_abs_le :
            |∑ σ : Config N, gibbs_pmf N H σ * h σ|
              ≤ ∑ σ : Config N, |gibbs_pmf N H σ * h σ| := by
          -- `Fintype` sum = `Finset.univ` sum; use `abs_sum_le_sum_abs`.
          simpa using
            (Finset.abs_sum_le_sum_abs
              (f := fun σ : Config N => gibbs_pmf N H σ * h σ)
              (s := (Finset.univ : Finset (Config N))))
        have h_abs_term :
            (∑ σ : Config N, |gibbs_pmf N H σ * h σ|)
              = ∑ σ : Config N, (gibbs_pmf N H σ) * |h σ| := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          have hg : 0 ≤ gibbs_pmf N H σ := gibbs_pmf_nonneg (N := N) (H := H) σ
          simp [abs_mul, abs_of_nonneg hg]
        have hsum_le :
            (∑ σ : Config N, (gibbs_pmf N H σ) * |h σ|)
              ≤ (∑ σ : Config N, gibbs_pmf N H σ) * ‖h‖ := by
          -- termwise: `gσ * |hσ| ≤ gσ * ‖h‖`.
          have hterm : ∀ σ : Config N, (gibbs_pmf N H σ) * |h σ| ≤ (gibbs_pmf N H σ) * ‖h‖ := by
            intro σ
            have hσ : |h σ| ≤ ‖h‖ := (abs_apply_le_norm (N := N) h σ)
            exact mul_le_mul_of_nonneg_left hσ (gibbs_pmf_nonneg (N := N) (H := H) σ)
          -- sum and rewrite.
          have hsum' :=
            (Finset.sum_le_sum (s := (Finset.univ : Finset (Config N)))
              (fun σ _ => hterm σ))
          -- rewrite the RHS as `(∑ gσ) * ‖h‖`.
          have hfactor :
              (∑ σ : Config N, (gibbs_pmf N H σ) * ‖h‖)
                = (∑ σ : Config N, gibbs_pmf N H σ) * ‖h‖ := by
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Config N)))
                (f := fun σ : Config N => gibbs_pmf N H σ) (a := ‖h‖)).symm
          -- Turn `hsum'` into the desired shape.
          simpa [hfactor] using hsum'
        -- assemble
        calc
          |∑ σ : Config N, gibbs_pmf N H σ * h σ|
              ≤ ∑ σ : Config N, |gibbs_pmf N H σ * h σ| := h_abs_le
          _ = ∑ σ : Config N, gibbs_pmf N H σ * |h σ| := h_abs_term
          _ ≤ (∑ σ : Config N, gibbs_pmf N H σ) * ‖h‖ := hsum_le
          _ = ‖h‖ := by simp [hs1]
      -- finish the opNorm bound
      -- `‖fderiv .. h‖ = |...|` since codomain is `ℝ`.
      have : ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H) h‖
            ≤ (1 / (N : ℝ)) * ‖h‖ := by
        -- rewrite using `h_eval` and the bound on the Gibbs sum
        -- avoid `simp` getting stuck on the absolute values; do it explicitly
        have :
            ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H) h‖
              = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N H σ * h σ| := by
          -- codomain is `ℝ`, so `‖x‖ = |x|`.
          simp [h_eval, Real.norm_eq_abs]
        -- apply the Gibbs-sum bound.
        calc
          ‖(fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H) h‖
              = (1 / (N : ℝ)) * |∑ σ : Config N, gibbs_pmf N H σ * h σ| := this
          _ ≤ (1 / (N : ℝ)) * ‖h‖ := by
                exact mul_le_mul_of_nonneg_left hsum_bound hN
      -- reorder scalar multiplication
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    -- absorb into the `C * (1 + ‖H‖)` profile with `m = 1`.
    have hcard_pos : 0 < Fintype.card (Config N) := by
      classical
      have : Nonempty (Config N) := ⟨fun _ => false⟩
      exact Fintype.card_pos
    have h1le : (1 : ℝ) ≤ (Fintype.card (Config N) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
    have hlog_nonneg : 0 ≤ Real.log (Fintype.card (Config N) : ℝ) :=
      Real.log_nonneg h1le
    have hC_ge1 : (1 : ℝ) ≤ C := by
      dsimp [C]
      nlinarith
    have h1 : (1 / (N : ℝ)) ≤ C * (1 + ‖H‖) := by
      have hone_le : (1 : ℝ) ≤ 1 + ‖H‖ := by nlinarith [norm_nonneg H]
      have h_one_le_mul : (1 : ℝ) ≤ C * (1 + ‖H‖) :=
        one_le_mul_of_one_le_of_one_le hC_ge1 hone_le
      have h_div_le_one : (1 / (N : ℝ)) ≤ (1 : ℝ) := by
        -- holds for all `N : ℕ` (including `N = 0`, since `1/0 = 0` in `ℝ`)
        cases N with
        | zero =>
            simp
        | succ n =>
            have hpos : (0 : ℝ) < (Nat.succ n : ℝ) := by exact_mod_cast (Nat.succ_pos n)
            -- `1/(n+1) ≤ 1` is a one-line inequality for positive denominators
            rw [div_le_one hpos]
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
      exact le_trans h_div_le_one h_one_le_mul
    -- final shape
    have : ‖fderiv ℝ (fun H : EnergySpace N => free_energy_density (N := N) H) H‖
          ≤ C * (1 + ‖H‖) := le_trans h_op h1
    simpa [C, pow_one] using this

/-- A convenient integrability corollary for Gaussian disorder. -/
lemma integrable_free_energy_density_of_gaussian
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {g : Ω → EnergySpace N} (hg : IsGaussianHilbert (Ω := Ω) (H := EnergySpace N) g) :
    Integrable (fun x => free_energy_density (N := N) (g x)) := by
  have hdiff : ContDiff ℝ 1 (fun H : EnergySpace N => free_energy_density (N := N) H) :=
    (contDiff_free_energy_density (N := N)).of_le (by simp)
  exact
    PhysLean.Probability.GaussianIBP.integrable_F_of_growth
      (g := g) (hg := hg) (hF_diff := hdiff)
      (hF_growth := hasModerateGrowth_free_energy_density (N := N))

end ModerateGrowth

end SpinGlass
