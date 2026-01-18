import Riemann.PhysLean.SpinGlass.Defs

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass.Algebra

/-!
# Algebraic identities for the finite‑`N` SK model

This file packages the *purely algebraic* steps used in Guerra's interpolation:

- trace identities for the SK and simple covariance kernels (proved in `Defs.lean`);
- the “square completion” identity which turns a difference of traces into a
  negative Gibbs average of a square.

## References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3, in particular the
  algebraic manipulation leading to Eq. (1.65).
-/

variable {N : ℕ} {β : ℝ}

/--
Re-export: trace identity for the SK covariance kernel.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (trace computation entering Eq. (1.65)).
-/
lemma trace_sk (hN : 0 < N) (H : EnergySpace N) :
    (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β^2 / 2) * (1 - ∑ σ, ∑ τ,
        gibbs_pmf N H σ * gibbs_pmf N H τ * (overlap N σ τ)^2) :=
  SpinGlass.trace_sk (N := N) (β := β) (hN := hN) (H := H)

/--
Re-export: trace identity for the simple covariance kernel.

Reference: Talagrand, Vol. I, Ch. 1, §1.3 (generalized for RSB).
-/
lemma trace_simple (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ)) =
      (β^2) * (xi 1 - ∑ σ, ∑ τ,
        gibbs_pmf N H σ * gibbs_pmf N H τ * xi (overlap N σ τ)) :=
  SpinGlass.trace_simple (N := N) (β := β) (xi := xi) (hN := hN) (H := H)

/--
**Square completion (Talagrand, Eq. (1.65), algebraic step).**

For real numbers `r` and `q`,
\[
\frac12(1-r^2) - q(1-r) = \frac12\big((1-q)^2 - (r-q)^2\big).
\]
-/
lemma square_completion (r q : ℝ) :
    (1 / 2) * (1 - r^2) - q * (1 - r) = (1 / 2) * ((1 - q)^2 - (r - q)^2) := by
  ring

end SpinGlass.Algebra
