import Riemann.PhysLean.SpinGlass.Algebra

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

/-!
# Guerra's bound: algebraic core (finite `N`)

The analytic part of Guerra's interpolation (differentiation under the disorder expectation,
Gaussian IBP, and endpoint evaluation) is substantial.  This file isolates the *finite‑`N`
algebraic* inequality that is the key ingredient once the derivative identity is established.

See `SpinGlass/Defs.lean` for the underlying trace computations and for the proof that the
relevant combination is bounded by \((β^2/4)(1-q)^2\) via nonnegativity of a Gibbs average of a
square.

## References
- M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Ch. 1, §1.3, Eq. (1.65)
  (algebraic rewriting of the interpolation derivative as a difference of squares).
-/

variable {N : ℕ} {β : ℝ}

/--
**Finite‑`N` Guerra derivative bound (algebraic part).**

This is the inequality corresponding to Talagrand's Eq. (1.65) *after* Gaussian IBP has reduced
the derivative of the interpolated expected free energy to a trace of the covariance kernels
against the Hessian. Generalized for RSB with functional order parameter `xi`.

Reference: Talagrand, Vol. I, Ch. 1, §1.3, Eq. (1.65).
-/
theorem guerra_derivative_bound_algebra_core (hN : 0 < N) (H : EnergySpace N) (xi : ℝ → ℝ) :
    let term_sk := (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    let term_simple := (∑ σ, ∑ τ, simple_cov_kernel N β xi σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    (1 / 2) * (term_sk - term_simple) = (β^2 / 2) * ((1/2 - xi 1) - ∑ σ, ∑ τ, gibbs_pmf N H σ * gibbs_pmf N H τ * ((overlap N σ τ)^2 / 2 - xi (overlap N σ τ))) :=
  SpinGlass.guerra_derivative_bound_algebra (N := N) (β := β) (xi := xi) hN H

end SpinGlass
