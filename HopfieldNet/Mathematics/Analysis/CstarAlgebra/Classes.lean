import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Module
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import HopfieldNet.Mathematics.aux
import Mathlib

open Finset Real Complex Matrix Quiver.Path

namespace Complex


variable {z : ℂ}

/-- The norm of a real number embedded in the complex numbers is its absolute value. -/
lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

theorem sq_eq_zero {R : Type*} [MonoidWithZero R] [NoZeroDivisors R] {x : R} : x ^ 2 = 0 ↔ x = 0 := by
  rw [pow_two, mul_eq_zero]
  exact or_self_iff

/-- An element of a nonempty set. -/
lemma Set.mem_of_nonempty {α : Type*} (s : Set α) (h : s.Nonempty) : ∃ x, x ∈ s := h

/--
An equality between real numbers implies an equality between their complex embeddings.
-/
lemma ofReal_eq_ofReal {r s : ℝ} : r = s → (r : ℂ) = (s : ℂ) := by
  intro h
  rw [h]

variable {ι : Type*} {z : ℂ}

/-- The square of the absolute value of a complex number is its norm squared. -/
lemma normSq_eq_abs_sq (z : ℂ) : Complex.normSq z = (norm z) ^ 2 := by
  exact Complex.normSq_eq_norm_sq z

/-- The square of the norm of a complex number is the sum of the squares of its real and imaginary
parts. -/
lemma norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm]; rw [← normSq_add_mul_I]
  simp [norm_eq_abs, ← normSq_eq_abs_sq, normSq_apply]

/-- The norm of the conjugate of a complex number is the same as the norm of the original number. -/
@[simp]
lemma RCLike.norm_conj {K} [RCLike K] (z : K) : ‖star z‖ = ‖z‖ := by exact norm_star z

/-- The real part of a sum is the sum of the real parts. -/
lemma RCLike.re_sum {F : Type*} [RCLike F] {v : ι → F} {s : Finset ι} :
    RCLike.re (∑ i ∈ s, v i) = ∑ i ∈ s, RCLike.re (v i) := by exact map_sum RCLike.re v s

/-- The real part of a product of complex numbers is less than or equal to the product of their norms.
This is a consequence of the Cauchy-Schwarz inequality. -/
lemma re_mul_le_norm (z w : ℂ) : re (z * w) ≤ ‖z‖ * ‖w‖ := by
  calc
    re (z * w) ≤ ‖z * w‖ := re_le_norm (z * w)
    _ = ‖z‖ * ‖w‖ := norm_mul z w

/-- If a sum of `f i` equals a sum of `g i`, and `f i ≤ g i` for all `i`, then `f i = g i` for all `i`. -/
lemma eq_of_sum_eq_of_le {s : Finset ι} {f g : ι → ℝ}
    (h_le : ∀ i ∈ s, f i ≤ g i) (h_sum_eq : ∑ i ∈ s, f i = ∑ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  intro i hi
  have h_sum_diff_eq_zero : ∑ j ∈ s, (g j - f j) = 0 := by
    rw [Finset.sum_sub_distrib, h_sum_eq, sub_self]
  have h_nonneg : ∀ j ∈ s, 0 ≤ g j - f j := fun j hj => sub_nonneg.mpr (h_le j hj)
  have h_all_zero : ∀ j ∈ s, g j - f j = 0 := by
    exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_diff_eq_zero
  exact (sub_eq_zero.mp (h_all_zero i hi)).symm

/-- A complex number whose norm equals its real part is a non-negative real number. -/
lemma eq_re_of_norm_eq (h : ‖z‖ = z.re) : z = z.re := by
  have h_re_nonneg : z.re ≥ 0 := by
    rw [← h]
    exact norm_nonneg z
  have : z.im ^ 2 = 0 := by
    have h_norm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := norm_sq_eq_re_sq_add_im_sq z
    rw [h, sq, sq] at h_norm_sq
    linarith
  refine Eq.symm ((fun {z w} ↦ Complex.ext_iff.mpr) ?_)
  simp_all only [ge_iff_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, and_self]

lemma eq_coe_re_of_mul_eq_norm_mul {z w : ℂ} (h : re (z * star w) = ‖z‖ * ‖w‖) :
    (z * star w) = ↑(re (z * star w)) := by
  have h_re_eq : (z * star w).re = ‖z * star w‖ := by
    rw [norm_mul, norm_star, h]
  exact eq_re_of_norm_eq (id (Eq.symm h_re_eq))

/-- The conjugate of a real number embedded in the complex numbers is the number itself. -/
lemma star_ofReal (r : ℝ) : star (r : ℂ) = r := by
  simp

/-- The product of a complex number and its conjugate is the square of its norm,
as a real number embedded in the complex plane. -/
lemma star_mul_self (z : ℂ) : z * star z = ↑(‖z‖ ^ 2) := by
  simpa [Matrix.star_eq_conjTranspose, normSq_eq_norm_sq] using mul_conj z

@[simp] lemma re_ofReal (r : ℝ) : (r : ℂ).re = r :=
rfl

/-- The square of the norm of a sum is the sum of the real parts of the products of each term
with the conjugate of the sum. -/
lemma norm_sq_eq_sum_re_mul_star {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) :
  ‖u‖ ^ 2 = ∑ i ∈ s, re (v i * star u) := by
  calc
    ‖u‖ ^ 2 = re (u * star u) := by rw [star_mul_self, re_ofReal]
    _ = re ((∑ i ∈ s, v i) * star u) := by rw [h_eq]
    _ = re (∑ i ∈ s, (v i * star u)) := by rw [sum_mul]
    _ = ∑ i ∈ s, re (v i * star u) := by rw [re_sum]

/-- If equality holds in the triangle inequality, then for each term `v i`, the equality
`re (v i * star u) = ‖v i‖ * ‖u‖` holds, where `u` is the sum. -/
lemma re_mul_star_eq_norm_mul_norm_of_triangle_eq {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) :
  ∀ i ∈ s, re (v i * star u) = ‖v i‖ * ‖u‖ := by
  have h_norm_u_sq : ‖u‖ ^ 2 = ∑ i ∈ s, re (v i * star u) :=
    norm_sq_eq_sum_re_mul_star h_eq
  have h_le : ∀ i ∈ s, re (v i * star u) ≤ ‖v i‖ * ‖u‖ := by
    intro i _
    calc re (v i * star u) ≤ ‖v i * star u‖ := re_le_norm _
    _ = ‖v i‖ * ‖star u‖ := by rw [norm_mul]
    _ = ‖v i‖ * ‖u‖ := by rw [norm_star]
  apply eq_of_sum_eq_of_le h_le
  calc
    ∑ i ∈ s, re (v i * star u) = ‖u‖ ^ 2 := h_norm_u_sq.symm
    _ = (∑ i ∈ s, ‖v i‖) * ‖u‖ := by rw [h_sum, pow_two]
    _ = ∑ i ∈ s, (‖v i‖ * ‖u‖) := by rw [sum_mul]

variable {ι : Type*} (s : Finset ι) {v : ι → ℂ}

/--
If `u = ∑ i in s, v i`, `‖u‖ = ∑ i in s, ‖v i‖`, and `u ≠ 0`, then each `v i`
is a **nonnegative real** multiple of `u`.
-/
lemma each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq {u : ℂ}
  (h_eq  : u = ∑ i ∈ s, v i)
  (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
  (h_ne  : u ≠ 0) :
  ∀ i ∈ s, ∃ k : ℝ, k ≥ 0 ∧ v i = (k : ℂ) * u := by
  have aligned := re_mul_star_eq_norm_mul_norm_of_triangle_eq h_eq h_sum
  have u_pos : 0 < ‖u‖ := norm_pos_iff.mpr h_ne
  intro i hi
  by_cases hv : v i = 0
  · use 0; simp [hv]
  let k := ‖v i‖ / ‖u‖
  have k_nonneg : 0 ≤ k := div_nonneg (norm_nonneg _) (norm_nonneg _)
  use k, k_nonneg
  have h : v i * star u = (‖v i‖ * ‖u‖ : ℂ) := by
    rw [← ofReal_mul, ← aligned i hi]
    exact eq_coe_re_of_mul_eq_norm_mul (aligned i hi)
  calc
    v i = (v i * star u) * u / (u * star u) := by rw [mul_assoc, mul_comm (star u), mul_div_cancel_right₀ _ (
      (CStarRing.mul_star_self_ne_zero_iff u).mpr h_ne)]
    _ = (‖v i‖ * ‖u‖ : ℂ) * u / (‖u‖ ^ 2 : ℂ) := by rw [h, star_mul_self, ofReal_pow]
    _ = (k : ℂ) * u := by
      rw [ofReal_div, ← ofReal_mul]
      field_simp [norm_ne_zero_iff.mpr h_ne]
      ring

/--
If `vi` is a non-negative real multiple `k` of a non-zero vector `u`, then `k` is the
ratio of their norms.
-/
lemma coeff_of_aligned_vector {u vi : ℂ} {k : ℝ}
    (h_aligned : vi = (k : ℂ) * u) (k_nonneg : k ≥ 0) (u_ne_zero : u ≠ 0) :
    k = ‖vi‖ / ‖u‖ := by
  have u_norm_ne_zero : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr u_ne_zero
  have h_norm_eq : ‖vi‖ = k * ‖u‖ := by
    rw [h_aligned, norm_mul, norm_ofReal, abs_of_nonneg k_nonneg]
  by_cases hvi_zero : vi = 0
  · have k_zero : k = 0 := by
      rw [h_aligned, mul_eq_zero] at hvi_zero
      cases hvi_zero
      subst h_aligned
      simp_all only [ge_iff_le, ne_eq, norm_eq_zero, not_false_eq_true, ofReal_eq_zero, ofReal_zero, zero_mul,
        norm_zero]
      rename_i h
      subst h h_aligned
      simp_all only [ge_iff_le, ne_eq, not_true_eq_false]
    simp [k_zero, hvi_zero, norm_zero, zero_div]
  · exact eq_div_of_mul_eq u_norm_ne_zero (id (Eq.symm h_norm_eq))

lemma sum_of_aligned_vectors_factors {u : ℂ} {v : ι → ℂ} {s : Finset ι}
    (h_eq  : u = ∑ i ∈ s, v i)
    (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
    (h_ne  : u ≠ 0) :
    ∑ i ∈ s, v i = (∑ i ∈ s, (‖v i‖ / ‖u‖ : ℂ)) * u := by
  have h_norm_ne : (‖u‖ : ℝ) ≠ 0 := by
    exact norm_ne_zero_iff.mpr h_ne
  have h_sum_div :
      (∑ i ∈ s, (‖v i‖ / ‖u‖ : ℂ)) =
      ((∑ i ∈ s, ‖v i‖) / ‖u‖ : ℂ) := by
    have h_real : (∑ i ∈ s, ‖v i‖ / ‖u‖) =
        (∑ i ∈ s, ‖v i‖) / ‖u‖ := by exact Eq.symm (sum_div s (fun i ↦ ‖v i‖) ‖u‖)
    simpa [ofReal_sum, ofReal_div] using congrArg (fun r : ℝ => (r : ℂ)) h_real
  have h_coeff :
      ((∑ i ∈ s, ‖v i‖) / ‖u‖ : ℂ) = 1 := by
    have h_coeff_real : (∑ i ∈ s, ‖v i‖) / ‖u‖ = (1 : ℝ) := by
      have h_eq : (∑ i ∈ s, ‖v i‖) = ‖u‖ := by
        simpa using h_sum.symm
      simp [h_eq, div_self h_norm_ne]
    simpa using congrArg (fun r : ℝ => (r : ℂ)) h_coeff_real
  calc
    ∑ i ∈ s, v i
        = u := by
          simpa using h_eq.symm
    _ = (1 : ℂ) * u := by simp
    _ = ((∑ i ∈ s, ‖v i‖) / ‖u‖ : ℂ) * u := by
          simp [h_coeff]
          subst h_eq
          simp_all only [ne_eq, ofReal_sum, one_mul]
    _ = (∑ i ∈ s, (‖v i‖ / ‖u‖ : ℂ)) * u := by
          simp [h_sum_div]

/-- If equality holds in the triangle inequality, the sum of the non-negative real multiples is 1.-/
lemma sum_of_multiples_is_one_of_triangle_eq
    {u : ℂ} {v : ι → ℂ} {s : Finset ι}
    (_  : u = ∑ i ∈ s, v i)
    (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖)
    (h_ne  : u ≠ 0) :
    ∑ i ∈ s, (‖v i‖ / ‖u‖) = 1 := by
  have h_norm_ne : (‖u‖ : ℝ) ≠ 0 := by
    exact norm_ne_zero_iff.mpr h_ne
  calc
    ∑ i ∈ s, ‖v i‖ / ‖u‖
        = (∑ i ∈ s, ‖v i‖) / ‖u‖ := by
          rw [← Finset.sum_div s (fun i => ‖v i‖) ‖u‖]
    _   = ‖u‖ / ‖u‖ := by
          simp [h_sum]
    _   = (1 : ℝ) := by
          simp [div_self h_norm_ne]

/-- 2) If `‖u‖ = ∑ i ∈ s, ‖v i‖` then each `v i` aligns with `u`. -/
lemma align_each_with_sum {u : ℂ} {v : ι → ℂ} {s : Finset ι}
  (h_eq : u = ∑ i ∈ s, v i) (h_sum : ‖u‖ = ∑ i ∈ s, ‖v i‖) (h_ne : u ≠ 0) :
  ∀ i ∈ s, (‖u‖ : ℂ) • v i = (‖v i‖ : ℂ) • u := by
  have h_norm_ne_zero : ‖u‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  intro i hi
  have ⟨k, k_nonneg, hk⟩ :=
    each_term_is_nonneg_real_multiple_of_sum_of_triangle_eq s h_eq h_sum h_ne i hi
  have coeff_mul : k * ‖u‖ = ‖v i‖ := by
    field_simp [coeff_of_aligned_vector hk k_nonneg h_ne, h_norm_ne_zero]
  calc
    (‖u‖ : ℂ) • v i
      = ↑‖u‖ * v i := by simp [smul_eq_mul]
    _ = ↑‖u‖ * (k * u) := by rw [hk]
    _ = (k * ↑‖u‖) * u := by ring
    _ = ↑(k * ‖u‖) * u := by simp [ofReal_mul]
    _ = ↑‖v i‖ * u := by rw [coeff_mul]
    _ = (‖v i‖ : ℂ) • u := by simp [smul_eq_mul, mul_comm]

variable {n : Type*} [Fintype n]
/-- If equality holds in thetriangle inequality for a sum of complex vectors,
    then all vectors must point in the same direction. -/
theorem triangle_equality_iff_aligned {v : n → ℂ} (hv_nonzero : ∀ i, v i ≠ 0) [Nonempty n] :
    ‖∑ i, v i‖ = ∑ i, ‖v i‖ ↔
    ∃ (c : ℂ), ‖c‖ = 1 ∧ ∀ i, v i = (‖v i‖ : ℂ) * c := by
  constructor
  · intro h_eq
    let u := ∑ i, v i
    have hu_nonzero : u ≠ 0 := by
      intro h_u_zero
      have h_sum_zero : (∑ i, v i) = 0 := h_u_zero
      rw [h_sum_zero, norm_zero, eq_comm] at h_eq
      rw [sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg (v i))] at h_eq
      · obtain ⟨i⟩ := univ_nonempty (α := n)
        specialize hv_nonzero i
        specialize h_eq i (mem_univ i)
        rw [norm_eq_zero] at h_eq
        contradiction
    let c := u / ↑‖u‖
    use c
    have hc_norm_one : ‖c‖ = 1 := by
      rw [norm_div, Complex.norm_ofReal, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hu_nonzero)]
    refine ⟨hc_norm_one, fun i ↦ ?_⟩
    have h_aligned := align_each_with_sum (s := univ) rfl h_eq hu_nonzero i (Finset.mem_univ i)
    rw [smul_eq_mul, smul_eq_mul] at h_aligned
    calc v i
      _ = (↑‖v i‖ * u) / ↑‖u‖ :=
        eq_div_of_mul_eq (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu_nonzero))
          (by rw [← h_aligned, mul_comm])
      _ = ↑‖v i‖ * (u / ↑‖u‖) := by rw [mul_div_assoc]
      _ = ↑‖v i‖ * c := rfl
  · rintro ⟨c, hc_norm_one, h_aligned⟩
    calc ‖∑ i, v i‖
        = ‖∑ i, (‖v i‖ : ℂ) * c‖ := by congr; ext i; exact h_aligned i
      _ = ‖(∑ i, ↑‖v i‖) * c‖ := by rw [Finset.sum_mul]
      _ = ‖∑ i, (‖v i‖ : ℂ)‖ * ‖c‖ := by rw [norm_mul]
      _ = ‖(↑(∑ i, ‖v i‖) : ℂ)‖ * ‖c‖ := by rw [ofReal_sum]
      _ = |∑ i, ‖v i‖| * ‖c‖ := by rw [Complex.norm_ofReal]
      _ = (∑ i, ‖v i‖) * ‖c‖ := by rw [abs_of_nonneg (sum_nonneg (fun i _ => norm_nonneg _))]
      _ = (∑ i, ‖v i‖) * 1 := by rw [hc_norm_one]
      _ = ∑ i, ‖v i‖ := by rw [mul_one]

end Complex
