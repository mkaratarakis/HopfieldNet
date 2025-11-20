import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Dominance

namespace Matrix

open Matrix CollatzWielandt Quiver.Path

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-!

## Main Perron-Frobenius Theorem for Stochastic Matrices

-/

/--
**Perron-Frobenius Theorem for Column-Stochastic Matrices**.

An irreducible, non-negative matrix with column sums equal to 1 (i.e., column-stochastic)
has a Perron root of 1, and there exists a unique (up to scaling) strictly positive
eigenvector `v` for this eigenvalue. This stationary vector is unique when constrained
to the standard simplex.
-/
theorem exists_positive_eigenvector_of_irreducible_stochastic
    {A : Matrix n n ℝ} (hA_irred : Irreducible A) (h_col_stoch : ∀ j, ∑ i, A i j = 1) :
    ∃! (v : stdSimplex ℝ n), A *ᵥ v.val = v.val := by
  have hA_nonneg : ∀ i j, 0 ≤ A i j := hA_irred.1
  let A_T := Aᵀ
  have hAT_nonneg : ∀ i j, 0 ≤ A_T i j := fun i j => hA_nonneg j i
  have hAT_row_sum : ∀ i, ∑ j, A_T i j = 1 := by
    simpa [A_T, transpose_apply] using h_col_stoch
  have h_ones_eig : A_T *ᵥ (fun _ => 1) = 1 • (fun _ => 1) := by
    simpa using row_sum_eigenvalue hAT_nonneg 1 hAT_row_sum
  have hAT_irred : Irreducible A_T := hA_irred.transpose hA_nonneg
  have r_AT_eq_one : perronRoot_alt A_T = 1 := by
    have h :=
      eigenvalue_is_perron_root_of_positive_eigenvector
        (A := A_T) (r := 1) (v := fun _ => 1)
        hAT_irred hAT_nonneg (by norm_num) (by intro _; exact Real.zero_lt_one)
    aesop
  have r_A_eq_one : perronRoot_alt A = 1 := by
    exact (perronRoot_transpose_eq A hA_irred).trans r_AT_eq_one
  obtain ⟨v_raw, ⟨r, hr_pos, h_eig⟩, v_raw_unique⟩ := pft_irreducible hA_irred
  let v : stdSimplex ℝ n := v_raw
  have h_eig_one : A *ᵥ v.val = v.val := by
    have r_eq_perron : r = perronRoot_alt A := by
      apply eigenvalue_is_perron_root_of_positive_eigenvector
      · exact hA_irred
      · exact hA_nonneg
      · exact hr_pos
      · have v_ne_zero : v.val ≠ 0 := ne_zero_of_mem_stdSimplex v.property
        have hv_nonneg : ∀ i, 0 ≤ v.val i := v.property.1
        exact eigenvector_is_positive_of_irreducible hA_irred h_eig hv_nonneg v_ne_zero
      · exact h_eig
    have : A *ᵥ v.val = (perronRoot_alt A) • v.val := by
      aesop
    simpa [r_A_eq_one, one_smul] using this
  refine ⟨v, h_eig_one, ?_⟩
  intro w hw_eig
  have v_pos : ∀ i, 0 < v.val i := by
    have v_ne_zero : v.val ≠ 0 := ne_zero_of_mem_stdSimplex v.property
    have hv_nonneg : ∀ i, 0 ≤ v.val i := v.property.1
    exact fun i ↦
      eigenvector_no_zero_entries_of_irreducible hA_irred hr_pos h_eig hv_nonneg v_ne_zero i
  have w_pos : ∀ i, 0 < w.val i := by
    have hw_nonneg : ∀ i, 0 ≤ w.val i := w.property.1
    have hw_ne_zero : w.val ≠ 0 := ne_zero_of_mem_stdSimplex w.property
    have hw_eig' : A *ᵥ w.val = (1 : ℝ) • w.val := by
      simpa [one_smul] using hw_eig
    exact eigenvector_is_positive_of_irreducible hA_irred hw_eig' hw_nonneg hw_ne_zero
  obtain ⟨c, hc_pos, hc_eq⟩ :=
    uniqueness_of_positive_eigenvector_gen hA_irred
      (by norm_num : (0 : ℝ) < 1)
      v_pos w_pos
      (by simpa [one_smul] using h_eig_one)
      (by simpa [one_smul] using hw_eig)
  have h_sum_v : ∑ i, v.val i = 1 := v.property.2
  have h_sum_w : ∑ i, w.val i = 1 := w.property.2
  have hc_one : c = 1 := by
    calc
      c = c * 1 := (mul_one c).symm
      _ = c * (∑ i, w.val i) := by simp [h_sum_w]
      _ = ∑ i, c * w.val i := by rw [Finset.mul_sum]
      _ = ∑ i, v.val i := by simp [hc_eq, smul_eq_mul]
      _ = 1 := h_sum_v
  exact Subtype.val_injective (by simp [hc_eq, hc_one, one_smul])

end Matrix
