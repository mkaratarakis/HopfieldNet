import Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Primitive

set_option linter.style.longLine false

/-!
# Perron-Frobenius Theorem: Uniqueness of the Eigenvector

This file proves that for a primitive, non-negative matrix, the strictly positive
eigenvector corresponding to the Perron root `r` is unique up to a positive
scalar multiple. This corresponds to part (d) of Theorem 1.1 in Seneta's
"Non-negative Matrices and Markov Chains".

The proof strategy is as follows:
1. Given two strictly positive eigenvectors `v` and `w` for the same eigenvalue `r`.
2. Construct a new vector `z = v - c • w`, where `c` is the minimum of the
   component-wise ratios `vᵢ / wᵢ`.
3. By construction, `z` is a non-negative vector, and at least one of its
   components is zero.
4. Show that `z` is also an eigenvector of `A` with eigenvalue `r`.
5. Use the primitivity of `A` to show that if `z` were non-zero, then `A^k * z`
   would be strictly positive for a large enough `k`.
6. However, `A^k * z = r^k • z`, which must have a zero component since `z` does.
   This is a contradiction.
7. Thus, `z` must be the zero vector, which implies `v = c • w`.
-/

namespace Matrix
variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ} {r : ℝ}

/--
A non-zero, non-negative eigenvector `z` of a primitive matrix `A` corresponding to a
positive eigenvalue `r` cannot have any zero entries. This is a crucial lemma for
the uniqueness and dominance proofs.
-/
lemma eigenvector_no_zero_entries_of_primitive (hA_prim : IsPrimitive A) (_ : 0 < r)
    {z : n → ℝ} (h_eig : A *ᵥ z = r • z) (hz_nonneg : ∀ i, 0 ≤ z i) (hz_ne_zero : z ≠ 0)
    (i₀ : n) (hi₀_zero : z i₀ = 0) :
    False := by
  rcases hA_prim with ⟨_, ⟨k, _, hA_k_pos⟩⟩
  have h_Ak_z_eig : (A ^ k) *ᵥ z = (r ^ k) • z := by
    have h_gen : ∀ m, (A ^ m) *ᵥ z = (r ^ m) • z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc (A ^ (m + 1)) *ᵥ z
            = A *ᵥ (A ^ m *ᵥ z)        := by rw [pow_mulVec_succ]
        _ = A *ᵥ (r ^ m • z)          := by rw [ih]
        _ = r ^ m • (A *ᵥ z)          := by rw [mulVec_smul]
        _ = r ^ m • (r • z)           := by rw [h_eig]
        _ = (r ^ m * r) • z           := by rw [smul_smul]
        _ = (r ^ (m + 1)) • z         := by rw [pow_succ']; rw [@pow_mul_comm']
    exact h_gen k
  have h_rhs_zero : ((r ^ k) • z) i₀ = 0 := by
    simp [hi₀_zero]
  have h_lhs_pos : 0 < ((A ^ k) *ᵥ z) i₀ :=
    positive_mul_vec_of_nonneg_vec hA_k_pos hz_nonneg hz_ne_zero i₀
  rw [h_Ak_z_eig] at h_lhs_pos
  exact lt_irrefl 0 (h_rhs_zero ▸ h_lhs_pos)

/--
**Uniqueness of the Positive Eigenvector for Primitive Matrices**

The positive eigenvector of a primitive matrix `A` corresponding to a positive eigenvalue `r`
is unique up to a positive scalar multiple. This corresponds to Theorem 1.1 (d) in Seneta.
-/
theorem uniqueness_of_positive_eigenvector (hA_prim : IsPrimitive A) (hr_pos : 0 < r)
    (v w : n → ℝ) (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = r • w)
    (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i) :
    ∃ c : ℝ, 0 < c ∧ v = c • w := by
  let c := Finset.univ.inf' Finset.univ_nonempty (fun i => v i / w i)
  have hc_pos : 0 < c := by
    apply Finset.inf'_pos Finset.univ_nonempty
    intro i _
    exact div_pos (hv_pos i) (hw_pos i)
  let z := v - c • w
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    have hc_le_ratio : c ≤ v i / w i := Finset.inf'_le _ (Finset.mem_univ i)
    exact (le_div_iff₀ (hw_pos i)).mp hc_le_ratio
  have hz_eig : A *ᵥ z = r • z := by
    dsimp [z]; simp only [mulVec_sub]; simp only [mulVec_smul]; simp only [ hv_eig]; simp only [hw_eig]; simp only [smul_sub]; rw [smul_comm]
  by_cases h_z_is_zero : z = 0
  · use c, hc_pos
    ext i
    simpa [z, sub_eq_zero] using congr_fun h_z_is_zero i
  · have hz_has_zero : ∃ i₀, z i₀ = 0 := by
      obtain ⟨i₀, _, hi₀_eq_inf⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => v i / w i)
      use i₀
      simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      rw [← div_eq_iff (hw_pos i₀).ne']
      rw [← hi₀_eq_inf]
    obtain ⟨i₀, hi₀_zero⟩ := hz_has_zero
    have h_contra := eigenvector_no_zero_entries_of_primitive hA_prim hr_pos hz_eig hz_nonneg h_z_is_zero i₀ hi₀_zero
    exact h_contra.elim

end Matrix
