import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Uniqueness

open Quiver.Path
namespace Matrix
open Quiver

open CollatzWielandt
variable {n : Type*} [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- If `A` is irreducible then so is `1 + A`. -/
theorem Irreducible.add_one (h_irred : Irreducible A) : Irreducible (1 + A) := by
  let B := (1 : Matrix n n ℝ) + A
  constructor
  · intro i j
    by_cases h : i = j
    · subst h
      simpa [B] using by
        have : (0 : ℝ) ≤ A i i := h_irred.1 i i
        linarith
    · simpa [B, h] using h_irred.1 i j
  · intro i j
    rcases h_irred.2 i j with ⟨pA, hpA_pos⟩
    letI GA : Quiver n := toQuiver A
    let GB : Quiver n := toQuiver B
    have arrow_map : ∀ {u v : n}, GA.Hom u v → GB.Hom u v := by
      intro u v e
      change 0 < B u v
      by_cases h_eq : u = v
      · subst h_eq
        have : (0 : ℝ) < 1 + A u u := by
          have : (0 : ℝ) < A u u := e
          linarith
        simpa [B] using this
      · simpa [B, h_eq] using e
    have hB_diag_pos : ∀ i, 0 < B i i := by
      intro i
      have : (0 : ℝ) < 1 + A i i := by
        have hAi : 0 ≤ A i i := h_irred.1 i i
        linarith
      simpa [B] using this
    have rec_path : ∀ {u v : n}, GA.Path u v → GB.Path u v := by
      intro u v q
      induction q with
      | nil            => exact .nil
      | cons q' e ih   => exact .cons ih (arrow_map e)
    let loop : Path i i := (Path.nil : Path i i).cons (hB_diag_pos i)
    let pB : Path i j := loop.comp (rec_path pA)
    have hpB_len : pB.length > 0 := by
      rw [@length_comp]
      simp only [le_refl, gt_iff_lt, add_pos_iff, List.Nat.eq_of_le_zero]
      simp_all only [gt_iff_lt, cons_eq_comp_toPath, nil_comp, length_toPath, Nat.lt_one_iff,
        pos_of_gt, true_or, B, GA, GB, loop]
    have hpB_pos :
        Quiver.Path.length pB > 0 := by
      exact hpB_len
    exact ⟨pB, hpB_pos⟩

/-
A non-zero, non-negative eigenvector of an irreducible matrix is
in fact strictly positive.
-/
lemma eigenvector_no_zero_entries_of_irreducible [Fintype n]
    {r : ℝ} (hA_irred : Irreducible A) (_ : 0 < r)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  by_contra h_has_zero
  push_neg at h_has_zero
  obtain ⟨i₀, hi₀_zero⟩ := h_has_zero
  let S : Set n := { i | 0 < v i }
  let T : Set n := { i | v i = 0 }
  have hS_nonempty : S.Nonempty := exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  have hT_nonempty : T.Nonempty := ⟨i₀, by simp [T, le_antisymm hi₀_zero (hv_nonneg i₀)]⟩
  have hT_ne_univ : T ≠ Set.univ := by
    intro h_univ
    have hv_zero : v = 0 := by
      funext i
      have : i ∈ T := by
        have : i ∈ (Set.univ : Set n) := by trivial
        simp_all [ne_eq, Set.mem_univ, T, S]
      simpa [T] using this
    exact hv_ne_zero hv_zero
  obtain ⟨j, hj_T, i, hi_not_T, h_Aji_pos⟩ :=
    hA_irred.exists_edge_out T hT_nonempty hT_ne_univ
  have vi_pos : 0 < v i := by
    have h_vi_ne_zero : v i ≠ 0 := by
      intro h_eq
      have : i ∈ T := by simp [T, h_eq]
      exact hi_not_T this
    exact lt_of_le_of_ne (hv_nonneg i) (Ne.symm h_vi_ne_zero)
  have vj_zero : v j = 0 := by
    have : j ∈ T := hj_T
    simpa [T] using this
  have h_Av_j_zero : (A *ᵥ v) j = 0 := by
    have h_rvj_zero : (r • v) j = 0 := by
      simp [Pi.smul_apply, vj_zero]
    have h_comp := congrArg (fun f : n → ℝ => f j) h_eig
    simpa [h_rvj_zero] using h_comp
  have h_terms_nonneg : ∀ k, 0 ≤ A j k * v k :=
    fun k => mul_nonneg (hA_irred.1 _ _) (hv_nonneg k)
  have h_Aji_vi_zero : A j i * v i = 0 := by
    by_cases h_eq : A j i * v i = 0
    · exact h_eq
    · have h_pos : 0 < A j i * v i := by
        have h_nonneg_i := h_terms_nonneg i
        exact lt_of_le_of_ne h_nonneg_i (Ne.symm h_eq)
      have h_sum_pos : 0 < ∑ k : n, A j k * v k := by
        have h_mem : i ∈ (Finset.univ : Finset n) := by simp
        have h_nonneg_fun : ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A j k * v k :=
          fun k _ => h_terms_nonneg k
        exact sum_pos_of_mem h_nonneg_fun i h_mem h_pos
      have : (∑ k : n, A j k * v k) = 0 := by
        simpa [mulVec, dotProduct] using h_Av_j_zero
      exact (lt_irrefl (0 : ℝ) (by simp [this] at h_sum_pos)).elim
  have h_Aji_zero : A j i = 0 :=
    (mul_eq_zero.mp h_Aji_vi_zero).resolve_right vi_pos.ne'
  have : (0 : ℝ) < 0 := by
    simp [h_Aji_zero] at h_Aji_pos
  exact this.false

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- **Perron–Frobenius, irreducible case (Existence part)**
If `A` is a non-negative irreducible matrix, then there exists a strictly positive eigenvalue `r > 0`
and a strictly positive eigenvector `v` (`∀ i, 0 < v i`) such that `A *ᵥ v = r • v`.

The proof uses the auxiliary matrix `B = 1 + A`, which is primitive, to apply the Perron-Frobenius theorem
for primitive matrices and translate the result back to `A`. -/
theorem exists_positive_eigenvector_of_irreducible
    (hA_irred : Irreducible A) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  -- 1.  We add the identity: `B := 1 + A`.
  let B : Matrix n n ℝ := 1 + A
  -- 1a.  Non-negativity of `B`.
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    intro i j
    by_cases h_eq : i = j
    · subst h_eq
      have : (0 : ℝ) ≤ 1 + A i i := by
        have hAi : 0 ≤ A i i := hA_irred.1 i i
        linarith
      simpa [B] using this
    · have : 0 ≤ A i j := hA_irred.1 i j
      simpa [B, h_eq] using this
  -- 1b.  Positive diagonal entries of `B`.
  have hB_diag_pos : ∀ i, 0 < B i i := by
    intro i
    have : (0 : ℝ) < 1 + A i i := by
      have hAi : 0 ≤ A i i := hA_irred.1 i i
      linarith
    simpa [B] using this
  -- 1c.  `B` is irreducible.
  have hB_irred : Irreducible (1 + A) := hA_irred.add_one
  -- 1d.  `B` is primitive.
  have hB_prim : IsPrimitive B :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  -- 2.  Primitive Perron–Frobenius applied to `B`.
  obtain ⟨rB, v, hrB_pos, hv_pos, h_eig_B⟩ :=
    exists_positive_eigenvector_of_primitive (A := B) hB_prim hB_nonneg
  -- 3.  We translate the eigen-relation for `B` to one for `A`.
  have h_eig_A : A *ᵥ v = (rB - 1) • v := by
    have h_exp : v + A *ᵥ v = rB • v := by
      simpa [B, add_mulVec, one_mulVec] using h_eig_B
    have : A *ᵥ v = rB • v - v := eq_sub_of_add_eq' h_exp
    simpa [one_smul, sub_smul] using this
  -- 4.  We show that `rB - 1 > 0`.
  classical
  letI GA : Quiver n := toQuiver A
  -- 4a.  We find a positive entry of `A`.
  have h_pos_entry : ∃ i j, 0 < A i j := by
    let i₀ : n := Classical.arbitrary n
    rcases hA_irred.2 i₀ i₀ with ⟨⟨p₀, hp₀_len⟩⟩
    have h_pos_len : p₀.length > 0 := hp₀_len
    rcases Quiver.Path.path_decomposition_first_edge p₀ h_pos_len with
      ⟨j, e, -, -, -⟩
    exact ⟨i₀, j, e⟩
  rcases h_pos_entry with ⟨i₀, j₀, hA_pos⟩
  -- 4b.  The `i₀`-component of `A * v` is positive.
  have hAv_i₀_pos : 0 < (A *ᵥ v) i₀ := by
    have hvj₀_pos : 0 < v j₀ := hv_pos j₀
    have h_nonneg :
        ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A i₀ k * v k := by
      intro k _
      exact mul_nonneg (hA_irred.1 _ _) (le_of_lt (hv_pos k))
    have h_sum_pos :
        0 < ∑ k, A i₀ k * v k := by
      have h_mem : j₀ ∈ (Finset.univ : Finset n) := by simp
      have h_pos_term : 0 < A i₀ j₀ * v j₀ := by
        exact mul_pos hA_pos hvj₀_pos
      exact sum_pos_of_mem h_nonneg j₀ h_mem h_pos_term
    simpa [mulVec_apply] using h_sum_pos
  -- 4c.  We use the `i₀`-component of the eigen-equation for `B`.
  have h_comp_eq :
      (v i₀) + (A *ᵥ v) i₀ = rB * v i₀ := by
    have := congr_fun h_eig_B i₀
    simpa [B, add_mulVec, one_mulVec, add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hrB_gt_one : 1 < rB := by
    have hv_i₀_pos : 0 < v i₀ := hv_pos i₀
    have h_lhs_gt : v i₀ < rB * v i₀ := by
      have : v i₀ + (A *ᵥ v) i₀ > v i₀ := by
        have : (A *ᵥ v) i₀ > 0 := hAv_i₀_pos; linarith
      simpa [h_comp_eq] using this
    exact ((mul_lt_mul_iff_of_pos_right hv_i₀_pos).1
            (by simpa [one_mul] using h_lhs_gt))
  have hrA_pos : 0 < rB - 1 := sub_pos.mpr hrB_gt_one
  exact ⟨rB - 1, v, hrA_pos, hv_pos, h_eig_A⟩

omit [Nonempty n] in
/-! A non-zero, non-negative eigenvector of an irreducible matrix is in fact **strictly** positive. -/
lemma eigenvector_is_positive_of_irreducible {r : ℝ}
    (hA_irred : Irreducible A)
    {v : n → ℝ} (h_eig : A *ᵥ v = r • v)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < v i := by
  by_contra h_has_nonpos
  push_neg at h_has_nonpos        -- `∃ i, v i ≤ 0`
  rcases h_has_nonpos with ⟨i₀, hvi₀_le⟩
  let S : Set n := {i | 0 < v i}
  let T : Set n := {i | v i = 0}
  have h_partition  : ∀ i, i ∈ S ↔ v i > 0 := by
    intro i; simp [S]
  have h_complement : ∀ i, i ∈ T ↔ v i = 0 := by
    intro i; simp [T]
  have hS_nonempty : S.Nonempty :=
    exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  have hT_nonempty : T.Nonempty := by
    have h_eq : v i₀ = 0 := by
      have : 0 ≤ v i₀ := hv_nonneg i₀
      exact le_antisymm hvi₀_le this
    exact ⟨i₀, by simp [T, h_eq]⟩
  have hS_ne_univ : (S : Set n) ≠ Set.univ := by
    intro h_univ
    have : (0 : ℝ) < 0 := by
      have : 0 < v i₀ := by
        have : i₀ ∈ S := by
          have : i₀ ∈ (Set.univ : Set n) := by trivial
          simp_all only [ne_eq, Set.mem_setOf_eq, gt_iff_lt, implies_true, Set.mem_univ, S, T]
        simpa [S] using this
      have : v i₀ = 0 := by
        have : 0 ≤ v i₀ := hv_nonneg i₀
        exact le_antisymm hvi₀_le this
      simpa [this] using ‹0 < v i₀›
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨j, i, hjT, hiS, hAji_pos⟩ :=
    exists_connecting_edge_of_irreducible
      (A := A) hA_irred hv_nonneg S T hS_nonempty hT_nonempty
      h_partition h_complement
  have vj_zero : v j = 0 := by
    have : j ∈ T := hjT
    simpa [T] using this
  have h_Av_j_zero : (A *ᵥ v) j = 0 := by
    have hrvj : (r • v) j = 0 := by simp [vj_zero]
    have h_eq := congrArg (fun f : n → ℝ => f j) h_eig
    simpa [hrvj] using h_eq
  have h_nonneg : ∀ k ∈ (Finset.univ : Finset n), 0 ≤ A j k * v k := by
    intro k _
    exact mul_nonneg (hA_irred.1 j k) (hv_nonneg k)
  have h_Aji_vi_zero : A j i * v i = 0 := by
    have h_sum_zero : (∑ k, A j k * v k) = 0 := by
      simpa [mulVec_apply] using h_Av_j_zero
    have h_all_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).1 h_sum_zero
    exact h_all_zero i (Finset.mem_univ i)
  have vi_pos : 0 < v i := by simpa [S] using hiS
  have h_Aji_zero : A j i = 0 :=
    (mul_eq_zero.mp h_Aji_vi_zero).resolve_right vi_pos.ne'
  exact (lt_irrefl (0 : ℝ)) (by simp [h_Aji_zero] at hAji_pos)

open Finset
/--
Given an irreducible non-negative matrix `A` and two strictly positive
eigenvectors for the same positive eigenvalue, they differ by a positive
scalar.
-/
theorem uniqueness_of_positive_eigenvector_gen
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} {r : ℝ} (hA_irred : Irreducible A) (hr_pos : 0 < r)
    {v w : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (hw_pos : ∀ i, 0 < w i)
    (hv_eig : A *ᵥ v = r • v) (hw_eig : A *ᵥ w = r • w) :
    ∃ c : ℝ, 0 < c ∧ v = c • w := by
  -- 1.  c := infᵢ (vᵢ / wᵢ)
  let c : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : n => v i / w i)
  have hc_pos : 0 < c := by
    apply Finset.inf'_pos Finset.univ_nonempty
    intro i _
    exact div_pos (hv_pos i) (hw_pos i)
  -- 2.  z := v − c•w  (still an eigenvector)
  let z : n → ℝ := v - c • w
  have hz_eig : A *ᵥ z = r • z := by
    calc
      A *ᵥ z
          = A *ᵥ v - A *ᵥ (c • w) := by
              simp only [mulVec_sub, z]
      _   = r • v - c • (r • w) := by
              simp only [hv_eig, mulVec_smul, hw_eig]
      _   = r • (v - c • w) := by
              rw [smul_sub, smul_comm, ← smul_assoc]
      _   = r • z := by
              simp only [z]
  -- 3.  z ≥ 0
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    have h_le : c ≤ v i / w i :=
      Finset.inf'_le _ (Finset.mem_univ _)
    have h_mul : c * w i ≤ v i := by
      exact (le_div_iff₀ (hw_pos i)).mp h_le
    have : 0 ≤ v i - c * w i := sub_nonneg.mpr h_mul
    simpa [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  -- 4.  analyse `z`
  by_cases hz_zero : z = 0
  · -- 4a. (`z = 0`)  ⇒  `v = c • w`
    refine ⟨c, hc_pos, ?_⟩
    have h_v_eq : v = c • w := by
      have : v - c • w = 0 := by
        simpa [z] using hz_zero
      exact (sub_eq_zero.1 this)
    exact h_v_eq
  · -- 4b. (`z ≠ 0`)  ⇒  contradiction
    have hz_pos : ∀ i, 0 < z i :=
      eigenvector_no_zero_entries_of_irreducible
        hA_irred hr_pos hz_eig hz_nonneg hz_zero
    -- the infimum is attained
    obtain ⟨i₀, _, h_inf_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n => v i / w i)
    -- at the attaining index we must have `z i₀ = 0`, contradiction
    have hzi₀_zero : z i₀ = 0 := by
      have hv_eq : v i₀ = c * w i₀ := by
        have hw_ne : w i₀ ≠ 0 := (ne_of_gt (hw_pos i₀))
        have h_div : v i₀ / w i₀ = c := by
          simpa using h_inf_eq.symm
        have : v i₀ = (v i₀ / w i₀) * w i₀ := by
          field_simp [hw_ne]
        simpa [h_div] using this
      simp only [Pi.sub_apply, hv_eq, Pi.smul_apply, smul_eq_mul, sub_self, z]
    have : 0 < z i₀ := hz_pos i₀
    have : (0 : ℝ) < 0 := by
      simp only [hzi₀_zero, lt_self_iff_false, z] at this
    simp_all only [div_pos_iff_of_pos_left, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, sub_nonneg, sub_pos, mem_univ, lt_self_iff_false, z, c]


/-- **Perron–Frobenius, primitive case (existence, positvity and uniqueness)** -/
theorem pft_primitive
    {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_prim : IsPrimitive A)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ) (_ : r > 0), A *ᵥ v.val = r • v.val := by
  obtain ⟨r, v_raw, hr_pos, hv_raw_pos, hv_raw_eig⟩ :=
    exists_positive_eigenvector_of_primitive hA_prim hA_nonneg
  let s : ℝ := ∑ i, v_raw i
  have hs_pos : 0 < s :=
    Finset.sum_pos (fun i _ ↦ hv_raw_pos i) Finset.univ_nonempty
  have hs_ne  : s ≠ 0 := ne_of_gt hs_pos
  let v0 : n → ℝ := s⁻¹ • v_raw
  have hv0_nonneg : ∀ i, 0 ≤ v0 i := by
    intro i
    have h₁ : 0 ≤ s⁻¹   := inv_nonneg.mpr (le_of_lt hs_pos)
    have h₂ : 0 ≤ v_raw i := (hv_raw_pos i).le
    simp only [v0, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg h₁ h₂
  have h_sum_v0 : ∑ i, v0 i = 1 := by
    calc
        ∑ i, v0 i
            = ∑ i, s⁻¹ * v_raw i := by simp [v0, smul_eq_mul]
        _ = s⁻¹ * ∑ i, v_raw i   := by
              rw [Finset.mul_sum]
        _ = s⁻¹ * s               := by simp [s]
        _ = 1                     := by field_simp [hs_ne]

  have hv0_simplex : v0 ∈ stdSimplex ℝ n := ⟨hv0_nonneg, h_sum_v0⟩
  have hv0_pos : ∀ i, 0 < v0 i := by
    intro i
    have h₁ : 0 < s⁻¹ := inv_pos.mpr hs_pos
    have h₂ : 0 < v_raw i := hv_raw_pos i
    simp only [v0, Pi.smul_apply, smul_eq_mul]
    exact mul_pos h₁ h₂
  have hv0_eig : A *ᵥ v0 = r • v0 := by
    calc
      A *ᵥ v0 = A *ᵥ (s⁻¹ • v_raw) := rfl
      _       = s⁻¹ • (A *ᵥ v_raw) := by rw [mulVec_smul]
      _       = s⁻¹ • (r • v_raw)  := by rw [hv_raw_eig]
      _       = r • (s⁻¹ • v_raw)  := by rw [smul_comm]
      _       = r • v0             := rfl
  refine ⟨⟨v0, hv0_simplex⟩, ?_, ?_⟩
  · exact ⟨r, hr_pos, hv0_eig⟩
  · intro w ⟨r', hr'_pos, hw_eig⟩
    have hw_nonneg : ∀ i, 0 ≤ w.1 i := w.property.1
    have hw_ne_zero := ne_zero_of_mem_stdSimplex w.property
    have hw_pos : ∀ i, 0 < w.1 i :=
      eigenvector_of_primitive_is_positive hA_prim hr'_pos
        hw_eig hw_nonneg hw_ne_zero
    let c : ℝ := Finset.univ.inf' Finset.univ_nonempty
                   (fun i : n => v0 i / w.1 i)
    have hc_pos : 0 < c := by
      apply Finset.inf'_pos Finset.univ_nonempty
      intro i _
      exact div_pos (hv0_pos i) (hw_pos i)
    obtain ⟨i₀, _, hc_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n => v0 i / w.1 i)
    have w_i₀_pos : 0 < w.1 i₀ := hw_pos i₀
    have v0_ge_cw : ∀ j, c * w.1 j ≤ v0 j := by
      intro j
      have h_le : c ≤ v0 j / w.1 j :=
        Finset.inf'_le _ (Finset.mem_univ j)
      exact (le_div_iff₀ (hw_pos j)).mp h_le

    have h_sum :
        c * (A *ᵥ w.1) i₀ ≤ (A *ᵥ v0) i₀ := by
      dsimp [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h_le : c * w.1 j ≤ v0 j := v0_ge_cw j
      have hA : 0 ≤ A i₀ j := hA_nonneg i₀ j
      have h := mul_le_mul_of_nonneg_left h_le hA
      rwa [mul_left_comm]
    have hv0_i₀ : (A *ᵥ v0) i₀ = r * v0 i₀ := by
      rw [hv0_eig]
      simp only [Pi.smul_apply, smul_eq_mul]
    have hw_i₀  : (A *ᵥ w.1) i₀ = r' * w.1 i₀ := by
      rw [hw_eig]
      simp only [Pi.smul_apply, smul_eq_mul]
    have v0_i₀_eq : v0 i₀ = c * w.1 i₀ := by
      have : c = v0 i₀ / w.1 i₀ := hc_eq
      have w_ne : w.1 i₀ ≠ 0 := ne_of_gt w_i₀_pos
      field_simp [this, w_ne]
    have h_r_ge_r' : r ≥ r' := by
      have h_pos : 0 < c * w.1 i₀ := mul_pos hc_pos w_i₀_pos
      have h1 : c * r' * w.1 i₀ ≤ r * v0 i₀ := by
        calc
          c * r' * w.1 i₀ = c * (r' * w.1 i₀)   := by ring
          _ = c * (A *ᵥ w.1) i₀                 := by rw [hw_i₀]
          _ ≤ (A *ᵥ v0) i₀                      := h_sum
          _ = r * v0 i₀                         := hv0_i₀
      have h2 : c * r' * w.1 i₀ ≤ r * (c * w.1 i₀) := by
        rwa [v0_i₀_eq] at h1
      have h2' : r' * (c * w.1 i₀) ≤ r * (c * w.1 i₀) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      exact le_of_mul_le_mul_right h2' h_pos
    let d : ℝ := Finset.univ.inf' Finset.univ_nonempty
                   (fun i : n => w.1 i / v0 i)
    have hd_pos : 0 < d := by
      apply Finset.inf'_pos Finset.univ_nonempty
      intro i _
      exact div_pos (hw_pos i) (hv0_pos i)
    obtain ⟨j₀, _, hd_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : n => w.1 i / v0 i)
    have v0_j₀_pos : 0 < v0 j₀ := hv0_pos j₀

    have w_ge_dv0 : ∀ j, d * v0 j ≤ w.1 j := by
      intro j
      have h_le : d ≤ w.1 j / v0 j :=
        Finset.inf'_le _ (Finset.mem_univ j)
      exact (le_div_iff₀ (hv0_pos j)).mp h_le
    have h_sum2 :
        d * (A *ᵥ v0) j₀ ≤ (A *ᵥ w.1) j₀ := by
      dsimp only [mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h_le : d * v0 j ≤ w.1 j := w_ge_dv0 j
      have hA : 0 ≤ A j₀ j := hA_nonneg j₀ j
      have h := mul_le_mul_of_nonneg_left h_le hA
      rwa [mul_left_comm]
    have w_j₀_eq : w.1 j₀ = d * v0 j₀ := by
      have : d = w.1 j₀ / v0 j₀ := hd_eq
      have v0_ne : v0 j₀ ≠ 0 := ne_of_gt v0_j₀_pos
      field_simp [this, v0_ne]
    have h_r'_ge_r : r' ≥ r := by
      have h_pos : 0 < d * v0 j₀ := mul_pos hd_pos v0_j₀_pos
      have h1 : d * r * v0 j₀ ≤ r' * w.1 j₀ := by
        calc
          d * r * v0 j₀ = d * (r * v0 j₀) := by ring
          _ = d * (A *ᵥ v0) j₀ := by simp only [hv0_eig, Pi.smul_apply,
            smul_eq_mul]
          _ ≤ (A *ᵥ w.1) j₀ := h_sum2
          _ = r' * w.1 j₀ := by simp only [hw_eig, Pi.smul_apply,
            smul_eq_mul]
      have h2 : d * r * v0 j₀ ≤ r' * (d * v0 j₀) := by
        rwa [w_j₀_eq] at h1
      have h2' : r * (d * v0 j₀) ≤ r' * (d * v0 j₀) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      exact (le_of_mul_le_mul_right h2' h_pos)
    have hr_eq : r = r' := le_antisymm h_r'_ge_r h_r_ge_r'
    have hw_eig' : A *ᵥ w.1 = r • w.1 := by
      simp only [hw_eig, hr_eq]
    rcases
      uniqueness_of_positive_eigenvector
          hA_prim hr_pos v0 w.1 hv0_eig hw_eig' hv0_pos hw_pos
      with ⟨c', hc'_pos, hc'_eq⟩
    have hc'_one : c' = 1 := by
      have h_sum_w : ∑ i, w.1 i = 1 := w.property.2
      calc
        c' = c' * 1                 := by ring
        _  = c' * (∑ i, w.1 i)      := by rw [h_sum_w]
        _  = (∑ i, c' * w.1 i)      := by rw [Finset.mul_sum]
        _  = (∑ i, v0 i)            := by
               simp only [hc'_eq, Pi.smul_apply, smul_eq_mul]
        _  = 1                      := h_sum_v0
    ext i
    simp [hc'_eq, hc'_one]
open Quiver

lemma Irreducible.exists_pos_entry
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {A : Matrix n n ℝ}
    (hA_irred : Irreducible A) :
    ∃ i j : n, 0 < A i j := by
  classical
  letI : Quiver n := toQuiver A
  let i₀ : n := Classical.arbitrary n
  obtain ⟨⟨p, hp_pos⟩⟩ := hA_irred.2 i₀ i₀
  have h_len : p.length > 0 := hp_pos
  rcases Quiver.Path.path_decomposition_first_edge p h_len with
    ⟨j, e, -, -, -⟩
  exact ⟨i₀, j, e⟩

/--
**Perron–Frobenius theorem for irreducible real matrices (Existence, positivity, uniqueness)**.

Let A : Matrix n n ℝ be an irreducible nonnegative matrix indexed by a finite nonempty type n.
Then there exists a unique eigenpair (v, r) where
  • v : stdSimplex ℝ n is a probability vector (i.e. v.val has nonnegative entries summing to 1),
  • r : ℝ is a positive scalar,
such that
  A *ᵥ v.val = r • v.val   and   r > 0.
Moreover, this eigenvector v in the standard simplex is unique, and the corresponding eigenvalue r
is the Perron root of A.
-/
theorem pft_irreducible {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA_irred : Irreducible A) :
    ∃! (v : stdSimplex ℝ n), ∃ (r : ℝ), r > 0 ∧ A *ᵥ v.val = r • v.val := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    intro i j; by_cases h : i = j
    · subst h
      have : (0 : ℝ) ≤ 1 + A i i := by
        have := hA_irred.1 i i; linarith
      simpa [B] using this
    · simpa [B, h] using hA_irred.1 i j
  have hB_diag_pos : ∀ i, 0 < B i i := by
    intro i
    have : (0 : ℝ) < 1 + A i i := by
      have := hA_irred.1 i i; linarith
    simpa [B] using this
  have hB_irred : Irreducible B := by
    simpa [B] using hA_irred.add_one
  have hB_prim : IsPrimitive B :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  obtain ⟨v, hv_unique⟩ := pft_primitive hB_prim hB_nonneg
  obtain ⟨rB, hrB_pos, h_eig_B⟩ := hv_unique.1
  let r : ℝ := rB - 1
  have h_eig_A : A *ᵥ v.val = r • v.val := by
    have h_B_eig_expanded : (1 + A) *ᵥ v.val = rB • v.val := by simpa [B] using h_eig_B
    have h_A_eig_expanded : v.val + A *ᵥ v.val = rB • v.val := by simpa [add_mulVec, one_mulVec] using h_B_eig_expanded
    have : A *ᵥ v.val = rB • v.val - v.val := eq_sub_of_add_eq' h_A_eig_expanded
    simpa [r, sub_smul, one_smul] using this
  let v_pos :=
    eigenvector_of_primitive_is_positive
      hB_prim hrB_pos h_eig_B v.2.1 (ne_zero_of_mem_stdSimplex v.2)
  rcases (Irreducible.exists_pos_entry (A := A) hA_irred) with
    ⟨i₀, j₀, hA_pos⟩
  have hr_pos : 0 < r := by
    have hAv_pos : 0 < (A *ᵥ v.val) i₀ := by
      have h_nonneg : ∀ k ∈ Finset.univ, 0 ≤ A i₀ k * v.val k :=
        fun k _ ↦ mul_nonneg (hA_irred.1 _ _) (le_of_lt (v_pos k))
      have h_term : 0 < A i₀ j₀ * v.val j₀ :=
        mul_pos hA_pos (v_pos _)
      have : 0 < ∑ k, A i₀ k * v.val k :=
        sum_pos_of_mem h_nonneg j₀ (Finset.mem_univ _) h_term
      simpa [mulVec_apply] using this
    have : 0 < r * v.val i₀ := by
      simpa [Pi.smul_apply, smul_eq_mul, h_eig_A] using hAv_pos
    exact (mul_pos_iff_of_pos_right (v_pos _)).1 this
  refine ⟨v, ⟨r, hr_pos, h_eig_A⟩, ?_⟩
  · intro v' ⟨r', hr'_pos, h_eig_A'⟩
    have v'_pos :=
      eigenvector_is_positive_of_irreducible
        hA_irred h_eig_A' v'.2.1 (ne_zero_of_mem_stdSimplex v'.2)
    have v_pos' :=
      eigenvector_is_positive_of_irreducible
        hA_irred h_eig_A v.2.1 (ne_zero_of_mem_stdSimplex v.2)
    have hr_eq : r = r' := by
      have h_eig_B' : B *ᵥ v'.val = (r' + 1) • v'.val := by
        simp [B, add_mulVec, one_mulVec, add_smul, one_smul, h_eig_A', add_comm]
      have h_unique_vec_B := hv_unique.2
      have h_v_eq_v' : v' = v := h_unique_vec_B v' ⟨r' + 1, by linarith, h_eig_B'⟩
      have h_smul_eq : rB • v.val = (r' + 1) • v.val := by
        rw [← h_eig_B, ← h_v_eq_v', h_eig_B']
      have h_rB_eq : rB = r' + 1 := by
        have h_v_ne_zero : v.val ≠ 0 := ne_zero_of_mem_stdSimplex v.property
        obtain ⟨i, hi_ne_zero⟩ := Function.exists_ne_zero_of_ne_zero h_v_ne_zero
        have : (rB • v.val) i = ((r' + 1) • v.val) i := by rw [h_smul_eq]
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at this
        exact (mul_left_inj' hi_ne_zero).mp this
      calc
        r = rB - 1 := by rfl
        _ = (r' + 1) - 1 := by rw [h_rB_eq]
        _ = r' := by ring
    have h_eig_A'_r : A *ᵥ v'.val = r • v'.val := by
      subst hr_eq
      simp_all only [add_apply, one_apply_eq, gt_iff_lt, exists_prop, forall_exists_index, and_imp, Subtype.forall,
        sub_pos, implies_true, B, r]
    obtain ⟨c, hc_pos, hcv⟩ :=
      uniqueness_of_positive_eigenvector_gen
        hA_irred hr_pos v_pos' v'_pos h_eig_A h_eig_A'_r
    have hc_one : c = 1 := by
      have h_sum_v' : (∑ i, v'.val i) = 1 := v'.property.2
      calc c
        _ = c * 1 := (mul_one c).symm
        _ = c * (∑ i, v'.val i) := by rw [h_sum_v']
        _ = ∑ i, c * v'.val i := by rw [Finset.mul_sum]
        _ = ∑ i, v.val i := by simp [hcv, smul_eq_mul]
        _ = 1 := v.property.2
    exact Subtype.val_injective (by simp [hcv, hc_one, one_smul])
