import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.CompletelyRegular

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.refine false

/-! # Perron-Frobenius Theory for Matrices -/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
## The Standard Simplex
-/

lemma stdSimplex_nonempty [Nonempty n] : (stdSimplex ℝ n).Nonempty :=
  ⟨(Fintype.card n : ℝ)⁻¹ • 1, by simp [stdSimplex, Finset.sum_const, nsmul_eq_mul]⟩

lemma isCompact_stdSimplex : IsCompact (stdSimplex ℝ n) :=
  _root_.isCompact_stdSimplex n

lemma convex_stdSimplex : Convex ℝ (stdSimplex ℝ n) :=
  _root_.convex_stdSimplex ℝ n

/-!
## Spectral Properties of Matrices
-/

/-- The spectrum of a matrix `A` is equal to the spectrum of its corresponding linear map
`Matrix.toLin' A`. -/
lemma spectrum_eq_spectrum_toLin' (A : Matrix n n ℝ) :
    spectrum ℝ A = spectrum ℝ (Matrix.toLin' A) := by
  exact Eq.symm (AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (Pi.basisFun ℝ n)) A)

/-- The determinant of `μ • 1 - A` is the evaluation of the characteristic polynomial of `A` at `μ`. -/
lemma det_smul_sub_eq_eval_charpoly (A : Matrix n n ℝ) (μ : ℝ) :
    det (μ • 1 - A) = (Matrix.charpoly A).eval μ := by
  have h : μ • 1 = Matrix.scalar n μ := by
    ext i j
    simp [Matrix.scalar, Matrix.one_apply, smul_apply]
    rfl
  rw [h]
  rw [← eval_charpoly A μ]

/-- A real number `μ` is in the spectrum of a matrix `A` if and only if it is a root
of the characteristic polynomial of `A`. -/
lemma mem_spectrum_iff_isRoot_charpoly (A : Matrix n n ℝ) (μ : ℝ) :
    μ ∈ spectrum ℝ A ↔ (charpoly A).IsRoot μ := by
  rw [spectrum.mem_iff]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff]
  have h_alg : (algebraMap ℝ (Matrix n n ℝ)) μ = μ • 1 := by
    ext i j
    simp [algebraMap, Matrix.one_apply]
    rfl
  rw [h_alg]
  rw [det_smul_sub_eq_eval_charpoly]
  rw [Polynomial.IsRoot.def]

/-- A matrix and its transpose have the same spectrum. -/
lemma spectrum_eq_spectrum_transpose (A : Matrix n n ℝ) :
    spectrum ℝ A = spectrum ℝ Aᵀ := by
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, mem_spectrum_iff_isRoot_charpoly, charpoly_transpose]

/-!
## Determinant, Kernel, and Invertibility
-/
open Module

/-- The determinant of a matrix equals the determinant of its associated linear map. -/
lemma det_toLin' (A : Matrix n n ℝ) : det A = LinearMap.det (toLin' A) := by
  rw [← LinearMap.det_toMatrix' (toLin' A)]
  simp [LinearMap.toMatrix'_toLin']

/-!
# Perron-Frobenius Theory for Matrices

This file provides core lemmas and theorems related to the Perron-Frobenius theory for non-negative,
irreducible matrices.
-/

open LinearMap

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- If a linear map is not injective, then its kernel is non-trivial. -/
lemma ker_ne_bot_of_not_injective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {f : V →ₗ[K] V} (h : ¬Function.Injective f) : LinearMap.ker f ≠ ⊥ := by
  contrapose! h
  rw [← LinearMap.ker_eq_bot]
  exact h

lemma LinearMap.isUnit_iff_bijective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) : IsUnit f ↔ Function.Bijective f := by
  constructor
  · intro h_unit
    exact (End.isUnit_iff f).mp h_unit
  · intro h_bij
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    rw [LinearMap.ker_eq_bot]
    exact h_bij.1

lemma LinearMap.injective_of_isUnit {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : V →ₗ[K] V} (h : IsUnit f) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  rw [← LinearMap.isUnit_iff_ker_eq_bot]
  exact h

/-- If the kernel of a linear endomorphism on a finite-dimensional vector space is non-trivial,
    then its determinant is zero. -/
lemma det_eq_zero_of_ker_ne_bot {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ↑(Basis.ofVectorSpaceIndex K V)]
    [FiniteDimensional K V] {f : V →ₗ[K] V} (h : LinearMap.ker f ≠ ⊥) :
    LinearMap.det f = 0 := by
  by_contra h_det_ne_zero
  have h_det_unit : IsUnit (LinearMap.det f) := IsUnit.mk0 _ h_det_ne_zero
  have h_f_is_unit : IsUnit f := by
    let b := Basis.ofVectorSpace K V
    have h_det_matrix_unit : IsUnit (Matrix.det (LinearMap.toMatrix b b f)) := by
      rw [LinearMap.det_toMatrix b f]
      exact h_det_unit
    have h_toMatrix_unit : IsUnit (LinearMap.toMatrix b b f) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr h_det_matrix_unit
    rw [← isUnit_map_iff ((Matrix.toLinAlgEquiv b).symm) f]
    exact h_toMatrix_unit
  have h_ker_eq_bot : LinearMap.ker f = ⊥ := by
    rw [← LinearMap.isUnit_iff_ker_eq_bot]
    exact h_f_is_unit
  exact h h_ker_eq_bot

/-- If a non-zero vector `v` is in the kernel of a linear map `f`, then `det f` must be zero. -/
lemma det_eq_zero_of_exists_mem_ker {K V} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ↑(Basis.ofVectorSpaceIndex K V)]
    [FiniteDimensional K V] {f : V →ₗ[K] V} (h : ∃ v, v ≠ 0 ∧ f v = 0) :
    LinearMap.det f = 0 := by
  apply det_eq_zero_of_ker_ne_bot
  obtain ⟨v, hv_ne_zero, hv_ker⟩ := h
  rw [Submodule.ne_bot_iff]
  use v
  exact ⟨LinearMap.mem_ker.mpr hv_ker, hv_ne_zero⟩

/-- If a linear endomorphism on a finite-dimensional vector space is not injective,
    then its determinant is zero. -/
lemma det_eq_zero_of_not_injective {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ↑(Basis.ofVectorSpaceIndex K V)]
    [FiniteDimensional K V] {f : V →ₗ[K] V} (h : ¬Function.Injective f) :
    LinearMap.det f = 0 := by
  apply det_eq_zero_of_ker_ne_bot
  exact ker_ne_bot_of_not_injective h

/-- If the determinant is zero, the linear map is not injective. -/
lemma not_injective_of_det_eq_zero {f : (n → ℝ) →ₗ[ℝ] (n → ℝ)} (h : LinearMap.det f = 0) :
    ¬Function.Injective f := by
  by_contra h_inj
  have h_unit : IsUnit f := by
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    rwa [LinearMap.ker_eq_bot]
  have h_det_unit : IsUnit (LinearMap.det f) := by
    exact LinearMap.isUnit_det f h_unit
  have h_det_ne_zero : LinearMap.det f ≠ 0 := by
    exact IsUnit.ne_zero h_det_unit
  exact h_det_ne_zero h

/-- For a matrix `A`, the associated linear map `toLin' A` has a non-trivial kernel
if and only if the determinant of `A` is zero. -/
lemma ker_toLin'_ne_bot_iff_det_eq_zero (A : Matrix n n ℝ) :
    LinearMap.ker (toLin' A) ≠ ⊥ ↔ det A = 0 := by
  constructor
  · intro h_ker_ne_bot
    rw [det_toLin']
    have h_not_inj : ¬Function.Injective (toLin' A) := by
      rwa [← LinearMap.ker_eq_bot]
    exact det_eq_zero_of_not_injective h_not_inj
  · intro h_det_zero
    by_contra h_ker_eq_bot
    rw [LinearMap.ker_eq_bot] at h_ker_eq_bot
    rw [det_toLin'] at h_det_zero
    have h_det_ne_zero : LinearMap.det (toLin' A) ≠ 0 := by
      by_contra h_zero
      exact not_injective_of_det_eq_zero h_zero h_ker_eq_bot
    exact h_det_ne_zero h_det_zero

/-- A real number `μ` is an eigenvalue of a matrix `A` if and only if `det(μ • 1 - A) = 0`. -/
lemma hasEigenvalue_toLin'_iff_det_sub_eq_zero (A : Matrix n n ℝ) (μ : ℝ) :
    Module.End.HasEigenvalue (toLin' A) μ ↔ det (μ • 1 - A) = 0 := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, ← spectrum_eq_spectrum_toLin',
    mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, det_smul_sub_eq_eval_charpoly]

/-! ## Spectral Radius Theory for Matrices -/

lemma not_isUnit_iff_eq_zero {R : Type*} [Field R] [Nontrivial R] (a : R) :
    ¬IsUnit a ↔ a = 0 ∨ a ∈ nonunits R := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr h
  · intro h
    cases h with
    | inl h0 => rw [h0]; exact not_isUnit_zero
    | inr hnon => exact hnon

lemma LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top {R : Type*} [Field R] {M : Type*}
    [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) :
    Function.Bijective f ↔ LinearMap.ker f = ⊥ ∧ LinearMap.range f = ⊤ := by
  constructor
  · intro h
    constructor
    · exact LinearMap.ker_eq_bot_of_injective h.1
    · exact LinearMap.range_eq_top_of_surjective _ h.2
  · intro ⟨h_ker, h_range⟩
    constructor
    · exact LinearMap.ker_eq_bot.mp h_ker
    · exact LinearMap.range_eq_top.mp h_range

lemma ker_ne_bot_of_det_eq_zero (A : Matrix n n ℝ) :
    LinearMap.det (Matrix.toLin' A) = 0 → LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
  contrapose!
  intro h_ker_bot
  have h_inj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot]
    exact h_ker_bot
  have h_isUnit : IsUnit (LinearMap.det (Matrix.toLin' A)) :=
    LinearMap.isUnit_det (Matrix.toLin' A) ((LinearMap.isUnit_iff_ker_eq_bot
      (toLin' A)).mpr h_ker_bot)
  exact IsUnit.ne_zero h_isUnit

-- Basic kernel-injectivity relationship
lemma ker_eq_bot_iff_injective_toLin' (A : Matrix n n ℝ) :
    LinearMap.ker (Matrix.toLin' A) = ⊥ ↔ Function.Injective (Matrix.toLin' A) := by
  exact LinearMap.ker_eq_bot

-- For finite dimensions, injective endomorphisms are bijective
lemma injective_iff_bijective_toLin' (A : Matrix n n ℝ) :
    Function.Injective (Matrix.toLin' A) ↔ Function.Bijective (Matrix.toLin' A) := by
  constructor
  · intro h_inj
    exact IsArtinian.bijective_of_injective_endomorphism (toLin' A) h_inj
  · exact fun h_bij => h_bij.1

-- Bijective linear maps are units
lemma bijective_iff_isUnit_toLin' (A : Matrix n n ℝ) :
    Function.Bijective (Matrix.toLin' A) ↔ IsUnit (Matrix.toLin' A) := by
  haveI : FiniteDimensional ℝ (n → ℝ) := by infer_instance
  rw [LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top]
  have h_equiv : LinearMap.range (Matrix.toLin' A) = ⊤ ↔ LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    Iff.symm LinearMap.ker_eq_bot_iff_range_eq_top
  rw [h_equiv, and_self]
  rw [LinearMap.isUnit_iff_ker_eq_bot]

lemma isUnit_of_det_ne_zero (A : Matrix n n ℝ) (h_det_ne_zero : LinearMap.det (Matrix.toLin' A) ≠ 0) :
    IsUnit (Matrix.toLin' A) := by
  rw [← bijective_iff_isUnit_toLin', ← injective_iff_bijective_toLin', ← ker_eq_bot_iff_injective_toLin']
  by_contra h_ker_ne_bot
  have h_det_zero : LinearMap.det (Matrix.toLin' A) = 0 := by
    exact det_eq_zero_of_ker_ne_bot h_ker_ne_bot
  exact h_det_ne_zero h_det_zero


-- An algebra equivalence preserves the property of being a unit.
lemma AlgEquiv.isUnit_map_iff {R A B : Type*} [CommSemiring R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (x : A) :
    IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h_ex_unit
    simp_all only [MulEquiv.isUnit_map]
  · intro h_x_unit
    simp_all only [MulEquiv.isUnit_map]

lemma isUnit_of_det_ne_zero' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (h_det_ne_zero : LinearMap.det (Matrix.toLin' A) ≠ 0) :
    IsUnit (Matrix.toLin' A) := by
  let f := Matrix.toLin' A
  have h_det_f_is_unit : IsUnit (LinearMap.det f) := IsUnit.mk0 (LinearMap.det f) h_det_ne_zero
  let b := Pi.basisFun ℝ n
  have h_det_matrix_form_is_unit : IsUnit (Matrix.det (LinearMap.toMatrix b b f)) :=
    (LinearMap.det_toMatrix b f).symm ▸ h_det_f_is_unit
  have h_matrix_representation_is_unit : IsUnit (LinearMap.toMatrix b b f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr h_det_matrix_form_is_unit
  simp only at h_matrix_representation_is_unit
  have h_toMatrix_eq_A : LinearMap.toMatrix b b f = A := by
    exact (LinearEquiv.eq_symm_apply (toMatrix b b)).mp rfl
  rw [h_toMatrix_eq_A] at h_matrix_representation_is_unit
  rw [← bijective_iff_isUnit_toLin']
  have h_isUnit_toLin : IsUnit (Matrix.toLin' A) := by
          let e : Matrix n n ℝ ≃ₐ[ℝ] Module.End ℝ (n → ℝ) := Matrix.toLinAlgEquiv (Pi.basisFun ℝ n)
          change IsUnit (e A)
          rw [AlgEquiv.isUnit_map_iff e A]
          exact h_matrix_representation_is_unit
  exact (bijective_iff_isUnit_toLin' A).mpr h_isUnit_toLin

lemma det_eq_zero_of_ker_ne_bot' (A : Matrix n n ℝ) :
    LinearMap.ker (Matrix.toLin' A) ≠ ⊥ → LinearMap.det (Matrix.toLin' A) = 0 := by
  contrapose!
  intro h_det_ne_zero
  have h_isUnit_det : IsUnit (LinearMap.det (Matrix.toLin' A)) :=
    isUnit_iff_ne_zero.mpr h_det_ne_zero
  have h_isUnit_map : IsUnit (Matrix.toLin' A) := isUnit_of_det_ne_zero A h_det_ne_zero
  have h_bijective : Function.Bijective (Matrix.toLin' A) := by
    rw [LinearMap.bijective_iff_ker_eq_bot_and_range_eq_top]
    constructor
    · exact (LinearMap.isUnit_iff_ker_eq_bot (Matrix.toLin' A)).mp h_isUnit_map
    · exact (LinearMap.isUnit_iff_range_eq_top (toLin' A)).mp h_isUnit_map
  exact LinearMap.ker_eq_bot_of_injective h_bijective.1

lemma det_eq_zero_iff_exists_nontrivial_ker (A : Matrix n n ℝ) :
    Matrix.det A = 0 ↔ ∃ v : n → ℝ, v ≠ 0 ∧ Matrix.mulVec A v = 0 := by
  rw [← LinearMap.det_toLin']
  constructor
  · intro h_det_zero
    have h_ker_ne_bot : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ :=
      ker_ne_bot_of_det_eq_zero A h_det_zero
    obtain ⟨v, hv_mem, hv_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ker_ne_bot
    use v
    constructor
    · exact hv_ne_zero
    · rw [← Matrix.toLin'_apply]
      exact hv_mem
  · intro ⟨v, hv_ne_zero, hv_ker⟩
    have h_ker_ne_bot : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
      intro h_ker_bot
      have hv_in_ker : v ∈ LinearMap.ker (Matrix.toLin' A) := by
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        exact hv_ker
      rw [h_ker_bot] at hv_in_ker
      simp at hv_in_ker
      exact hv_ne_zero hv_in_ker
    exact det_eq_zero_of_ker_ne_bot' A h_ker_ne_bot

lemma spectralRadius_le_nnnorm_of_mem_spectrum {A : Matrix n n ℝ} {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : ‖μ‖₊ ≤ ‖(Matrix.toLin' A).toContinuousLinearMap‖₊ := by
  have h_eigenvalue : ∃ v : n → ℝ, v ≠ 0 ∧ Matrix.mulVec A v = μ • v := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hμ
    push_neg at hμ
    have : Matrix.det (algebraMap ℝ (Matrix n n ℝ) μ - A) = 0 := hμ
    rw [Algebra.algebraMap_eq_smul_one, Matrix.det_eq_zero_iff_exists_nontrivial_ker] at this
    obtain ⟨v, hv_ne_zero, hv_ker⟩ := this
    use v
    constructor
    · exact hv_ne_zero
    · rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec, sub_eq_zero] at hv_ker
      exact hv_ker.symm
  obtain ⟨v, hv_ne_zero, hv_eigen⟩ := h_eigenvalue
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne_zero
  have : ‖μ • v‖ = ‖μ‖ * ‖v‖ := norm_smul μ v
  rw [← hv_eigen, ← Matrix.toLin'_apply] at this
  have h_bound : ‖(Matrix.toLin' A).toContinuousLinearMap v‖ ≤ ‖(Matrix.toLin' A).toContinuousLinearMap‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ v
  rw [LinearMap.coe_toContinuousLinearMap', this] at h_bound
  exact le_of_mul_le_mul_right h_bound hv_norm_pos

lemma spectralRadius_lt_top {A : Matrix n n ℝ} :
    spectralRadius ℝ A < ⊤ := by
  rw [spectralRadius]
  apply iSup_lt_iff.mpr
  use ‖(Matrix.toLin' A).toContinuousLinearMap‖₊ + 1
  constructor
  · exact ENNReal.coe_lt_top
  · intro i
    apply iSup_le
    intro hi
    exact ENNReal.coe_le_coe.mpr (le_trans (spectralRadius_le_nnnorm_of_mem_spectrum hi) (le_add_of_nonneg_right zero_le_one))

lemma spectrum.nnnorm_le_nnnorm_of_mem {𝕜 A : Type*}
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]
    (a : A) {k : 𝕜} (hk : k ∈ spectrum 𝕜 a) : ‖k‖₊ ≤ ‖a‖₊ := by
  have h_subset : spectrum 𝕜 a ⊆ Metric.closedBall 0 ‖a‖ :=
    spectrum.subset_closedBall_norm a
  have hk_in_ball : k ∈ Metric.closedBall 0 ‖a‖ := h_subset hk
  have h_norm_le : ‖k‖ ≤ ‖a‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hk_in_ball
    exact hk_in_ball
  exact h_norm_le

lemma toLin'_eq_toEuclideanLin (A : Matrix n n ℝ) :
    Matrix.toLin' A = (Matrix.toEuclideanLin A : (n → ℝ) →ₗ[ℝ] (n → ℝ)) := by
  rfl

lemma toLin'_toContinuousLinearMap_eq (A : Matrix n n ℝ) :
    (Matrix.toLin' A).toContinuousLinearMap =
    (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  rw [toLin'_eq_toEuclideanLin]
  rfl

lemma toLin'_apply_eq_toEuclideanLin_apply (A : Matrix n n ℝ) (v : n → ℝ) :
    Matrix.toLin' A v = Matrix.toEuclideanLin A v := by
  simp [Matrix.toLin'_apply, Matrix.toEuclideanLin_apply]
  rfl

lemma toLin'_toContinuousLinearMap (A : Matrix n n ℝ) :
    (Matrix.toLin' A).toContinuousLinearMap = (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  ext v
  rfl

lemma vecMul_eq_mulVec_transpose {n : Type*} [Fintype n] (A : Matrix n n ℝ) (v : n → ℝ) :
    v ᵥ* A = Aᵀ *ᵥ v := by
  ext j
  simp [vecMul, mulVec, transpose]
  rw [@dotProduct_comm]

lemma dotProduct_le_dotProduct_of_nonneg_left' {n : Type*} [Fintype n] {u x y : n → ℝ}
    (hu_nonneg : ∀ i, 0 ≤ u i) (h_le : x ≤ y) :
    u ⬝ᵥ x ≤ u ⬝ᵥ y := by
  rw [dotProduct, dotProduct, ← sub_nonneg, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [← mul_sub]
  exact mul_nonneg (hu_nonneg i) (sub_nonneg.mpr (h_le i))

lemma eq_zero_of_nonneg_of_dotProduct_eq_zero {n : Type*} [Fintype n] {u z : n → ℝ}
    (hu_pos : ∀ i, 0 < u i) (hz_nonneg : ∀ i, 0 ≤ z i) (h_dot : u ⬝ᵥ z = 0) :
    z = 0 := by
  have h_terms_nonneg : ∀ i, 0 ≤ u i * z i := fun i => mul_nonneg (hu_pos i).le (hz_nonneg i)
  have h_terms_zero : ∀ i, u i * z i = 0 := by
    rw [dotProduct, Finset.sum_eq_zero_iff_of_nonneg] at h_dot
    · exact fun i => h_dot i (Finset.mem_univ _)
    · exact fun i _ => h_terms_nonneg i
  funext i
  exact (mul_eq_zero.mp (h_terms_zero i)).resolve_left (hu_pos i).ne'

lemma Module.End.exists_eigenvector_of_mem_spectrum {K V : Type*}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : V →ₗ[K] V} {μ : K} (h_is_eigenvalue : μ ∈ spectrum K f) :
  ∃ v, v ≠ 0 ∧ f v = μ • v := by
  rw [spectrum.mem_iff, LinearMap.isUnit_iff_ker_eq_bot] at h_is_eigenvalue
  obtain ⟨v, hv_mem, hv_ne_zero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_is_eigenvalue
  use v, hv_ne_zero
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv_mem
  exact (sub_eq_zero.mp hv_mem).symm

-- Core lemma: spectral radius is bounded by the operator norm
lemma spectralRadius_le_nnnorm {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
     [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]
    (a : A) :
    spectralRadius 𝕜 a ≤ ↑‖a‖₊ := by
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  have h_nnnorm_le : ‖μ‖₊ ≤ ‖a‖₊ := spectrum.nnnorm_le_nnnorm_of_mem a hμ
  exact ENNReal.coe_le_coe.mpr h_nnnorm_le

-- Specialized version for continuous linear maps
lemma spectralRadius_le_nnnorm_continuousLinearMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E] (T : E →L[ℝ] E) :
    spectralRadius ℝ T ≤ ↑‖T‖₊ := by
  exact spectralRadius_le_nnnorm (𝕜 := ℝ) (A := E →L[ℝ] E) T

/-- The spectral radii of a matrix and its transpose are equal. -/
lemma spectralRadius_eq_spectralRadius_transpose [DecidableEq n] (A : Matrix n n ℝ) :
    spectralRadius ℝ A = spectralRadius ℝ Aᵀ := by
  unfold spectralRadius
  rw [spectrum_eq_spectrum_transpose]

lemma spectralRadius_le_opNorm (A : Matrix n n ℝ) :
    spectralRadius ℝ (Matrix.toLin' A) ≤ ↑‖(Matrix.toLin' A).toContinuousLinearMap‖₊ := by
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  have hμ_matrix : μ ∈ spectrum ℝ A := by
    rw [spectrum_eq_spectrum_toLin']
    exact hμ
  exact ENNReal.coe_le_coe.mpr (spectralRadius_le_nnnorm_of_mem_spectrum hμ_matrix)

lemma spectralRadius_finite (A : Matrix n n ℝ) :
    spectralRadius ℝ (Matrix.toLin' A) ≠ ⊤ := by
  have h_le_norm : spectralRadius ℝ (Matrix.toLin' A) ≤ ↑‖(Matrix.toLin' A).toContinuousLinearMap‖₊ :=
    spectralRadius_le_opNorm A
  have h_norm_finite : (↑‖(Matrix.toLin' A).toContinuousLinearMap‖₊ : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  exact ne_top_of_le_ne_top h_norm_finite h_le_norm

lemma norm_mulVec_le_of_row_stochastic
    {A : Matrix n n ℝ} (h_stochastic : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, (0 : ℝ) ≤ A i j) :
    ∀ v : n → ℝ, ‖A *ᵥ v‖ ≤ ‖v‖ := by
  intro v
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec]
  calc |∑ j, A i j * v j|
    _ ≤ ∑ j, |A i j * v j| :=
      Finset.abs_sum_le_sum_abs (fun i_1 ↦ A i i_1 * v i_1) Finset.univ
    _ = ∑ j, (A i j) * |v j| := by simp_rw [abs_mul, abs_of_nonneg (h_nonneg i _)]
    _ ≤ ∑ j, A i j * ‖v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (h_nonneg i j)
    _ = (∑ j, A i j) * ‖v‖ := (Finset.sum_mul ..).symm
    _ = ‖v‖ := by rw [h_stochastic i, one_mul]

/--
The spectral radius of a row-stochastic matrix with non-negative entries is at most 1.
-/
theorem spectralRadius_stochastic_le_one {A : Matrix n n ℝ}
  (h_stochastic : ∀ i, ∑ j, A i j = 1)
  (h_nonneg : ∀ i j, 0 ≤ A i j) :
  spectralRadius ℝ (Matrix.toLin' A) ≤ 1 := by
  let L := (Matrix.toLin' A).toContinuousLinearMap
  have h_norm_le_one : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one)
    intro v
    dsimp
    rw [one_mul]
    exact norm_mulVec_le_of_row_stochastic h_stochastic h_nonneg v
  have h_spectral_le_norm : spectralRadius ℝ (Matrix.toLin' A) ≤ ↑‖L‖₊ :=
    spectralRadius_le_opNorm A
  exact le_trans h_spectral_le_norm (ENNReal.coe_le_coe.mpr h_norm_le_one)

/-! ## Core Perron-Frobenius Theory -/

noncomputable def supportFinset (v : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => v i > 0)

noncomputable def kernelFinset (v : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => v i = 0)

lemma disjoint_kernel_support {v : n → ℝ} :
  Disjoint (supportFinset v) (kernelFinset v) := by
  simp only [supportFinset, kernelFinset, Finset.disjoint_left]
  intro i hi_support hi_kernel
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_support hi_kernel
  exact (hi_support.ne hi_kernel.symm).elim

/-- If a submodule contains a non-zero vector, then it is not the zero submodule. -/
theorem Submodule.ne_bot_of_mem {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} (v : M) (hv_mem : v ∈ p) (hv_ne_zero : v ≠ 0) : p ≠ ⊥ := by
  intro h_bot
  have h_zero : v = 0 := by
    rw [h_bot] at hv_mem
    exact hv_mem
  exact hv_ne_zero h_zero

lemma support_nonempty_of_ne_zero {v : n → ℝ}
  (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
  (supportFinset v).Nonempty := by
  by_contra h
  have h_all_nonpos : ∀ i, v i ≤ 0 := by
    intro i
    by_contra hi_pos
    push_neg at hi_pos
    have hi_in_support : i ∈ supportFinset v := by
      simp [supportFinset, Finset.mem_filter]
      exact hi_pos
    exact h ⟨i, hi_in_support⟩
  have : v = 0 := funext fun i =>
    le_antisymm (h_all_nonpos i) (hv_nonneg i)
  exact hv_ne_zero this

lemma spectrum.of_eigenspace_ne_bot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : V →ₗ[K] V} {μ : K}
    (h : Module.End.eigenspace f μ ≠ ⊥) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact h

/-- If a finite sum of non-negative terms is positive, at least one term must be positive. -/
lemma exists_pos_of_sum_pos {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h_nonneg : ∀ i, 0 ≤ f i) (h_sum_pos : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  by_contra h_not_exists
  push_neg at h_not_exists
  have h_all_zero : ∀ i, f i = 0 := by
    intro i
    exact le_antisymm (h_not_exists i) (h_nonneg i)
  have h_sum_zero : ∑ i, f i = 0 := by
    exact Finset.sum_eq_zero (fun i _ => h_all_zero i)
  exact h_sum_pos.ne' h_sum_zero

/-- For a non-negative `a`, `a * b` is positive iff both `a` and `b` are positive. -/
lemma mul_pos_iff_of_nonneg_left {a b : ℝ} (ha_nonneg : 0 ≤ a) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  refine' ⟨fun h_mul_pos => _, fun ⟨ha_pos, hb_pos⟩ => mul_pos ha_pos hb_pos⟩
  have ha_pos : 0 < a := by
    refine' lt_of_le_of_ne ha_nonneg fun ha_zero => _
    rw [ha_zero] at h_mul_pos
    subst ha_zero
    simp_all only [le_refl, zero_mul, lt_self_iff_false]
  simp_all only [mul_pos_iff_of_pos_left, and_self]

/-- If a scalar `μ` is an eigenvalue of a matrix `A`, then it is a root of its
characteristic polynomial. -/
lemma isRoot_of_hasEigenvalue {A : Matrix n n ℝ} {μ : ℝ}
    (h_eig : Module.End.HasEigenvalue (toLin' A) μ) :
    (charpoly A).IsRoot μ := by
  rw [← mem_spectrum_iff_isRoot_charpoly, spectrum_eq_spectrum_toLin']
  exact Module.End.hasEigenvalue_iff_mem_spectrum.mp h_eig

/-- The spectrum of a matrix `A` is equal to the spectrum of its corresponding linear map
`Matrix.toLin' A`. -/
theorem spectrum.Matrix_toLin'_eq_spectrum {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    spectrum R (Matrix.toLin' A) = spectrum R A := by
  exact AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (Pi.basisFun R n)) A
end Matrix

/-- If a linear map `f` has an eigenvector `v` for an eigenvalue `μ`, then `μ` is in the spectrum of `f`. -/
lemma Module.End.mem_spectrum_of_hasEigenvector {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : V →ₗ[K] V} {μ : K} {v : V} (h : HasEigenvector f μ v) :
    μ ∈ spectrum K f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector h
