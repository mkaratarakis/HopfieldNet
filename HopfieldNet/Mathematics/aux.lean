import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Semicontinuous

open Filter Set Finset Matrix Topology Convex

/- Standard simplex definition
def stdSimplex (𝕜 ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] : Set (ι → 𝕜) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

-- Upper semicontinuous function definition
def UpperSemicontinuousOn {α β : Type*} [TopologicalSpace α] [Preorder β]
    (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y, f x < y → ∃ U ∈ 𝓝[s] x, ∀ z ∈ U, f z < y

-- Lower semicontinuous function definition
def LowerSemicontinuousOn {α β : Type*} [TopologicalSpace α] [Preorder β]
    (f : α → β) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y, y < f x → ∃ U ∈ 𝓝[s] x, ∀ z ∈ U, y < f z

-- Cluster point definition
def ClusterPt {X : Type*} [TopologicalSpace X] (x : X) (F : Filter X) : Prop :=
  (𝓝 x ⊓ F).NeBot

-- Ultrafilter definition
structure Ultrafilter (α : Type*) extends Filter α where
  isUltra : ∀ s, s ∈ toFilter ∨ sᶜ ∈ toFilter-/

/-!
## Key Theorems for Compactness & Ultrafilters
-/

/- Ultrafilter existence theorem
theorem Ultrafilter.exists_le {α : Type*} {F : Filter α} (h : F.NeBot) :
  ∃ U : Ultrafilter α, (U : Filter α) ≤ F := by
  exact Ultrafilter.exists_le F

-- Compactness characterization via ultrafilters
theorem isCompact_iff_ultrafilter_le_nhds {X : Type*} [TopologicalSpace X] {s : Set X} :
  IsCompact s ↔ ∀ (f : Ultrafilter X), s ∈ f → ∃ x ∈ s, (f : Filter X) ≤ 𝓝 x := by
  exact isCompact_iff_ultrafilter_le_nhds

-- Cluster point existence in compact sets
theorem IsCompact.exists_clusterPt {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsCompact s) {f : Filter X} (hf : f.NeBot) (hfs : f ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x f := by
  exact hs.exists_clusterPt hfs-/

-- Ultrafilter convergence from cluster point
theorem ClusterPt.exists_ultrafilter {X : Type*} [TopologicalSpace X] {x : X} {f : Filter X}
    (h : ClusterPt x f) : ∃ U : Ultrafilter X, (U : Filter X) ≤ f ∧ (U : Filter X) ≤ 𝓝 x := by
  exact clusterPt_iff_ultrafilter.mp h

/-!
## Semicontinuity Theorems
-/
/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is continuous on `s`,
then `f` maps `G` to the neighborhood filter of `f x`.
This is a version with lower and upper semicontinuity.
-/
lemma tendsto_of_lower_upper_semicontinuous_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder Y] [OrderTopology Y]
    {f : X → Y} {s : Set X} (h_upper : UpperSemicontinuousOn f s)
    (h_lower : LowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) :
    Tendsto f (G : Filter X) (𝓝 (f x)) := by
  have h_cont : ContinuousWithinAt f s x :=
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨h_lower x hx, h_upper x hx⟩
  exact h_cont.tendsto.comp (tendsto_id.mono_left hG)

/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is upper semicontinuous on `s`,
then for any `y' > f x`, `f` eventually maps elements of `G` to values less than `y'`.
-/
lemma upperSemicontinuousOn_eventually_lt_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X}
    (hf : UpperSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) {y' : Y} (hy' : f x < y') :
    ∀ᶠ (z : X) in (G : Filter X), f z < y' :=
  hG (hf x hx y' hy')

/--
If an ultrafilter `G` on `X` converges to `x` within `s`, and `f` is lower semicontinuous on `s`,
then for any `y' < f x`, `f` eventually maps elements of `G` to values greater than `y'`.
-/
lemma lowerSemicontinuousOn_eventually_gt_ultrafilter
    {X Y : Type*} [TopologicalSpace X] [LinearOrder Y] {f : X → Y} {s : Set X}
    (hf : LowerSemicontinuousOn f s) {x : X} (hx : x ∈ s) {G : Ultrafilter X}
    (hG : (G : Filter X) ≤ 𝓝[s] x) {y' : Y} (hy' : y' < f x) :
    ∀ᶠ (z : X) in (G : Filter X), y' < f z :=
  hG (hf x hx y' hy')



/-!
## Standard Simplex Properties
-/

/- Standard simplex is compact
theorem isCompact_stdSimplex (ι : Type*) [Fintype ι] : IsCompact (stdSimplex ℝ ι) := by
  exact _root_.isCompact_stdSimplex ι

-- Standard simplex is convex
theorem convex_stdSimplex (𝕜 ι : Type*) [OrderedRing 𝕜] [Fintype ι] :
    Convex 𝕜 (stdSimplex 𝕜 ι) := by
  exact _root_.convex_stdSimplex 𝕜 ι-/

-- Standard simplex is nonempty when ι is nonempty
theorem stdSimplex_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (stdSimplex ℝ ι).Nonempty := by
  exact ⟨(Fintype.card ι : ℝ)⁻¹ • 1, by simp [stdSimplex, Finset.sum_const, nsmul_eq_mul]⟩

/-!
## Supremum & Infimum Theorems
-/

-- Compact sets in ℝ attain their supremum
theorem IsCompact.exists_max {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty) :
  ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  let sup_s := sSup s
  have h_mem : sup_s ∈ s := sSup_mem hs hne
  use sup_s, h_mem
  intro y hy
  exact le_csSup (hs.bddAbove) hy

-- Function attaining maximum equals supremum of image
theorem isMaxOn_eq_sSup {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} {v : X}
    (hv : v ∈ s) (hmax : ∀ z ∈ s, f z ≤ f v) :
    sSup (f '' s) = f v := by
  apply le_antisymm
  · apply csSup_le
    · use f v
      refine ⟨v, hv, rfl⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hmax x hx
  · apply le_csSup
    · exact ⟨f v, fun a ha => by
        rcases ha with ⟨x, hx, rfl⟩
        exact hmax x hx⟩
    · exact Set.mem_image_of_mem f hv

/-!
## Filter & Ultrafilter Operations
-/

/- Ultrafilter mapping
def Ultrafilter.map {α β : Type*} (f : α → β) (u : Ultrafilter α) : Ultrafilter β :=
  ⟨Filter.map f u, by
    intro s
    have := u.isUltra (f ⁻¹' s)
    cases this with
    | inl h => left; exact Filter.mem_map.mpr h
    | inr h => right; exact Filter.mem_map.mpr h⟩

-- Ultrafilter equality from inclusion
theorem Ultrafilter.eq_of_le {α : Type*} {u v : Ultrafilter α} (h : (u : Filter α) ≤ v) :
    u = v := by
  exact Ultrafilter.eq_of_le h

-- Tendsto characterization for ultrafilters
theorem tendsto_map'_iff {α β : Type*} {f : α → β} {u : Ultrafilter α} {l : Filter β} :
    Tendsto f (u : Filter α) l ↔ (Ultrafilter.map f u : Filter β) ≤ l := by
  exact tendsto_map'_iff-/

/-!
## Helper Lemmas for Continuity
-/

-- Eventually to open set conversion
theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ (U : Set α), IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  aesop

-- Continuous infimum over finset
theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*} [Fintype ι]
    {s : Finset ι} {U : Set α} (hs : s.Nonempty) {f : ι → α → β}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf

-- Infimum monotonicity for subsets
theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f := by
  exact inf'_mono f h hs

/-!
## Matrix & Vector Operations
-/

-- Matrix-vector multiplication component
theorem matrix_mulVec_component {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (j : n) :
    (A *ᵥ v) j = ∑ i, A j i * v i := by
  simp [Matrix.mulVec]; rfl

-- Non-negative matrix preserves non-negative vectors
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

-- Positive matrix with positive vector gives positive result
theorem positive_mul_vec_pos {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp
    · exact mul_pos (hA_pos i k) hk_pos

/-!
## Utility Lemmas
-/

-- Existence of positive element in sum of non-negative elements
theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (h i) (hnonneg i)
  have h_sum_zero : ∑ i, x i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  have : 1 = 0 := by linarith
  exact absurd this (by norm_num)

-- Existence of non-zero element in non-zero vector
theorem exists_ne_zero_of_ne_zero [Fintype n] [Nonempty n] {n : Type*} {x : n → ℝ} (hx : x ≠ 0) : ∃ j, x j ≠ 0 := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := h
  have x_is_zero : x = 0 := by
    ext i
    exact h_all_zero i
  exact hx x_is_zero

-- Matrix power multiplication
theorem pow_mulVec_succ {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] {A : Matrix n n ℝ} (k : ℕ) (x : n → ℝ) :
    (A^(k+1)).mulVec x = A.mulVec ((A^k).mulVec x) := by
  simp only [mulVec_mulVec]
  rw [pow_succ']


/-!
## Finset Operations
-/

-- Infimum over finite type equals finset infimum
theorem iInf_apply_eq_finset_inf'_apply_fun {α β γ : Type*} [Fintype α] [Nonempty α]
    [ConditionallyCompleteLinearOrder γ] (f : α → β → γ) :
    (fun x => ⨅ i, f i x) = (fun x => (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x)) := by
  ext x
  have h1 : ⨅ i, f i x = ⨅ i ∈ Set.univ, f i x := by simp only [mem_univ, ciInf_unique]
  have h2 : ⨅ i ∈ Set.univ, f i x = ⨅ i ∈ (Finset.univ : Finset α), f i x := by
    congr
    ext i
    simp only [mem_univ, ciInf_unique, Finset.mem_univ]
  have h3 : ⨅ i ∈ (Finset.univ : Finset α), f i x =
           (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x) := by
    rw [Finset.inf'_eq_csInf_image]
    simp only [mem_univ, ciInf_unique, Finset.mem_univ, Finset.coe_univ, image_univ]
    rfl
  rw [h1, h2, h3]

-- Infimum over finite type equals conditional infimum
theorem iInf_eq_ciInf {α β : Type*} [Fintype α] [Nonempty α] [ConditionallyCompleteLinearOrder β]
    (f : α → β) : (⨅ i, f i) = ⨅ i ∈ (Set.univ : Set α), f i := by
  apply eq_of_forall_le_iff
  intro b
  simp only [mem_univ, ciInf_unique]

/-!
## Order & Field Properties
-/

-- Multiplication cancellation for positive elements
theorem mul_div_cancel_pos_right {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (h : a * b = c) (hb : 0 < b) : c / b = a := by
  rw [← h]
  exact mul_div_cancel_right₀ a hb.ne'

-- Non-positive times positive is non-positive
theorem mul_nonpos_of_nonpos_of_pos {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (ha : a ≤ 0) (hb : 0 < b) : a * b ≤ 0 := by
  cases' le_iff_eq_or_lt.mp ha with h h
  · rw [h, zero_mul, ← h]
  · exact (mul_neg_of_neg_of_pos h hb).le

-- Continuous infimum over finite index
theorem continuousOn_iInf {α β : Type*} [Fintype α] [Nonempty α] [TopologicalSpace β]
    {s : Set β} {f : α → β → ℝ} (hf : ∀ i, ContinuousOn (f i) s) :
    ContinuousOn (fun x => ⨅ i, f i x) s := by
  classical
  let g : β → ℝ := fun x => (Finset.univ : Finset α).inf' Finset.univ_nonempty (fun i => f i x)
  have hg : ContinuousOn g s := ContinuousOn.finset_inf'_apply Finset.univ_nonempty fun i _ => hf i
  have h_eq : (fun x => ⨅ i, f i x) = g := by
    dsimp [g]
    exact iInf_apply_eq_finset_inf'_apply_fun f
  rwa [h_eq]


namespace Fintype

lemma card_gt_one_of_nonempty_ne {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] :
    1 < Fintype.card α ↔ ∃ (i j : α), i ≠ j := by
  constructor
  · intro h
    obtain ⟨i⟩ : Nonempty α := ‹Nonempty α›
    have h_card_ne_one : Fintype.card α ≠ 1 := ne_of_gt h
    have : ∃ j, j ≠ i := by
      by_contra h_all_eq
      push_neg at h_all_eq
      have : ∀ x : α, x = i := h_all_eq
      have h_card_eq_one : Fintype.card α = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨i, this⟩
      exact h_card_ne_one h_card_eq_one
    obtain ⟨j, hj⟩ := this
    exact ⟨i, j, hj.symm⟩
  · intro ⟨i, j, hij⟩
    have : Fintype.card α ≥ 2 := by
      rw [← Finset.card_univ]
      have : ({i, j} : Finset α) ⊆ Finset.univ := by simp
      have : Finset.card ({i, j} : Finset α) ≤ Finset.card Finset.univ := Finset.card_le_card this
      have : Finset.card ({i, j} : Finset α) = 2 := by simp [hij]
      linarith
    linarith

end Fintype

/-!
## Additional Helper Theorems
-/

-- Sum of non-negative terms is positive if at least one term is positive
theorem sum_pos_of_mem {α : Type*} {s : Finset α} {f : α → ℝ}
    [DecidableEq α] (h_nonneg : ∀ a ∈ s, 0 ≤ f a) (a : α) (ha_mem : a ∈ s) (ha_pos : 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  have h_sum_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x :=
    Eq.symm (add_sum_erase s f ha_mem)
  have h_erase_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x :=
    Finset.sum_nonneg (λ x hx => h_nonneg x (Finset.mem_of_mem_erase hx))
  rw [h_sum_split]
  exact add_pos_of_pos_of_nonneg ha_pos h_erase_nonneg

-- Existence of positive element in positive sum
theorem exists_mem_of_sum_pos {α : Type*} {s : Finset α} {f : α → ℝ}
    (h_pos : 0 < ∑ a ∈ s, f a) (h_nonneg : ∀ a ∈ s, 0 ≤ f a) :
    ∃ a ∈ s, 0 < f a := by
  by_contra h; push_neg at h
  have h_zero : ∀ a ∈ s, f a = 0 := fun a ha => le_antisymm (h a ha) (h_nonneg a ha)
  have h_sum_zero : ∑ a ∈ s, f a = 0 := by rw [sum_eq_zero_iff_of_nonneg h_nonneg]; exact h_zero
  linarith

-- Multiplication positivity characterization
theorem mul_pos_iff_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h_mul_pos
    refine ⟨lt_of_le_of_ne ha ?_, lt_of_le_of_ne hb ?_⟩
    · rintro rfl; simp_all only [le_refl, zero_mul, lt_self_iff_false]
    · rintro rfl; simp_all only [le_refl, mul_zero, lt_self_iff_false]
  · rintro ⟨ha_pos, hb_pos⟩; exact mul_pos ha_pos hb_pos

/-- The infimum over a non-empty finset is equal to the infimum over the corresponding subtype. -/
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]

/-- The standard simplex is a closed set. -/
lemma isClosed_stdSimplex [Fintype n] : IsClosed (stdSimplex ℝ n) := by
  have h₁ : IsClosed (⋂ i, {x : n → ℝ | 0 ≤ x i}) :=
    isClosed_iInter (fun i ↦ isClosed_le continuous_const (continuous_apply i))
  have h_set_eq : {x : n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by { ext; simp }
  rw [← h_set_eq] at h₁
  have h₂ : IsClosed {x : n → ℝ | ∑ i, x i = 1} :=
    isClosed_eq (continuous_finset_sum _ (fun i _ ↦ continuous_apply i)) continuous_const
  exact IsClosed.inter h₁ h₂

lemma abs_le_of_le_of_neg_le {x y : ℝ} (h_le : x ≤ y) (h_neg_le : -x ≤ y) : |x| ≤ y := by
  rw [abs_le]
  constructor
  · linarith
  · exact h_le

/-- A sum over a finset can be split into the value at a point `a`
and the sum over the rest of the finset. -/
lemma sum_add_sum_erase {M : Type*} [AddCommMonoid M] [DecidableEq n] {s : Finset n} {f : n → M}
    (a : n) (ha : a ∈ s) :
    f a + ∑ i ∈ s.erase a, f i = ∑ i ∈ s, f i := by
  rw [add_sum_erase s f ha]

/-- A finset `s` is disjoint from its right complement. -/
@[simp]
lemma Finset.disjoint_compl_right [Fintype n] [DecidableEq n] {s : Finset n} :
    Disjoint s (univ \ s) := by
  rw [@Finset.disjoint_iff_inter_eq_empty]
  rw [@inter_sdiff_self]

/-- The standard simplex is bounded. -/
lemma bounded_stdSimplex' [Fintype n] [DecidableEq n] : Bornology.IsBounded (stdSimplex ℝ n) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use 1
  intro v hv
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  have h_le_one : v i ≤ 1 := by
    have h_sum_others_nonneg : 0 ≤ ∑ j ∈ univ.erase i, v j :=
      sum_nonneg fun j _ => hv.1 j
    have h_split : ∑ j ∈ univ, v j = v i + ∑ j ∈ univ.erase i, v j := by
      simp_all only [Finset.mem_univ, sum_erase_eq_sub, sub_nonneg, add_sub_cancel]
    linarith [hv.2, h_split, h_sum_others_nonneg]
  exact abs_le_of_le_of_neg_le h_le_one (by linarith [hv.1 i])

/-- For a vector on the standard simplex, if the sum of a subset of its components is 1,
    then the components outside that subset must be zero. -/
lemma mem_supp_of_sum_eq_one [Fintype n] [DecidableEq n] {v : n → ℝ} (hv : v ∈ stdSimplex ℝ n) (S : Finset n)
    (h_sum : ∑ i ∈ S, v i = 1) :
    ∀ i, v i ≠ 0 → i ∈ S := by
  intro i hi_ne_zero
  by_contra hi_not_in_S
  have h_sum_all : ∑ j, v j = 1 := hv.2
  have h_sum_split : ∑ j, v j = (∑ j ∈ S, v j) + (∑ j ∈ Sᶜ, v j) := by
    rw [@sum_add_sum_compl]
  rw [← h_sum, h_sum_split] at h_sum_all
  have h_sum_compl_zero : ∑ j ∈ Sᶜ, v j = 0 := by linarith
  have h_nonneg : ∀ j ∈ Sᶜ, 0 ≤ v j := fun j _ ↦ hv.1 j
  have h_v_compl_zero : ∀ j ∈ Sᶜ, v j = 0 :=
    (sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_compl_zero
  specialize h_v_compl_zero i (mem_compl.mpr hi_not_in_S)
  exact hi_ne_zero h_v_compl_zero

/-!
## End of Compressed API

This compressed API contains all essential definitions and theorems needed to complete
the Perron-Frobenius theorem formalization. It includes:

1. Core topology definitions (compactness, semicontinuity, ultrafilters)
2. Standard simplex properties
3. Supremum/infimum theorems for compact sets
4. Matrix and vector operations
5. Order and field properties
6. Finset operations and utility lemmas

All theorems are proven and ready for use in the main formalization.
-/
