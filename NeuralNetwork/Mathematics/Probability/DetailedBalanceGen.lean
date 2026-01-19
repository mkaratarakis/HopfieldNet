import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.openClassical false

open MeasureTheory Filter Set

open scoped ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

namespace ProbabilityTheory.Kernel



/--
A reversible Markov kernel leaves the measure `π` invariant.
Proof uses detailed balance with `B = univ` and `κ x univ = 1`.
-/
theorem Invariant.of_IsReversible
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  have h' := (h_rev hs MeasurableSet.univ).symm
  have h'' : ∫⁻ x, κ x s ∂π = ∫⁻ x in s, κ x Set.univ ∂π := by
    simpa [Measure.restrict_univ] using h'
  have hConst : ∫⁻ x in s, κ x Set.univ ∂π = π s := by

    simp [measure_univ]
  have hπ : ∫⁻ x, κ x s ∂π = π s := h''.trans hConst
  calc
    (π.bind κ) s = ∫⁻ x, κ x s ∂π := Measure.bind_apply hs (Kernel.aemeasurable _)
    _ = π s := hπ
section ReversibilityFinite

open MeasureTheory ProbabilityTheory Classical

variable {α : Type*}
variable [Fintype α] [DecidableEq α]
variable [MeasurableSpace α] [MeasurableSingletonClass α]
variable (π : Measure α) (κ : Kernel α α)

section AuxFiniteSum

/-- General finite-type identity:
a sum over the whole type with an `if … ∈ S` guard can be rewritten
as a sum over the `Finset` of the elements that satisfy the guard. -/
lemma Finset.sum_if_mem_eq_sum_filter
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x := by
  have h_univ :
      (∑ x : α, (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0) := by
    simp
  have h_filter :
      (∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ.filter fun x : α => x ∈ S), f x := by
    simpa using
      (Finset.sum_filter
          (s := (Finset.univ : Finset α))
          (p := fun x : α => x ∈ S)
          (f := f)).symm
  have h_ident :
      (Finset.univ.filter fun x : α => x ∈ S) = S.toFinset := by
    ext x
    by_cases hx : x ∈ S
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
  simp [h_filter, h_ident]

lemma Finset.sum_subset_of_subset
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β)
    (_h₁ : ∀ x, x ∈ S.toFinset → True)
    (_h₂ : ∀ x, x ∈ S.toFinset → False → False)
    (_h₃ : ∀ x, x ∈ S.toFinset → True) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x :=
  Finset.sum_if_mem_eq_sum_filter S f

/-- Every subset of a finite type is finite. -/
lemma Set.finite_of_subsingleton_fintype
    {γ : Type*} [Fintype γ] (S : Set γ) : S.Finite :=
  (Set.toFinite _)

end AuxFiniteSum
section FiniteMeasureAPI
open scoped  ENNReal NNReal
open MeasureTheory

variable {α : Type*}

/-- On a finite discrete measurable space (⊤ σ–algebra), every set is measurable. -/
@[simp] lemma measurableSet_univ_of_fintype
    [Fintype α] [MeasurableSpace α] (hσ : ‹MeasurableSpace α› = ⊤)
    (s : Set α) : MeasurableSet s := by
  subst hσ; trivial

/-- For a finite type with counting measure, the (lower) integral
is the finite sum (specialization of the `tsum` version). -/
lemma lintegral_count_fintype
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [DecidableEq α]
    (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂(Measure.count : Measure α) = ∑ x : α, f x := by

  simpa [tsum_fintype] using (MeasureTheory.lintegral_count f)

-- Finite-type restricted lintegral as a weighted finite sum.
lemma lintegral_fintype_measure_restrict
    {α : Type*}
    [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α)
    (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  have hRestr :
      ∫⁻ x in A, f x ∂μ
        = ∑ x : α, f x * (μ.restrict A) {x} := by
    simpa using (lintegral_fintype (μ:=μ.restrict A) (f:=f))
  have hSingleton :
      ∀ x : α, (μ.restrict A) {x} = (if x ∈ A then μ {x} else 0) := by
    intro x
    by_cases hx : x ∈ A
    · have hInter : ({x} : Set α) ∩ A = {x} := by
        ext y; constructor
        · intro hy; rcases hy with ⟨hy1, hy2⟩
          simp at hy1
          subst hy1
          simp
        · intro hy
          simp [hy]
          simp_all only [MeasurableSet.singleton, Measure.restrict_apply, mem_singleton_iff]
      simp [Measure.restrict_apply, hx, hInter]
    · have hInter : ({x} : Set α) ∩ A = (∅ : Set α) := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have : y = x := by simpa [Set.mem_singleton_iff] using hy1
        subst this
        exact hx hy2
      simp [Measure.restrict_apply, hx, hInter]
  calc
    ∫⁻ x in A, f x ∂μ
        = ∑ x : α, f x * (μ.restrict A) {x} := hRestr
    _ = ∑ x : α, f x * (if x ∈ A then μ {x} else 0) := by
          simp [hSingleton]
    _ = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          by_cases hx : x ∈ A
          · simp [hx, mul_comm]
          · simp [hx]

/-- Probability measure style formula for a finite type:
turn a restricted integral into a finite sum with point masses. -/
lemma lintegral_fintype_prob_restrict
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  simpa using lintegral_fintype_measure_restrict μ A f

/-- Restricted version over the counting measure (finite type). -/
lemma lintegral_count_restrict
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [DecidableEq α]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂(Measure.count : Measure α)
      = ∑ x : α, (if x ∈ A then f x else 0) := by

  have h :=
    lintegral_fintype_prob_restrict (μ:=(Measure.count : Measure α)) A f
  have hμ : ∀ x : α, (Measure.count : Measure α) {x} = 1 := by
    intro x; simp
  simpa [hμ, one_mul] using h

/-- Convenience rewriting for the specific pattern used in detailed balance proofs:
move `μ {x}` factor to the left of function argument. -/
lemma lintegral_restrict_as_sum_if
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α)
    (g : α → ℝ≥0∞) :
    ∫⁻ x in A, g x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * g x else 0) :=
  lintegral_fintype_measure_restrict μ A g

end FiniteMeasureAPI

/-- Evaluation lemma for `Kernel.ofFunOfCountable`. Added for convenient rewriting/simp. -/
@[simp]
lemma ofFunOfCountable_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (f : α → Measure β) (a : α) :
    (Kernel.ofFunOfCountable f) a = f a := rfl

omit [Fintype α] in
/-- Finite discrete expansion of a restricted lintegral of a kernel (measurable singletons). -/
lemma lintegral_kernel_restrict_fintype [Fintype α]
    (A : Set α) :
    ∫⁻ x in A, κ x A ∂π
      =
    ∑ x : α, (if x ∈ A then π {x} * κ x A else 0) := by
  simpa using
    (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x A))

open MeasureTheory Set Finset Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- On a finite (any finite subset) space with measurable singletons, the measure of a finite
set under a kernel is the finite sum of the singleton masses. -/
lemma measure_eq_sum_finset
    [DecidableEq α] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    (κ : Kernel β α) (x : β) {B : Set α} (hB : B.Finite) :
    κ x B = ∑ y ∈ hB.toFinset, κ x {y} := by
  have hBset : B = (hB.toFinset : Finset α).toSet := by
    ext a; aesop
  set s : Finset α := hB.toFinset
  suffices H : κ x s.toSet = ∑ y ∈ s, κ x {y} by aesop
  refine s.induction_on ?h0 ?hstep
  · simp
  · intro a s ha_notin hIH
    have hDisj : Disjoint ({a} : Set α) s.toSet := by
      refine disjoint_left.mpr ?_
      intro y hy_in hy_in_s
      have : y = a := by simpa using hy_in
      subst this
      aesop
    have hMeas_s : MeasurableSet s.toSet := by
      refine s.induction_on ?m0 ?mstep
      · simp
      · intro b t hb_notin ht
        simpa [Finset.coe_insert, Set.image_eq_range, Set.union_comm, Set.union_left_comm,
               Set.union_assoc] using (ht.union (measurableSet_singleton b))
    have hMeas_a : MeasurableSet ({a} : Set α) := measurableSet_singleton a
    have hUnion :
        (insert a s).toSet
          = ({a} : Set α) ∪ s.toSet := by
      ext y; by_cases hy : y = a
      · subst hy; simp
      · simp [hy]
    have hAdd :
        κ x ((insert a s).toSet)
          = κ x ({a} : Set α) + κ x s.toSet := by
      rw [← measure_union_add_inter {a} hMeas_s]
      simp_rw [hUnion, measure_union_add_inter {a} hMeas_s]
      exact measure_union hDisj hMeas_s
    have hSum :
        ∑ y ∈ insert a s, κ x {y}
          = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := by
      simp [Finset.sum_insert, ha_notin]
    calc
      κ x ((insert a s).toSet)
          = κ x ({a} : Set α) + κ x s.toSet := hAdd
      _ = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := by rw [hIH]
      _ = ∑ y ∈ insert a s, κ x {y} := by simp [hSum]

/-- Finite discrete reversibility from pointwise detailed balance. -/
lemma isReversible_of_pointwise_fintype
    (hPoint :
      ∀ ⦃x y⦄, π {x} * κ x {y} = π {y} * κ y {x})
    : ProbabilityTheory.Kernel.IsReversible κ π := by
  intro A B hA hB
  have hFinA : A.Finite := Set.finite_of_subsingleton_fintype A
  have hFinB : B.Finite := Set.finite_of_subsingleton_fintype B
  have hAexp :
      ∫⁻ x in A, κ x B ∂π
        = ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
    have h1 :
        ∫⁻ x in A, κ x B ∂π
          = ∑ x : α,
              (if x ∈ A then π {x} * κ x B else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x B))
    have :
        (∑ x : α, (if x ∈ A then π {x} * κ x B else 0))
          =
        ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
      simp_rw
        [(Finset.sum_if_mem_eq_sum_filter
            (S:=A) (f:=fun x => π {x} * κ x B))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hBexp :
      ∫⁻ x in B, κ x A ∂π
        = ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
    have h1 :
        ∫⁻ x in B, κ x A ∂π
          = ∑ x : α,
              (if x ∈ B then π {x} * κ x A else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=B) (g:=fun x => κ x A))
    have :
        (∑ x : α, (if x ∈ B then π {x} * κ x A else 0))
          =
        ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
      simp_rw
        [(Finset.sum_if_mem_eq_sum_filter
            (S:=B) (f:=fun x => π {x} * κ x A))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hκB :
      ∀ x, κ x B = ∑ y ∈ hFinB.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinB)
  have hκA :
      ∀ x, κ x A = ∑ y ∈ hFinA.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinA)
  have hL :
      ∑ x ∈ hFinA.toFinset, π {x} * κ x B
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκB x, Finset.mul_sum]
  have hR :
      ∑ x ∈ hFinB.toFinset, π {x} * κ x A
        =
      ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκA x, Finset.mul_sum]
  erw [hAexp, hBexp, hL, hR]
  have hRew :
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y}
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    exact hPoint (x:=x) (y:=y)
  calc
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y}
          = ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := hRew
      _ = ∑ y ∈ hFinB.toFinset, ∑ x ∈ hFinA.toFinset, π {y} * κ y {x} := by
            simpa using
              (Finset.sum_comm :
                (∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset,
                    π {y} * κ y {x})
                  =
                ∑ y ∈ hFinB.toFinset, ∑ x ∈ hFinA.toFinset,
                    π {y} * κ y {x})
      _ = ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := rfl

end ReversibilityFinite
end ProbabilityTheory.Kernel

open scoped ENNReal NNReal

/-- Singleton evaluation of a PMF turned into a measure. -/
@[simp]
lemma PMF.toMeasure_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : α) :
    p.toMeasure {a} = p a := by
  rw [toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply_singleton]

/-- (Finite) evaluation of the measure of a set under a bind of PMFs. -/
lemma PMF.toMeasure_bind_fintype
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → PMF β) (B : Set β) (hB : MeasurableSet B) :
    (p.bind f).toMeasure B = ∑ a : α, p a * (f a).toMeasure B := by
  have hBind_apply : ∀ b : β, (p.bind f) b = ∑ a : α, p a * f a b := by
    intro b
    simp [PMF.bind_apply, tsum_fintype]
  have hMeasure :
    (p.bind f).toMeasure B
      = ∑ b : β, (p.bind f) b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
        have h0 :
          (p.bind f).toMeasure B
            = ∑ b : β, B.indicator (p.bind f) b := by
            simp [PMF.toMeasure, hB]
        refine h0.trans ?_
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hb : b ∈ B
        · simp [hb]
        · simp [hb]
  calc
    (p.bind f).toMeasure B
        = ∑ b : β, (p.bind f) b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := hMeasure
    _ = ∑ b : β, (∑ a : α, p a * f a b) *
            B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
            refine Finset.sum_congr rfl ?_; intro b _; simp [hBind_apply]
    _ = ∑ b : β, ∑ a : α, (p a * f a b) *
            B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
            refine Finset.sum_congr rfl ?_; intro b _
            have h := Finset.sum_mul (s:=Finset.univ)
                        (f:=fun a : α => p a * f a b)
                        (a:=B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
            simpa using h
    _ = ∑ a : α, ∑ b : β, (p a * f a b) *
            B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
            simpa using
              (Finset.sum_comm :
                (∑ b : β, ∑ a : α, (p a * f a b) *
                    B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
                  =
                ∑ a : α, ∑ b : β, (p a * f a b) *
                    B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
    _ = ∑ a : α, p a *
            (∑ b : β, f a b *
                B.indicator (fun _ : β => (1 : ℝ≥0∞)) b) := by
            refine Finset.sum_congr rfl ?_; intro a _
            have hTerm :
              ∑ b : β, (p a * f a b) *
                  B.indicator (fun _ : β => (1 : ℝ≥0∞)) b
                = p a * ∑ b : β, f a b *
                    B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
              have h2 :=
                (Finset.mul_sum (a:=p a) (s:=Finset.univ)
                  (f:=fun b : β => f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)).symm
              have hR :
                ∑ b : β, p a * (f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
                  = ∑ b : β, (p a * f a b) *
                      B.indicator (fun _ : β => (1 : ℝ≥0∞)) b := by
                  refine Finset.sum_congr rfl ?_; intro b _; simp [mul_assoc]
              simpa [hR] using h2
            simp [hTerm]
    _ = ∑ a : α, p a * (f a).toMeasure B := by
            refine Finset.sum_congr rfl ?_
            intro a _
            have hIndicator :
              (∑ b : β, f a b * B.indicator (fun _ : β => (1 : ℝ≥0∞)) b)
                = ∑ b : β, B.indicator (f a) b := by
              refine Finset.sum_congr rfl ?_
              intro b _
              by_cases hb : b ∈ B
              · simp [hb]
              · simp [hb]
            simp [hIndicator, PMF.toMeasure, hB]
