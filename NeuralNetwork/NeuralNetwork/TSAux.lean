import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/- Simple ENNReal evaluation lemmas for the Gibbs one-step with Bernoulli bind. -/
namespace PMF
open scoped ENNReal NNReal

variable {α : Type}

/-- Bernoulli bind selecting the left pure branch gives mass `p`. -/
@[simp]
lemma bernoulli_bind_pure_apply_left_of_ne
    {p : ℝ≥0} (hp : p ≤ 1) {x y : α} (hxy : x ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) x
      = (p : ℝ≥0∞) := by
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) x
    = (p : ℝ≥0∞)
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, tsum_fintype]
  have : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; simp
  simp [this, hxy]

/-- Bernoulli bind selecting the right pure branch gives mass `1 - p`. -/
@[simp]
lemma bernoulli_bind_pure_apply_right_of_ne
    {p : ℝ≥0} (hp : p ≤ 1) {x y : α} (hxy : x ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) y
      = ((1 : ℝ≥0) - p : ℝ≥0) := by
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) y
    = ((1 : ℝ≥0) - p : ℝ≥0)
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, tsum_fintype]
  have : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; simp
  simp [this]
  simp_all only [ne_eq, Fintype.univ_bool]
  split
  next h =>
    subst h
    simp_all only [not_true_eq_false]
  next h => simp_all only [add_zero]

/-- Bernoulli bind at a point different from both pure branches has mass 0. -/
@[simp]
lemma bernoulli_bind_pure_apply_other
    {p : ℝ≥0} (hp : p ≤ 1) {x y z : α} (hzx : z ≠ x) (hzy : z ≠ y) :
    ((PMF.bernoulli p hp) >>= fun b => if b then PMF.pure x else PMF.pure y) z = 0 := by
  change (PMF.bind (PMF.bernoulli p hp) (fun b => if b then PMF.pure x else PMF.pure y)) z = 0
  rw [PMF.bind_apply]
  simp only [PMF.bernoulli_apply, tsum_fintype]
  have : (Finset.univ : Finset Bool) = ({false, true} : Finset Bool) := by
    ext b; simp
  simp [this, hzx, hzy]

end PMF
open scoped Topology Filter
open PMF Filter

variable {R : Type*} [LinearOrder R]
variable {U : Type*} [DecidableEq U]-- [Fintype U] [Nonempty U]
open ENNReal NNReal

-- strict monotonicity from order-hom + injective
lemma strictMono_of_injective_orderHom
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) : StrictMono f :=
  (OrderHomClass.mono f).strictMono_of_injective hf

/-- If `a > 0`, the piecewise {1, 0, 1/2} based on the sign of `a*v` matches that of `v`. -/
lemma piecewise01half_sign_mul_left_pos {a v : ℝ} (ha : 0 < a) :
    (if 0 < a * v then 1 else if a * v < 0 then 0 else (1/2 : ℝ))
    =
    (if 0 < v then 1 else if v < 0 then 0 else (1/2 : ℝ)) := by
  by_cases hvpos : 0 < v
  · have : 0 < a * v := Left.mul_pos ha hvpos
    simp [hvpos, this]
  · by_cases hvneg : v < 0
    · have : a * v < 0 := mul_neg_of_pos_of_neg ha hvneg
      simp [hvpos, hvneg, this, not_lt.mpr this.le]
    · have hv0 : v = 0 := le_antisymm (le_of_not_gt hvpos) (le_of_not_gt hvneg)
      simp [hv0]

/-- If `x < 0` then the {1,0,1/2} piecewise is ≤ 0 (it equals 0). -/
private lemma piecewise01half_le_zero_of_neg {x : ℝ} (hx : x < 0) :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) ≤ 0 := by
  have hnotpos : ¬ 0 < x := not_lt.mpr hx.le
  simp [hnotpos, hx]

variable [Field R]-- [LinearOrder R]-- [IsStrictOrderedRing R]
variable [DecidableEq U] [Fintype U] [Nonempty U]

/-- Map of a positive (resp. negative) argument remains positive (resp. negative)
under a strictly monotone embedding sending `0 ↦ 0`. -/
@[simp]
lemma map_pos_of_pos
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ] [RingHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) {x : R} (hx : 0 < x) : 0 < f x := by
  have hsm := strictMono_of_injective_orderHom (R:=R) (f:=f) hf
  simpa [map_zero f] using (hsm hx)

@[simp]
lemma map_neg_of_neg
    {F} [FunLike F R ℝ] [OrderHomClass F R ℝ] [RingHomClass F R ℝ]
    (f : F) (hf : Function.Injective f) {x : R} (hx : x < 0) : f x < 0 := by
  have hsm := strictMono_of_injective_orderHom (R:=R) (f:=f) hf
  simpa [map_zero f] using (hsm hx)

/-
  General limit lemmas for reals, used to analyze the zero-temperature limit.
  These are independent of the neural-network context (mathlib-ready).
-/
open Real Filter Topology Monotone

/-- Multiplication by a positive constant maps `atTop` to `atTop`. -/
lemma tendsto_mul_const_atTop_atTop_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => c * x) atTop atTop := by
  refine (Filter.tendsto_atTop_atTop).2 ?_
  intro M
  refine ⟨M / c, ?_⟩
  intro x hx
  exact (div_le_iff₀' hc).mp hx

/-- Multiplication by a negative constant maps `atTop` to `atBot`. -/
lemma tendsto_mul_const_atTop_atBot_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun x : ℝ => c * x) atTop atBot := by
  refine (Filter.tendsto_atTop_atBot).2 ?_
  intro M
  refine ⟨M / c, ?_⟩
  intro x hx
  exact (div_le_iff_of_neg' hc).mp hx

/-- As `T → 0+`, if `c > 0` then `c/T → +∞`. -/
lemma tendsto_c_div_atTop_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => c / T) (𝓝[>] (0 : ℝ)) atTop := by
  have h_inv : Tendsto (fun T : ℝ => T⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_mul := tendsto_mul_const_atTop_atTop_of_pos hc
  simpa [div_eq_mul_inv] using (h_mul.comp h_inv)

/-- As `T → 0+`, if `c < 0` then `c/T → -∞`. -/
lemma tendsto_c_div_atBot_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun T : ℝ => c / T) (𝓝[>] (0 : ℝ)) atBot := by
  have h_inv : Tendsto (fun T : ℝ => T⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h_mul := tendsto_mul_const_atTop_atBot_of_neg hc
  simpa [div_eq_mul_inv] using (h_mul.comp h_inv)

@[simp]
lemma signPiece_eq_half_iff_zero {x : ℝ} :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) = (1/2 : ℝ) ↔ x = 0 := by
  constructor
  · intro h
    by_cases h_pos : 0 < x
    · simp [h_pos] at h
    · by_cases h_neg : x < 0
      · simp [h_pos, h_neg] at h
      · simp [h_pos, h_neg] at h
        exact le_antisymm (not_lt.mp h_pos) (not_lt.mp h_neg)
  · intro h
    simp [h]

@[simp]
lemma ENNReal.ofReal_one_sub_signPiece_of_zero {x : ℝ} (hx : x = 0) :
    ENNReal.ofReal (1 - (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ))) = (1/2 : ℝ≥0∞) := by
  subst hx
  calc
    ENNReal.ofReal (1 - (if 0 < (0:ℝ) then 1 else if (0:ℝ) < 0 then 0 else (1/2 : ℝ)))
        = ENNReal.ofReal (1 - (1/2 : ℝ)) := by simp
    _ = ENNReal.ofReal ((1/2 : ℝ≥0) : ℝ) := by norm_num
    _ = (1/2 : ℝ≥0∞) := by
      simpa using (ENNReal.ofReal_coe_nnreal (p := (1/2 : ℝ≥0)))


/-- Real piecewise {1,0,1/2} driven by the sign of a real. -/
@[simp]
lemma piecewise_sign_eval (x : ℝ) :
    (if 0 < x then 1 else if x < 0 then 0 else (1/2 : ℝ)) =
      (if x > 0 then 1 else if x < 0 then 0 else (1/2 : ℝ)) := by
  by_cases hpos : 0 < x
  · simp [hpos]
  · by_cases hneg : x < 0
    · simp [hpos, hneg]
    · have : x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [this]
