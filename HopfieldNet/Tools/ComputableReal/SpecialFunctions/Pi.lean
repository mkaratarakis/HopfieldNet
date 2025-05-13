import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import HopfieldNet.Tools.ComputableReal.SpecialFunctions.Sqrt

open scoped QInterval

namespace ComputableℝSeq

section Pi
#exit
instance instComputableSqrtTwoAddSeries (x : ℝ) [hx : IsComputable x] (n : ℕ) :
    IsComputable (Real.sqrtTwoAddSeries x n) :=
  n.rec hx (fun _ _ ↦ IsComputable.instComputableSqrt _)

def sqrtTwoAddSeries_n : ℕ → ComputableℝSeq :=
  fun n ↦ (instComputableSqrtTwoAddSeries 0 n).seq

theorem sqrtTwoAddSeries_n_lb_le (n k : ℕ) : (sqrtTwoAddSeries_n n).lb k ≤ Real.sqrtTwoAddSeries 0 n := by
  rw [← IsComputable.prop (x := Real.sqrtTwoAddSeries 0 n)]
  exact ComputableℝSeq.hlb _ _

theorem sqrtTwoAddSeries_n_ub_ge (n k : ℕ) : Real.sqrtTwoAddSeries 0 n ≤ (sqrtTwoAddSeries_n n).ub k := by
  rw [← IsComputable.prop (x := Real.sqrtTwoAddSeries 0 n)]
  exact ComputableℝSeq.hub _ _

theorem sqrtTwoAddSeries_n_ub_pos (n k : ℕ) : (0 : ℝ) ≤ (sqrtTwoAddSeries_n n).ub k := by
   exact le_trans (Real.sqrtTwoAddSeries_zero_nonneg n) (sqrtTwoAddSeries_n_ub_ge n k)

theorem sqrtTwoAddSeries_n_lb_lt_two (n k : ℕ) : (sqrtTwoAddSeries_n n).lb k < 2 := by
  rify
  refine lt_of_le_of_lt ?_ (Real.sqrtTwoAddSeries_lt_two n)
  convert ComputableℝSeq.hlb _ _
  symm
  exact IsComputable.prop

theorem sqrtTwoAddSeries_n_succ_lb (n k : ℕ) :
    (sqrtTwoAddSeries_n (n + 1)).lb k = (Sqrt.sqrtq (2 + (sqrtTwoAddSeries_n n).lub k) k).fst := by
  rfl

theorem sqrtTwoAddSeries_n_succ_ub (n k : ℕ) :
    (sqrtTwoAddSeries_n (n + 1)).ub k = (Sqrt.sqrtq (2 + (sqrtTwoAddSeries_n n).lub k) k).snd := by
  rfl

theorem sqrtTwoAddSeries_n_lb_nonneg (n k : ℕ) : 0 ≤ (sqrtTwoAddSeries_n n).lb k := by
  cases n
  · rfl
  · apply Sqrt.sqrtq_nonneg

theorem sqrtTwoAddSeries_n_lb_gt_one (n k : ℕ) (hk : 3 ≤ k) : 1 ≤ (sqrtTwoAddSeries_n (n + 1)).lb k := by
  have h₀ : (0 : ℝ) ≤ ((sqrtTwoAddSeries_n n).lub k).snd := sqrtTwoAddSeries_n_ub_pos n k
  rw [sqrtTwoAddSeries_n_succ_lb, Sqrt.sqrt_lb_def,
    if_neg (by push_neg; change 0 < 2 + _; rify; positivity)]
  clear h₀

  have h₁ := sqrtTwoAddSeries_n_lb_nonneg n k
  rify at h₁ ⊢

  rw [show (2 + (sqrtTwoAddSeries_n n).lub k).toProd.1 = 2 + (sqrtTwoAddSeries_n n).lb k by rfl]
  set x : ℚ := (sqrtTwoAddSeries_n n).lb k
  have h₂ := Sqrt.sqrt_le_mkRat_add (2 + x) k
  generalize ↑(mkRat (Int.sqrt ((2 + x).num * 4 ^ k)) (((2 + x).den * 4 ^ k).sqrt + 1))=y at h₂ ⊢
  replace h₂ : √↑(2 + x) * (1 - 2 / 2^k) ≤ y := by
    ring_nf at h₂ ⊢
    linarith

  refine le_trans ?_ (le_trans (a := √↑(2 + x) * 3 / 4) ?_ h₂)
  · suffices 4 / 3 ≤ √↑(2 + x) by linarith
    apply Real.le_sqrt_of_sq_le
    push_cast
    linarith
  · rw [← mul_div]
    apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [show (3 / 4 : ℝ) = 1 - 2 / 8 by norm_num]
    apply sub_le_sub_left
    apply div_le_div₀ zero_le_two le_rfl Nat.ofNat_pos'
    rw [show 8 = (2 : ℝ) ^ 3 by norm_num]
    exact_mod_cast Nat.pow_le_pow_right Nat.ofNat_pos' hk

theorem sqrtTwoAddSeries_n_bounds (n k : ℕ) (hk : 3 ≤ k) :
    (sqrtTwoAddSeries_n n).ub k ≤ (sqrtTwoAddSeries_n n).lb k + 18 * n / 2^k
    := by
  induction n
  · simp only [CharP.cast_eq_zero, zero_div, mul_zero, add_zero]
    rfl
  rename_i n ih
  dsimp [lb, ub] at ih
  rify at ih ⊢
  rw [sqrtTwoAddSeries_n_succ_lb, sqrtTwoAddSeries_n_succ_ub]

  set x := ((sqrtTwoAddSeries_n n).lub k)

  have hl : (2 + x).fst ≤ 2 + Real.sqrtTwoAddSeries 0 n := by
    change ((2 + _ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, add_le_add_iff_left]
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop

  have hu : 2 + Real.sqrtTwoAddSeries 0 n ≤ (2 + x).snd := by
    change _ ≤ ((2 + _ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, add_le_add_iff_left]
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop

  have hm : 0 < (2 + x).fst := by
    change 0 < 2 + _
    suffices 0 ≤ x.fst by linarith
    apply sqrtTwoAddSeries_n_lb_nonneg n k

  have h₁ := Sqrt.sqrt_le_sqrtq_add (2 + Real.sqrtTwoAddSeries 0 n) (2 + x) k ⟨hl, hu⟩ hm
  have h₂ := Sqrt.sqrtq_sub_le_sqrt (2 + Real.sqrtTwoAddSeries 0 n) (2 + x) k ⟨hl, hu⟩ hm hk

  simp only [show (2 + x).snd = 2 + x.snd by rfl, show (2 + x).fst = 2 + x.fst by rfl] at h₁ h₂
  simp only [Rat.cast_add, Rat.cast_ofNat, add_sub_add_left_eq_sub, tsub_le_iff_right] at h₁ h₂

  set y := √(2 + Real.sqrtTwoAddSeries 0 n)
  set z := (Sqrt.sqrtq (2 + x) k).fst
  set w := (Sqrt.sqrtq (2 + x) k).snd
  set x₁ := x.fst
  set x₂ := x.snd

  have hgap : w - z ≤ (3 / 2) * ((↑x₂ - ↑x₁) / (√(2 + ↑x₁))) + 9 * y / 2^k := by
    rw [← mul_div] at h₁ h₂ ⊢
    conv at h₁ =>
      enter [2,2,2]
      rw [_root_.mul_comm]
    rw [← div_div] at h₁
    linarith

  have hxdiv : 3 / 2 * ((↑x₂ - ↑x₁) / √(2 + ↑x₁)) ≤ 18 * ↑n / 2 ^ k := by
    rcases n with _|n
    · simp [show x₁ = 0 by rfl, show x₂ = 0 by rfl]
    suffices (3 / 2) / √(2 + ↑x₁) ≤ 1 by stop
      rw [mul_div, _root_.mul_comm, ← mul_div]
      apply mul_le_of_le_of_le_one_of_nonneg
      · linarith
      · exact this
      · have : (x.fst : ℝ) ≤ x.snd := by exact_mod_cast x.fst_le_snd
        linarith [x.fst_le_snd]
    have hx₂ : 1 ≤ x₁ :=
      sqrtTwoAddSeries_n_lb_gt_one _ _ hk
    rify at hx₂
    rw [div_le_one₀ (by positivity), Real.le_sqrt' (by positivity)]
    linarith

  have hydiv : 9 * y / 2^k ≤ 18 / 2^k := by
    rw [div_le_div_iff_of_pos_right]
    · have hy2 : y < 2 := Real.sqrtTwoAddSeries_lt_two (n.succ)
      linarith
    · exact_mod_cast Nat.two_pow_pos k

  rw [mul_add, add_div]
  linarith

def sqrtTwoSubSqrtTwoAddSeries_n : ℕ → ComputableℝSeq :=
  fun n ↦ (inferInstance : IsComputable (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n))).seq

theorem sqrtTwoSubSqrtTwoAddSeries_eq (n k : ℕ) :
    (sqrtTwoSubSqrtTwoAddSeries_n n).lub k = Sqrt.sqrtq ((2 - sqrtTwoAddSeries_n n).lub k) k := by
  rfl

theorem real_sqrtTwoAddSeries_lb (n : ℕ) : 1 / 2 ^ n < √(2 - Real.sqrtTwoAddSeries 0 n) := by
  have h : 2 ≤ Real.pi - 1 / 4 ^ n := by
    have : 1 / 4 ^ n ≤ (1 : ℝ) := by
      rw [one_div]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.one_le_pow' n 3
    linarith [Real.pi_gt_three]

  have h₂ := lt_of_le_of_lt h (sub_right_lt_of_lt_add (Real.pi_lt_sqrtTwoAddSeries n))
  ring_nf at h₂
  rwa [lt_mul_iff_one_lt_left zero_lt_two, ← div_lt_iff₀ (by positivity)] at h₂

theorem sqrtTwoSubSqrtTwoAddSeries_lb (n k : ℕ) (hk : 3 ≤ k) :
    √(2 - Real.sqrtTwoAddSeries 0 n) ≤ (sqrtTwoSubSqrtTwoAddSeries_n n).lb k +
    (18 * n * 2 ^ n + 4) / 2 ^ k
     := by

  dsimp [lb]
  rw [sqrtTwoSubSqrtTwoAddSeries_eq]

  have h₁ := Sqrt.sqrt_le_sqrtq_add' (2 - Real.sqrtTwoAddSeries 0 n) ((2 - sqrtTwoAddSeries_n n).lub k) k
    ⟨?_, ?_⟩ ?_; rotate_left
  · change ((2 + -_ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop
  · change _ ≤ ((2 + -_ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop
  · linarith [Real.sqrtTwoAddSeries_lt_two n]

  have hx : ((2 - sqrtTwoAddSeries_n n).lub k).fst = 2 - (sqrtTwoAddSeries_n n).ub k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  have hy : ((2 - sqrtTwoAddSeries_n n).lub k).snd = 2 - (sqrtTwoAddSeries_n n).lb k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  simp only [hx, hy, Rat.cast_sub, Rat.cast_ofNat, sub_sub_sub_cancel_left] at h₁
  clear hx hy

  have h₄ := Real.sqrtTwoAddSeries_zero_nonneg n
  have h₅ := Real.sqrtTwoAddSeries_lt_two n
  have h₆ := sqrtTwoAddSeries_n_bounds n k hk
  have h₇ := (real_sqrtTwoAddSeries_lb n).le

  generalize
    (Sqrt.sqrtq ((2 - sqrtTwoAddSeries_n n).lub k) k).fst=w,
    (sqrtTwoAddSeries_n n).lb k=x,
    (sqrtTwoAddSeries_n n).ub k=y,
    Real.sqrtTwoAddSeries 0 n=z at *

  have h₈ : (↑y - ↑x) / √(2 - z) ≤ 18 * ↑n / 2 ^ k * 2 ^ n := by
    rw [div_eq_mul_inv]
    apply mul_le_mul
    · rify at h₆
      linarith
    · rw [← inv_inv (2^n),
        inv_le_inv₀ (by (have : 0 < 2 - z := by linarith); positivity) (by positivity),
        ← one_div]
      exact h₇
    · positivity
    · positivity

  have h₉ : 2 * √(2 - z) / 2 ^ k ≤ 4 / 2 ^ k := by
    apply div_le_div₀ zero_le_four ?_ (by positivity) le_rfl
    suffices √(2 - z) ≤ 2 by linarith
    rw [Real.sqrt_le_left zero_le_two]
    linarith

  have h₁₀ : ((18 * n * 2 ^ n + 4) / 2 ^ k : ℝ) = 18 * ↑n / 2 ^ k * 2 ^ n + 4 / 2 ^ k := by
    ring_nf

  linarith

theorem sqrtTwoSubSqrtTwoAddSeries_ub (n k : ℕ) (hk : 3 ≤ k) :
    (sqrtTwoSubSqrtTwoAddSeries_n n).ub k - (18 * n * 2 ^ n + 14) / 2 ^ k ≤ √(2 - Real.sqrtTwoAddSeries 0 n) := by
  dsimp [ub]
  rw [sqrtTwoSubSqrtTwoAddSeries_eq]

  have h₁ := Sqrt.sqrtq_sub_le_sqrt' (2 - Real.sqrtTwoAddSeries 0 n) ((2 - sqrtTwoAddSeries_n n).lub k) k
    ⟨?_, ?_⟩ ?_ hk; rotate_left
  · change ((2 + -_ : ℚ) : ℝ) ≤ _
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    rw [← ge_iff_le]
    convert ComputableℝSeq.hub _ _
    symm
    exact IsComputable.prop
  · change _ ≤ ((2 + -_ : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg]
    apply tsub_le_tsub_left
    convert ComputableℝSeq.hlb _ _
    symm
    exact IsComputable.prop
  · linarith [Real.sqrtTwoAddSeries_lt_two n]

  have hx : ((2 - sqrtTwoAddSeries_n n).lub k).fst = 2 - (sqrtTwoAddSeries_n n).ub k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  have hy : ((2 - sqrtTwoAddSeries_n n).lub k).snd = 2 - (sqrtTwoAddSeries_n n).lb k := by
    change (2 +- _) = _
    rw [sub_eq_add_neg]
    rfl
  simp only [hx, hy, Rat.cast_sub, Rat.cast_ofNat, sub_sub_sub_cancel_left] at h₁
  clear hx hy
  have h₄ := Real.sqrtTwoAddSeries_zero_nonneg n
  have h₅ := Real.sqrtTwoAddSeries_lt_two n
  have h₆ := sqrtTwoAddSeries_n_bounds n k hk
  have h₇ := (real_sqrtTwoAddSeries_lb n).le

  generalize
    (Sqrt.sqrtq ((2 - sqrtTwoAddSeries_n n).lub k) k).fst=w,
    (sqrtTwoAddSeries_n n).lb k=x,
    (sqrtTwoAddSeries_n n).ub k=y,
    Real.sqrtTwoAddSeries 0 n=z at *

  have h₈ : (↑y - ↑x) / √(2 - z) ≤ 18 * ↑n / 2 ^ k * 2 ^ n := by
    rw [div_eq_mul_inv]
    apply mul_le_mul
    · rify at h₆
      linarith
    · rw [← inv_inv (2^n),
        inv_le_inv₀ (by (have : 0 < 2 - z := by linarith); positivity) (by positivity),
        ← one_div]
      exact h₇
    · positivity
    · positivity

  have h₉ : 7 * √(2 - z) / 2 ^ k ≤ 14 / 2 ^ k := by
    apply div_le_div₀ (by norm_num) ?_ (by positivity) le_rfl
    suffices √(2 - z) ≤ 2 by linarith
    rw [Real.sqrt_le_left zero_le_two]
    linarith

  have h₁₀ : ((18 * n * 2 ^ n + 14) / 2 ^ k : ℝ) = 18 * ↑n / 2 ^ k * 2 ^ n + 14 / 2 ^ k := by
    ring_nf

  linarith

/-- See theorem Real.pi_lt_sqrtTwoAddSeries in Mathlib -/
def pi_lb (n : ℕ) : ℚ :=
  2 ^ (n + 1) * (sqrtTwoSubSqrtTwoAddSeries_n n).lb (3 * n)

/-- See theorem Real.pi_gt_sqrtTwoAddSeries in Mathlib -/
def pi_ub (n : ℕ) : ℚ :=
  2 ^ (n + 1) * (sqrtTwoSubSqrtTwoAddSeries_n n).ub (3 * n) + 1 / 4 ^ n

-- ~70ms for 10^-40 precision
-- #time #eval! Rat.toDecimal (prec := 40) (pi_ub 65 - 3.14159265358979323846264338327950288419716939937510)
-- #time #eval! Rat.toDecimal (prec := 40) (pi_lb 65 - 3.14159265358979323846264338327950288419716939937510)

theorem pi_lb_le_pi (n : ℕ) : pi_lb n ≤ Real.pi := by
  refine le_trans ?_ (Real.pi_gt_sqrtTwoAddSeries n).le
  simp only [pi_lb, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Nat.ofNat_pos, pow_pos, mul_le_mul_left]
  convert ComputableℝSeq.hlb _ _
  symm
  exact IsComputable.prop

theorem pi_ub_ge_pi (n : ℕ) : Real.pi ≤ pi_ub n := by
  refine le_trans (Real.pi_lt_sqrtTwoAddSeries n).le ?_
  simp only [one_div, pi_ub, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_inv,
    add_le_add_iff_right, Nat.ofNat_pos, pow_pos, mul_le_mul_left]
  rw [← ge_iff_le]
  convert ComputableℝSeq.hub _ _
  symm
  exact IsComputable.prop

theorem pi_lb_ge_pi_sub_pow (n : ℕ) (hn : 0 < n) : Real.pi - 41 * n / 2 ^ n ≤ pi_lb n := by
  suffices 2 ^ (n + 1) * ((18 * n * 2 ^ n + 4) / 2 ^ (3 * n)) + 1 / 4 ^ n ≤ (41 * n / 2 ^ n : ℚ) by
    rify at this
    rw [pi_lb]
    have h₁ := sqrtTwoSubSqrtTwoAddSeries_lb n (3 * n) (by omega)
    replace h₁ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 ^ (n + 1) by positivity)
    rw [mul_add] at h₁
    have h₂ := Real.pi_lt_sqrtTwoAddSeries n
    push_cast
    linarith

  by_cases hn' : n < 2
  · interval_cases n
    norm_num
  clear hn
  push_neg at hn'
  qify at hn'

  have h₁ : (2 ^ (n + 1) * ((18 * n * 2 ^ n + 4) / 2 ^ (3 * n)) + 1 / 4 ^ n : ℚ)
      = 36 * n / 2 ^ n + 9 / 4 ^ n := by
    rw [show (4 : ℚ) ^ n = (2 ^ 2) ^ n by rfl, ← pow_mul]
    field_simp
    ring_nf
  rw [h₁]; clear h₁

  suffices (9 / 4 ^ n : ℚ) ≤ 5 * n / 2 ^ n by
    simp only [← mul_div] at this ⊢
    linarith

  exact div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ rfl rfl n)

theorem pi_ub_le_pi_add_pow (n : ℕ) (hn : 0 < n) : pi_ub n ≤ Real.pi + 51 * n / 2 ^ n := by
  suffices 2 ^ (n + 1) * ((18 * n * 2 ^ n + 14) / 2 ^ (3 * n)) + 1 / 4 ^ n ≤ (51 * n / 2 ^ n : ℚ) by
    rify at this
    rw [pi_ub]
    have h₁ := sqrtTwoSubSqrtTwoAddSeries_ub n (3 * n) (by omega)
    replace h₁ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 ^ (n + 1) by positivity)
    rw [mul_sub] at h₁
    have h₂ := Real.pi_gt_sqrtTwoAddSeries n
    push_cast
    linarith

  by_cases hn' : n < 2
  · interval_cases n
    norm_num
  clear hn
  push_neg at hn'
  qify at hn'

  have h₁ : (2 ^ (n + 1) * ((18 * n * 2 ^ n + 14) / 2 ^ (3 * n)) + 1 / 4 ^ n : ℚ)
      = 36 * n / 2 ^ n + 29 / 4 ^ n := by
    rw [show (4 : ℚ) ^ n = (2 ^ 2) ^ n by rfl, ← pow_mul]
    field_simp
    ring_nf
  rw [h₁]; clear h₁

  suffices (29 / 4 ^ n : ℚ) ≤ 15 * n / 2 ^ n by
    simp only [← mul_div] at this ⊢
    linarith

  exact div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ rfl rfl n)

theorem pi_lb_causeq : ∃ (h' : IsCauSeq abs pi_lb), Real.mk ⟨pi_lb, h'⟩ = Real.pi := by
  refine Real.of_near pi_lb Real.pi ?_
  intro ε hε
  have h₁ := Filter.Tendsto.const_mul 41 (tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two)
  simp only [pow_one, mul_zero] at h₁
  replace h₁ := h₁.eventually_mem (Ioo_mem_nhds (neg_neg_iff_pos.mpr hε) hε)
  simp only [Set.mem_Ioo, Filter.eventually_atTop, ge_iff_le] at h₁
  obtain ⟨i, hi⟩ := h₁
  use max i 1
  intro j hj
  specialize hi j (le_of_max_le_left hj)
  rw [abs_lt]
  have h₂ := pi_lb_ge_pi_sub_pow j (le_of_max_le_right hj)
  rw [← mul_div] at h₂
  constructor
  · linarith
  · linarith [pi_lb_le_pi j]

theorem pi_ub_causeq : ∃ (h' : IsCauSeq abs pi_ub), Real.mk ⟨pi_ub, h'⟩ = Real.pi := by
  refine Real.of_near pi_ub Real.pi ?_
  intro ε hε
  have h₁ := Filter.Tendsto.const_mul 51 (tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two)
  simp only [pow_one, mul_zero] at h₁
  replace h₁ := h₁.eventually_mem (Ioo_mem_nhds (neg_neg_iff_pos.mpr hε) hε)
  simp only [Set.mem_Ioo, Filter.eventually_atTop, ge_iff_le] at h₁
  obtain ⟨i, hi⟩ := h₁
  use max i 1
  intro j hj
  specialize hi j (le_of_max_le_left hj)
  rw [abs_lt]
  have h₂ := pi_ub_le_pi_add_pow j (le_of_max_le_right hj)
  rw [← mul_div] at h₂
  constructor
  · linarith  [pi_ub_ge_pi j]
  · linarith

def Pi : ComputableℝSeq :=
  mk Real.pi
  (lub := fun n ↦ ⟨⟨pi_lb n, pi_ub n⟩,
    Rat.cast_le.mp <| (pi_lb_le_pi n).trans (pi_ub_ge_pi n)⟩)
  (hlb := pi_lb_le_pi)
  (hub := pi_ub_ge_pi)
  (hcl := pi_lb_causeq.rec (fun w _ ↦ w))
  (hcu := pi_ub_causeq.rec (fun w _ ↦ w))
  (heq := by
    obtain ⟨_, h₁⟩ := pi_lb_causeq
    obtain ⟨_, h₂⟩ := pi_ub_causeq
    rw [← Real.mk_eq, h₁, h₂]
  )

end Pi

end ComputableℝSeq

namespace IsComputable

instance instComputablePi : IsComputable (Real.pi) where
  seq := ComputableℝSeq.Pi
  prop := ComputableℝSeq.mk_val_eq_val

end IsComputable

example :
    2 < √(Real.pi + 1)
    ∧ √(1 - Real.pi) = 0
    ∧ 5 * Real.pi / √(2 + Real.pi) < 7
    ∧ (31415926 / 10000000 : ℚ) < Real.pi
    ∧ Real.pi < 31415927 / 10000000
    := by sorry
  --native_decide
