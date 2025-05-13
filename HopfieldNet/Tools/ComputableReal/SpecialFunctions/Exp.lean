import HopfieldNet.Tools.ComputableReal.IsComputable
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ComputableℝSeq
namespace Exp
#exit
/-
The Taylor series error formula, where fN is the nth-order approximation:
f(x) - fN(x) = 1/(n+1)! * f^(n+1)(c) * x^(n+1) for some c in [0,x].

For exp:
exp(x) - expN(x) = 1/(n+1)! * exp(c) * x^(n+1)

|exp(x) - expN(x)| = |1/(n+1)! * exp(c) * x^(n+1)|
  <= |1/(n+1)! * exp(x) * x^(n+1)|

|expN(x) - exp(x)| <= 1/(n+1)! * exp(x) * x^(n+1)

expN(x) <= exp(x) + 1/(n+1)! * exp(x) * x^(n+1)

expN(x) <= exp(x) (1 + x^(n+1) / (n+1)!)

∴ exp(x) >= expN(x) / (1 + x^(n+1) / (n+1)!)

likewise,

exp(x) <= expN(x) / (1 - x^(n+1) / (n+1)!)
 if (1 - x^(n+1) / (n+1)!) >= 0, otherwise 0
-/

/-- A valid lower bound when 0 ≤ x. Forms a `CauSeq` that converges to Real.exp x from below.
Functions by dividing `n` by a constant `k` so that it's in the range `[0,1]`, taking `n` terms
of the Taylor expansion (which is an under-approximation), and then raising it to `k` again. -/
def exp_lb₀ (x : ℚ) (n : ℕ) : ℚ :=
  let xc := ⌈x⌉.toNat
  let y : ℚ := x / xc
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
  let ey : ℚ := (List.range n).foldr (fun (n : ℕ) v ↦ 1 + (y * v) / (n+1)) 1
  ey ^ xc

/-- A valid upper bound when 0 ≤ x. CauSeq that converges to Real.exp x from above. -/
def exp_ub₀ (x : ℚ) (n : ℕ) : ℚ :=
  let xc := ⌈x⌉.toNat
  let y : ℚ := x / xc
    -- (Finset.sum (Finset.range n) fun i => x ^ i / ↑(Nat.factorial i))
  let ey : ℚ := (List.range n).foldr (fun (n : ℕ) v ↦ 1 + (y * v) / (n+1)) 1
  let err : ℚ := 2 * y^(n+1) / (n+1).factorial
  (ey + err) ^ xc

lemma List_foldr_eq_finset_sum (x : ℚ) (n : ℕ) :
    List.foldr (fun n v => 1 + x * v / (↑n + 1)) 1 (List.range n)
    = ∑ i ∈ Finset.range (n + 1), x^i / i.factorial := by
  suffices ∀ (v : ℚ), List.foldr (fun n v => 1 + x * v / (↑n + 1)) v (List.range n)
      = (∑ i ∈ Finset.range n, x^i / i.factorial) + v * (x ^ n) / n.factorial by
    convert this 1
    simp [Finset.range_add_one, _root_.add_comm]
  induction n
  · simp
  · intro v
    rename_i n ih
    simp [Finset.range_add_one, List.range_succ, Nat.factorial_succ, ih]
    rw [add_mul, one_mul, add_div, pow_succ]
    suffices x * v / (↑n + 1) * x ^ n / ↑n.factorial = v * (x ^ n * x) / ((↑n + 1) * ↑n.factorial) by
      rw [this]
      ring
    field_simp
    ring_nf

theorem exp_lb₀_pos {x : ℚ} (n : ℕ) (hx : 0 ≤ x) : 0 < exp_lb₀ x n := by
  rw [exp_lb₀, List_foldr_eq_finset_sum, Finset.range_add_one']
  rw [Finset.sum_insert (by simp)]
  positivity

theorem exp_lb₀_ge_one {x : ℚ} (n : ℕ) (hx : 0 ≤ x) : 1 ≤ exp_lb₀ x n := by
  rw [exp_lb₀, List_foldr_eq_finset_sum, Finset.range_add_one']
  rw [Finset.sum_insert (by simp)]
  apply one_le_pow₀
  simpa using by positivity

theorem exp_lb₀_le_exp {x : ℚ} (n : ℕ) (hx : 0 ≤ x) : exp_lb₀ x n ≤ Real.exp x := by
  rw [exp_lb₀, List_foldr_eq_finset_sum]
  have he : Real.exp x = (Real.exp (x / ↑⌈x⌉.toNat)) ^ ⌈x⌉.toNat := by
    cases eq_or_lt_of_le hx
    · subst x; simp
    · rw [div_eq_mul_inv, Real.exp_mul, Real.rpow_inv_natCast_pow (Real.exp_nonneg ↑x)]
      rwa [Nat.ne_zero_iff_zero_lt, Int.lt_toNat, Int.lt_ceil]
  rw [he]
  push_cast
  apply pow_le_pow_left₀ (by positivity)
  apply_mod_cast Real.sum_le_exp_of_nonneg
  positivity

theorem exp_ub₀_ge_exp (x : ℚ) (n : ℕ) (hx : 0 ≤ x) : Real.exp x ≤ exp_ub₀ x n := by
  rw [exp_ub₀, List_foldr_eq_finset_sum]
  have he : Real.exp x = (Real.exp (x / ↑⌈x⌉.toNat)) ^ ⌈x⌉.toNat := by
    cases eq_or_lt_of_le hx
    · subst x; simp
    · rw [div_eq_mul_inv, Real.exp_mul, Real.rpow_inv_natCast_pow (Real.exp_nonneg ↑x)]
      rwa [Nat.ne_zero_iff_zero_lt, Int.lt_toNat, Int.lt_ceil]
  rw [he]
  push_cast
  apply pow_le_pow_left₀ (by positivity)
  have := Real.exp_bound' (x := (↑x / ↑⌈x⌉.toNat)) (by positivity) ?_ (Nat.zero_lt_succ n)
  · refine le_trans this ?_
    simp only [Nat.succ_eq_add_one, add_le_add_iff_left]
    rw [_root_.mul_comm 2, ← mul_div, ← mul_div]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [_root_.mul_comm, ← div_div]
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    rw [add_div, div_self (by positivity), ← one_add_one_eq_two, add_le_add_iff_left 1, one_div]
    apply inv_le_one_of_one_le₀
    simp
  · cases eq_or_lt_of_le hx
    · subst x; simp
    rw [div_le_one₀]
    · trans (⌈x⌉ : ℝ)
      · simpa using Int.le_ceil x
      · norm_cast
        simp only [Int.ofNat_toNat, le_sup_left]
    simpa

-- theorem _root_.Real.mul_log_one_plus_div_lt {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
--     x * Real.log (1 + t / x) < t := by
--   suffices Real.log (1 + t / x) < t / x by
--     rwa [_root_.mul_comm, ← lt_div_iff₀ hx]
--   convert Real.log_lt_sub_one_of_pos (x := 1 + t / x) (by positivity) ?_ using 1
--   · ring_nf
--   · simpa using ⟨ht.ne', hx.ne'⟩

-- theorem _root_.Real.mul_log_one_plus_div_le {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
--     x * Real.log (1 + t / x) ≤ t := by
--   cases eq_or_lt_of_le ht
--   · subst t; simp
--   · apply (Real.mul_log_one_plus_div_lt hx ‹_›).le

-- theorem _root_.Real.one_plus_div_pow_lt_exp {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
--     (1 + t / x) ^ x < Real.exp t := by
--   convert Real.exp_lt_exp_of_lt (x := x * Real.log (1 + t / x))
--     (Real.mul_log_one_plus_div_lt hx ht) using 1
--   rw [← Real.log_rpow (by positivity), Real.exp_log (by positivity)]

theorem _root_.Real.one_plus_pow_lt_exp_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 + x) ^ y < Real.exp (x * y) := by
  rw [Real.exp_mul, _root_.add_comm]
  exact Real.rpow_lt_rpow (by linarith) (Real.add_one_lt_exp hx.ne') hy

/-- This proves that the gap between `exp_lb₀` and `exp_ub₀` shrinks at least as
fast as `exp x * (exp (2x/n!) - 1)`. This is then used to prove that they are
cauchy sequences in `n`, i.e. taking sufficiently large `n` makes this go to zero. -/
theorem exp_ub₀_sub_exp_lb₀ {x : ℚ} (n : ℕ) (hx : 0 ≤ x) :
    exp_ub₀ x n - exp_lb₀ x n ≤ Real.exp x * (Real.exp (2 * x / n.factorial) - 1) := by
  rw [exp_ub₀, exp_lb₀]
  rw [List_foldr_eq_finset_sum]

  --Special case out x=0
  rcases eq_or_lt_of_le hx
  · subst x
    simp
  clear hx; rename_i hx

  set y := ∑ i ∈ Finset.range (n + 1), (x / ↑⌈x⌉.toNat) ^ i / ↑i.factorial with hdy
  set z := 2 * (x / ↑⌈x⌉.toNat) ^ (n + 1) / ↑(n + 1).factorial


  have hy : y ≠ 0 := by
    apply ne_of_gt
    rw [hdy, Finset.range_add_one', Finset.sum_insert (by simp)]
    positivity
  conv_lhs =>
    equals (y ^ ⌈x⌉.toNat * ((1 + z / y)^⌈x⌉.toNat - 1) : ℝ) =>
      rw [mul_sub, mul_one, ← mul_pow, mul_add, mul_one, mul_div_cancel₀]
      · norm_cast
      · norm_cast

  have hxn : 0 < ↑⌈x⌉.toNat := by simpa
  have hz : 0 < z := by positivity
  have hzy₀ : 0 < z / y := by positivity
  have hy₂ : y ^ ⌈x⌉.toNat ≤ Real.exp x := by
    have := exp_lb₀_le_exp n hx.le
    rw [exp_lb₀, List_foldr_eq_finset_sum] at this
    exact_mod_cast this

  have hzy₁ : z / y ≤ 2 * (x / ↑⌈x⌉.toNat) / n.factorial := by
    trans z
    · apply div_le_self hz.le
      rw [hdy, Finset.range_add_one']
      simp
      positivity
    · unfold z
      refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
      · simp only [pow_succ, Nat.ofNat_pos, mul_le_mul_left]
        refine mul_le_of_le_one_left (by positivity) ?_
        apply pow_le_one₀ (by positivity)
        rw [div_le_one₀ (by positivity)]
        refine (Int.le_ceil x).trans ?_
        exact_mod_cast Int.self_le_toNat ⌈x⌉
      · exact_mod_cast Nat.factorial_le (Nat.le_add_right n 1)

  have hzy₂ := calc ((1 + z / y) ^ ⌈x⌉.toNat : ℝ)
    _ ≤ (1 + 2 * (x / ⌈x⌉.toNat) / n.factorial) ^ ⌈x⌉.toNat := by
      norm_cast at hzy₁ ⊢
      apply pow_le_pow_left₀ (by positivity) (by linarith)
    _ < Real.exp (2 * (x / ⌈x⌉.toNat) * ⌈x⌉.toNat / n.factorial) := by
      convert Real.one_plus_pow_lt_exp_mul (y := ⌈x⌉.toNat)
        (Rat.cast_pos.mpr <| lt_of_lt_of_le hzy₀ hzy₁) (by simpa) using 2
      · norm_cast
      · norm_cast
        ring_nf
    _ ≤ Real.exp (2 * x / n.factorial) := by
      rw [mul_div, div_mul, div_self, div_one]
      simpa

  apply mul_le_mul hy₂ (by simpa using hzy₂.le) ?_ (Real.exp_nonneg _)
  rw [sub_nonneg]
  apply one_le_pow₀
  rw [le_add_iff_nonneg_right]
  positivity

/-- Unlike `exp_lb₀`, which only works for `0 ≤ x`, this is valid for all `x`. -/
def exp_lb (x : ℚ) : ℕ → ℚ :=
  if 0 ≤ x then exp_lb₀ x else fun n ↦ (exp_ub₀ (-x) n)⁻¹

/-- Unlike `exp_ub₀`, which only works for `0 ≤ x`, this is valid for all `x`. -/
def exp_ub (x : ℚ) : ℕ → ℚ :=
  if 0 ≤ x then exp_ub₀ x else fun n ↦ (exp_lb₀ (-x) n)⁻¹

theorem exp_lb_le_exp (x : ℚ) (n : ℕ) : exp_lb x n ≤ Real.exp x := by
  rw [exp_lb]
  split
  · apply exp_lb₀_le_exp n ‹_›
  · simp only [Rat.cast_inv]
    rw [← inv_inv (Real.exp _)]
    have := exp_ub₀_ge_exp (-x) n (by linarith)
    rw [inv_le_inv₀]
    · simpa [Real.exp_neg]
    · refine lt_of_lt_of_le ?_ this
      positivity
    · positivity

theorem exp_ub_ge_exp (x : ℚ) (n : ℕ) : Real.exp x ≤ exp_ub x n := by
  rw [exp_ub]
  split
  · apply exp_ub₀_ge_exp x n ‹_›
  · simp only [Rat.cast_inv]
    rw [← inv_inv (Real.exp _)]
    have := exp_lb₀_le_exp (x := -x) n (by linarith)
    rw [inv_le_inv₀]
    · simpa [Real.exp_neg]
    · positivity
    · exact_mod_cast exp_lb₀_pos (x := -x) n (by linarith)

theorem exp_ub_sub_exp_lb_of_nonneg {x : ℚ} (n : ℕ) (hx : 0 ≤ x) :
    exp_ub x n - exp_lb x n ≤ Real.exp x * (Real.exp (2 * x / n.factorial) - 1) := by
  simpa [exp_ub, hx, ↓reduceIte, exp_lb] using exp_ub₀_sub_exp_lb₀ n hx

theorem exp_ub_sub_exp_lb_of_neg {x : ℚ} (n : ℕ) (hx : x < 0) :
    exp_ub x n - exp_lb x n ≤ Real.exp (2 * ↑(-x) / n.factorial) - 1 := by
  simp only [exp_ub, Rat.not_le.mpr hx, ↓reduceIte, exp_lb]
  replace hx : 0 < -x := by linarith
  generalize -x=x' at hx ⊢; clear x; rename ℚ => x

  have hl₁ := exp_lb₀_pos n hx.le
  have hl₂ := exp_lb₀_le_exp n hx.le
  have hu₁ := exp_ub₀_ge_exp x n hx.le
  have hu₂ : 0 < exp_ub₀ x n := by rify at hl₁ ⊢; linarith
  have hlu := exp_ub₀_sub_exp_lb₀ n hx.le

  conv_lhs =>
    equals (exp_ub₀ x n - exp_lb₀ x n : ℝ) / (exp_ub₀ x n * exp_lb₀ x n) =>
      field_simp
      left
      ring_nf

  rw [div_le_iff₀ (by positivity)]
  refine hlu.trans ?_
  conv_rhs =>
    rw [_root_.mul_comm (Rat.cast _), ← _root_.mul_assoc, _root_.mul_comm]

  apply mul_le_mul hu₁ ?_ ?_ (by positivity)
  · apply le_mul_of_one_le_right
    · rw [sub_nonneg, Real.one_le_exp_iff]
      positivity
    · exact_mod_cast exp_lb₀_ge_one n hx.le
  · rw [sub_nonneg, Real.one_le_exp_iff]
    positivity

theorem exp_ub_lb_err (x : ℚ) (n : ℕ) :
    Real.exp x ≤ exp_lb x n + (Real.exp ↑|x| * (Real.exp (2 * |x| / n.factorial) - 1)) ∧
    exp_ub x n - (Real.exp ↑|x| * (Real.exp (2 * |x| / n.factorial) - 1)) ≤ Real.exp x := by
  have hl := exp_lb_le_exp x n
  have hu := exp_ub_ge_exp x n
  rcases lt_or_ge x 0 with hx | hx
  · have hlu := exp_ub_sub_exp_lb_of_neg n hx
    replace hlu := hlu.trans (le_mul_of_one_le_left (a := Real.exp ↑(-x)) ?_ ?_)
    · simp only [abs_of_neg hx]
      constructor <;> linarith
    · rw [sub_nonneg, Real.one_le_exp_iff]
      have : 0 < -x := by linarith
      positivity
    · simp [hx.le]
  · have hlu := exp_ub_sub_exp_lb_of_nonneg n hx
    simp only [abs_of_nonneg hx]
    constructor <;> linarith

private lemma err_antitone_n (x : ℝ) :
    Antitone fun (n : ℕ) ↦ Real.exp ↑|x| * (Real.exp (2 * |x| / n.factorial) - 1) := by
  apply Antitone.const_mul ?_ (Real.exp_nonneg |x|)
  simp_rw [sub_eq_add_neg]
  apply Antitone.add_const
  conv_rhs =>
    equals ((Real.exp) ∘ (fun n ↦ (2 * |x| / n.factorial))) =>
      ext x
      rfl
  refine Monotone.comp_antitone Real.exp_monotone ?_
  simp_rw [div_eq_mul_inv]
  apply Antitone.const_mul ?_ (by positivity)
  conv_rhs =>
    equals ((fun (x : ℕ) ↦ (↑x)⁻¹) ∘ (fun n ↦ n.factorial)) =>
      ext x
      rfl
  intro x y h
  field_simp
  apply one_div_le_one_div_of_le
  · exact Nat.cast_pos'.mpr (Nat.factorial_pos x)
  · exact Nat.cast_le.mpr (Nat.factorial_le h)

private lemma err_monotone_x (n : ℕ) :
    MonotoneOn (fun (x : ℝ) ↦ Real.exp x * (Real.exp (2 * x / n.factorial) - 1)) (Set.Ici 0) := by
  apply MonotoneOn.mul (Real.exp_monotone.monotoneOn _) ?_  (fun _ ↦ Real.exp_nonneg ·) ?_
  · simp_rw [sub_eq_add_neg]
    apply Monotone.monotoneOn
    apply Monotone.add_const
    conv_rhs =>
      equals ((Real.exp) ∘ (fun x ↦ (2 * x / n.factorial))) =>
        ext x
        rfl
    refine Monotone.comp Real.exp_monotone ?_
    simp_rw [_root_.mul_comm, ← mul_div]
    exact Monotone.mul_const monotone_id (by positivity)
  · intro x (hx : 0 ≤ x)
    rw [sub_nonneg, Real.one_le_exp_iff]
    positivity

private lemma inverr_monotone_x (ε : ℝ) (hε : 0 < ε):
    MonotoneOn (fun (x : ℝ) ↦ 2 * x / Real.log (1 + ε / Real.exp x)) (Set.Ici 0) := by
  apply MonotoneOn.mul ?_ ?_ ?_ ?_
  · apply MonotoneOn.mul monotoneOn_const ?_ (by norm_num) (by norm_num)
    intro x y h
    exact fun x_1 a => a
  · conv_lhs =>
      equals ((·⁻¹) ∘ Real.log ∘ (1 + ε / Real.exp ·)) =>
        ext x
        rfl
    suffices AntitoneOn (1 + ε / Real.exp ·) (Set.Ici 0) by
      intro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
      specialize this hx hy hxy
      dsimp at this ⊢
      replace this := Real.log_le_log (by positivity) this
      rwa [inv_le_inv₀]
      all_goals (
        apply Real.log_pos
        rw [lt_add_iff_pos_right]
        positivity
      )
    apply AntitoneOn.const_add
    intro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
    refine div_le_div₀ hε.le le_rfl (Real.exp_pos _) (Real.exp_le_exp.mpr hxy)
  · intro x (h : 0 ≤ x)
    positivity
  · intros
    rw [inv_nonneg, Real.log_nonneg_iff]
    · rw [le_add_iff_nonneg_right]; positivity
    · positivity

private lemma exists_n_bound_err (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ), ∀ (y : ℚ), ↑y ∈ Set.Icc a b →
      (Real.exp ↑|y| * (Real.exp (2 * |y| / n.factorial) - 1)) ≤ ε
    := by
  conv =>
    enter [1,n,y,h]
    equals 2 * |y| / Real.log (1 + ε / Real.exp |y|) ≤ n.factorial =>
      by_cases hy : y = 0
      · simp [hε.le, hy]
      have hy₂ : 0 < |y| := by simpa
      rw [← Rat.cast_abs]
      rw [_root_.mul_comm, ← le_div_iff₀ (by positivity)]
      rw [tsub_le_iff_right, _root_.add_comm]
      rw [← Real.le_log_iff_exp_le (by positivity)]
      rw [eq_iff_iff]
      apply div_le_comm₀ (by positivity) (Real.log_pos ?_)
      rw [lt_add_iff_pos_right]
      positivity
  let v₁ := 2 * |a| / Real.log (1 + ε / Real.exp |a|)
  let v₂ := 2 * |b| / Real.log (1 + ε / Real.exp |b|)
  let v₃ := ⌈max v₁ v₂⌉.toNat
  use v₃
  intro y ⟨hy₁, hy₂⟩
  trans (v₃ : ℝ)
  · trans max v₁ v₂
    · trans 2 * (|a| ⊔ |b|) / Real.log (1 + ε / Real.exp (|a| ⊔ |b|))
      · rw [Rat.cast_abs]
        exact inverr_monotone_x ε hε (abs_nonneg (y : ℝ)) (show 0 ≤ |a| ⊔ |b| by positivity)
          (abs_le_max_abs_abs hy₁ hy₂)
      · apply le_of_eq
        apply MonotoneOn.map_max (inverr_monotone_x ε hε)
        · exact abs_nonneg a
        · exact abs_nonneg b
    · unfold v₃
      trans ↑⌈v₁ ⊔ v₂⌉
      · exact Int.le_ceil (v₁ ⊔ v₂)
      · norm_cast
        simp
  · rw [Nat.cast_le]
    exact Nat.self_le_factorial v₃

theorem TLUW_lb_ub :
    TendstoLocallyUniformlyWithout (fun n x => exp_lb x n) Real.exp ∧
    TendstoLocallyUniformlyWithout (fun n x => exp_ub x n) Real.exp := by
  rw [TendstoLocallyUniformlyWithout]
  constructor
  all_goals (
    intro ε hε x
    obtain ⟨n,hn⟩ := exists_n_bound_err (x-1) (x+1) (half_pos hε)
    use Set.Icc (x-1) (x+1), Icc_mem_nhds (sub_one_lt x) (lt_add_one x), n
    intro b hb y ⟨hy₁, hy₂⟩
    specialize hn y ⟨hy₁, hy₂⟩
    rw [abs_sub_lt_iff]
    have hl := exp_lb_le_exp y b
    have hu := exp_ub_ge_exp y b
    have ⟨h₀, h₁⟩ := exp_ub_lb_err y b
    have h₂ := err_antitone_n y hb
    simp only [Rat.cast_abs] at h₀ h₁ hn
    constructor <;> linarith
  )

end Exp

def exp : ComputableℝSeq → ComputableℝSeq :=
  of_TendstoLocallyUniformly_Continuous Real.continuous_exp
  (fun n q ↦ ⟨⟨Exp.exp_lb q.fst n, Exp.exp_ub q.snd n⟩,
    Rat.cast_le.mp <|
      le_trans (Exp.exp_lb_le_exp q.fst n) <|
      le_trans (Real.exp_le_exp_of_le <| Rat.cast_le.mpr q.fst_le_snd) <|
      Exp.exp_ub_ge_exp q.snd n⟩)
  (fun n x ↦ Exp.exp_lb x n)
  (fun n x ↦ Exp.exp_ub x n)
  (fun n ⟨⟨q₁, _⟩, _⟩ _ ⟨hx, _⟩ ↦
    (Exp.exp_lb_le_exp q₁ n).trans (Real.exp_le_exp_of_le hx))
  (fun n ⟨⟨_, q₂⟩, _⟩ _ ⟨_, hx⟩ ↦
    (Real.exp_le_exp_of_le hx).trans (Exp.exp_ub_ge_exp q₂ n))
  (fun _ _ ↦ rfl)
  (Exp.TLUW_lb_ub.1)
  (Exp.TLUW_lb_ub.2)

end ComputableℝSeq

namespace IsComputable

instance instComputableExp (x : ℝ) [hx : IsComputable x] : IsComputable (Real.exp x) :=
  lift Real.exp ComputableℝSeq.exp
    (by apply ComputableℝSeq.val_of_TendstoLocallyUniformly_Continuous) hx

instance instComputableSinh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.sinh x) :=
  lift_eq (Real.sinh_eq x).symm inferInstance

instance instComputableCosh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.cosh x) :=
  lift_eq (Real.cosh_eq x).symm inferInstance

instance instComputableTanh (x : ℝ) [hx : IsComputable x] : IsComputable (Real.tanh x) :=
  lift_eq (Real.tanh_eq_sinh_div_cosh x).symm inferInstance

end IsComputable
