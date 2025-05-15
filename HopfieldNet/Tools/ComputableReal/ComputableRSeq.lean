import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Sign
import Mathlib.Tactic.Rify

import HopfieldNet.Tools.ComputableReal.aux_lemmas


namespace QInterval

scoped notation "ℚInterval" => NonemptyInterval ℚ

scoped instance (priority := 100) instMemℝℚInterval : Membership ℝ ℚInterval :=
  ⟨fun s a => s.fst ≤ a ∧ a ≤ s.snd⟩

section mul
/--Multiplication on intervals of ℚ. TODO: Should generalize to any LinearOrderedField... -/
def mul_pair (x y : ℚInterval) : ℚInterval :=
  let ⟨⟨xl,xu⟩,_⟩ := x
  let ⟨⟨yl,yu⟩,_⟩ := y
  ⟨⟨min (min (xl*yl) (xu*yl)) (min (xl*yu) (xu*yu)),
    max (max (xl*yl) (xu*yl)) (max (xl*yu) (xu*yu))⟩,
    by simp only [le_max_iff, min_le_iff, le_refl, true_or, or_true, or_self]⟩

/--Multiplication of intervals by a ℚ. TODO: Should generalize to any LinearOrderedField -/
def mul_q (x : ℚInterval) (y : ℚ) : ℚInterval :=
  if h : y ≥ 0 then
    ⟨⟨x.fst * y, x.snd * y⟩, by dsimp; nlinarith [x.2]⟩
  else
    ⟨⟨x.snd * y, x.fst * y⟩, by dsimp; nlinarith [x.2]⟩

scoped instance : Mul (ℚInterval) :=
  ⟨mul_pair⟩

scoped instance : HMul (ℚInterval) ℚ (ℚInterval) :=
  ⟨mul_q⟩

scoped instance : HDiv (ℚInterval) ℚ (ℚInterval) :=
  ⟨fun x y ↦ x * y⁻¹⟩

section slow
set_option maxHeartbeats 400000
theorem mul_pair_lb_is_lb {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y,
    (mul_pair x y).fst ≤ xv * yv := by stop
  intro xv ⟨hxl,hxu⟩ yv ⟨hyl,hyu⟩
  dsimp [mul_pair]
  push_cast
  rcases le_or_lt xv 0 with hxn|hxp
  all_goals rcases le_or_lt (y.fst:ℝ) 0 with hyln|hylp
  all_goals rcases le_or_lt (y.snd:ℝ) 0 with hyun|hyup
  all_goals try linarith
  all_goals repeat rw [min_def]
  all_goals split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃
  all_goals try nlinarith

theorem mul_pair_ub_is_ub {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y,
    (mul_pair x y).snd ≥ xv * yv := by stop
  intro xv ⟨hxl,hxu⟩ yv ⟨hyl,hyu⟩
  dsimp [mul_pair]
  push_cast
  rcases le_or_lt xv 0 with hxn|hxp
  all_goals rcases le_or_lt (y.1.1:ℝ) 0 with hyln|hylp
  all_goals rcases le_or_lt (y.1.2:ℝ) 0 with hyun|hyup
  all_goals try linarith
  all_goals repeat rw [max_def]
  all_goals split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃
  all_goals try nlinarith

end slow

theorem mem_mul_pair {x y : ℚInterval} : ∀ xv ∈ x, ∀ yv ∈ y, xv * yv ∈ mul_pair x y :=
  fun _ hx _ hy ↦ ⟨mul_pair_lb_is_lb _ hx _ hy, mul_pair_ub_is_ub _ hx _ hy⟩

end mul

scoped instance instRatCastQInterval : RatCast ℚInterval :=
  ⟨fun q ↦ NonemptyInterval.pure q⟩

scoped instance instOfNatQInterval : OfNat ℚInterval n :=
  ⟨NonemptyInterval.pure n⟩

end QInterval

/-- Type class for sequences that converge to some real number from above and below. `lub` is a
  function that gives upper *and* lower bounds, bundled so it can reuse computation. `hcau`
  asserts that the two bounds are Cauchy sequences, `hlub` asserts that they're valid
  lower and upper bounds, and `heq'` asserts that they converge to a common value. Use
  `ComputableℝSeq.mk` to construct with regards to a reference real value.

  The defs `lb`, `ub` are the actual CauSeq's , `val` is the associated real number,
  and `hlb`, `hub`, and `heq` relate `lb` `ub` and `val` to each other. -/
structure ComputableℝSeq where
  mk' ::
  lub : ℕ → NonemptyInterval ℚ
  hcl : IsCauSeq abs fun n ↦ (lub n).fst
  hcu : IsCauSeq abs fun n ↦ (lub n).snd
  hlub : ∀n, (lub n).fst ≤ (Real.mk ⟨fun n ↦ (lub n).fst, hcl⟩) ∧
    (lub n).snd ≥ (Real.mk ⟨fun n ↦ (lub n).fst, hcl⟩)
  heq' : let lb : CauSeq ℚ abs := ⟨fun n ↦ (lub n).fst, hcl⟩
        let ub : CauSeq ℚ abs := ⟨fun n ↦ (lub n).snd, hcu⟩
        lb ≈ ub

namespace ComputableℝSeq

open scoped QInterval

def lb (x : ComputableℝSeq) : CauSeq ℚ abs := ⟨fun n ↦ (x.lub n).fst, x.hcl⟩

def ub (x : ComputableℝSeq) : CauSeq ℚ abs := ⟨fun n ↦ (x.lub n).snd, x.hcu⟩

/-- Get the real value determined by the sequence. (Irreducibly) given here as the limit of
  the lower bound sequence. -/
irreducible_def val (x : ComputableℝSeq) : ℝ := Real.mk x.lb

theorem heq (x : ComputableℝSeq) : x.lb ≈ x.ub :=
  x.heq'

theorem lb_eq_ub (x : ComputableℝSeq) : Real.mk x.lb = Real.mk x.ub :=
  Real.mk_eq.2 x.heq'

theorem val_eq_mk_lb (x : ComputableℝSeq) : x.val = Real.mk x.lb :=
  val_def x

theorem val_eq_mk_ub (x : ComputableℝSeq) : x.val = Real.mk x.ub :=
  x.val_eq_mk_lb.trans x.lb_eq_ub

theorem hlb (x : ComputableℝSeq) : ∀n, x.lb n ≤ x.val :=
  fun n ↦ val_eq_mk_lb _ ▸ (x.hlub n).1

theorem hub (x : ComputableℝSeq) : ∀n, x.ub n ≥ x.val :=
  fun n ↦ val_eq_mk_lb _ ▸ (x.hlub n).2

theorem val_mem_interval (x : ComputableℝSeq) : ∀n, x.val ∈ x.lub n :=
  fun n ↦ ⟨x.hlb n, x.hub n⟩

private theorem val_uniq' {x : ℝ} {lb ub : CauSeq ℚ abs} (hlb : ∀n, lb n ≤ x)
    (hub : ∀n, ub n ≥ x) (heq : lb ≈ ub) : Real.mk lb = x :=
  (Real.of_near lb x (fun εℝ hεℝ ↦
      let ⟨ε, ⟨hε₁, hε₂⟩⟩ := exists_rat_btwn hεℝ
      let ⟨i,hi⟩ := heq ε (Rat.cast_pos.1 hε₁)
      ⟨i, fun j hj ↦ by stop
        replace hi := hi j hj
        have hl₁ := hlb j
        have hu₂ := hub j
        rify at hi hl₁ hu₂ hε₁
        rw [abs_ite_le] at hi ⊢
        split_ifs at hi ⊢
        <;> linarith⟩)).2

/-- If a real number x is bounded below and above by a sequence, it must be the value of that sequence. -/
theorem val_uniq {x : ℝ} {s : ComputableℝSeq} (hlb : ∀n, s.lb n ≤ x) (hub : ∀n, s.ub n ≥ x) :
    s.val = x :=
  s.val_def ▸ val_uniq' hlb hub s.heq

/-- Make a computable sequence for x from a separate lower and upper bound CauSeq. -/
def mk (x : ℝ) (lub : ℕ → ℚInterval)
    (hcl : IsCauSeq abs (fun n ↦ (lub n).fst))
    (hcu : IsCauSeq abs (fun n ↦ (lub n).snd))
    (hlb : ∀n, (lub n).fst ≤ x)
    (hub : ∀n, (lub n).snd ≥ x)
    (heq : let lb : CauSeq ℚ abs := ⟨fun n ↦ (lub n).fst, hcl⟩
        let ub : CauSeq ℚ abs := ⟨fun n ↦ (lub n).snd, hcu⟩
        lb ≈ ub) : ComputableℝSeq where
  lub := lub
  hcl := hcl
  hcu := hcu
  heq' := heq
  hlub n := by
    rw [val_uniq' hlb hub heq]
    exact ⟨hlb n, hub n⟩

theorem mk_val_eq_val : (mk x v h₁ h₂ h₃ h₄ h₅).val = x :=
  val_uniq (by convert h₃) (by convert h₄)

theorem lb_le_ub (x : ComputableℝSeq) : ∀n, x.lb n ≤ x.ub n :=
  fun n ↦ Rat.cast_le.mp (le_trans (x.hlb n) (x.hub n))

@[ext]
theorem ext {x y : ComputableℝSeq} (h₁ : ∀ n, x.lb n = y.lb n) (h₂ : ∀ n, x.ub n = y.ub n) : x = y :=
  mk'.injEq _ _ _ _ _ _ _ _ _ _ ▸ (funext fun n ↦ NonemptyInterval.ext (Prod.ext (h₁ n) (h₂ n)))

/-- All rational numbers `q` have a computable sequence: the constant sequence `q`. -/
def ofRat (q : ℚ) : ComputableℝSeq :=
  mk q
    (fun _ ↦ NonemptyInterval.pure q)
    (IsCauSeq.const q) (IsCauSeq.const q)
    (fun _ ↦ rfl.le) (fun _ ↦ rfl.le)
    (Real.mk_eq.mp rfl)

instance natCast : NatCast ComputableℝSeq where natCast n := ofRat n

instance intCast : IntCast ComputableℝSeq where intCast z := ofRat z

instance ratCast : RatCast ComputableℝSeq where ratCast q := ofRat q

def add (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq :=
  mk (x.val + y.val)
  (fun n ↦ x.lub n + y.lub n)
  (IsCauSeq.add x.hcl y.hcl)
  (IsCauSeq.add x.hcu y.hcu)
  (by stop
    intro n
    rw [NonemptyInterval.fst_add]
    push_cast
    exact add_le_add (x.hlb n) (y.hlb n))
  (by stop
    intro n
    rw [NonemptyInterval.snd_add]
    push_cast
    exact add_le_add (x.hub n) (y.hub n))
  (have := CauSeq.add_equiv_add x.heq y.heq; this) --TODO why does 'inlining' the have not work

def neg (x : ComputableℝSeq) : ComputableℝSeq :=
  mk (-x.val)
  (fun n ↦ -x.lub n)
  (IsCauSeq.neg x.hcu)
  (IsCauSeq.neg x.hcl)
  (by simpa using x.hub ·)
  (by simpa using x.hlb ·)
  (have := CauSeq.neg_equiv_neg (Setoid.symm x.heq); this)

def sub (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq :=
  add x (neg y)

-- def applyℚMono (x : ComputableℝSeq) (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q)
--     (hf₁ : Monotone fr) (hf₂ : Continuous fr) : ComputableℝSeq :=
--   mk (x := fr x.val)
--   (lb := x.lb.apply fq (hf₂.continuous_embed fq hfr))
--   (ub := x.ub.apply fq (hf₂.continuous_embed fq hfr))
--   (hlb := fun n ↦ (hfr _).symm ▸ (hf₁ (x.hlb n)))
--   (hub := fun n ↦ (hfr _).symm ▸ (hf₁ (x.hub n)))
--   (heq := CauSeq.equiv_apply x.lb x.ub fq (hf₂.continuous_embed fq hfr) x.heq)

-- @[simp]
-- theorem val_applyℚMono : (applyℚMono x fq fr h₁ h₂ h₃).val = fr x.val :=
--   mk_val_eq_val

-- def applyℚAnti (x : ComputableℝSeq) (fq : ℚ → ℚ) (fr : ℝ → ℝ) (hfr : ∀q, fq q = fr q)
--     (hf₁ : Antitone fr) (hf₂ : Continuous fr) : ComputableℝSeq :=
--   applyℚMono (neg x) (fq∘Neg.neg) (fr∘Neg.neg)
--     (fun q ↦ by have := hfr (-q); rwa [Rat.cast_neg] at this)
--     (hf₁.comp monotone_id.neg)
--     (hf₂.comp ContinuousNeg.continuous_neg)

-- @[simp]
-- theorem val_applyℚAnti : (applyℚAnti x fq fr h₁ h₂ h₃).val = fr x.val := by
--   rw [applyℚAnti, val_applyℚMono, neg, mk_val_eq_val]
--   dsimp
--   rw [neg_neg]

-- --Faster one for rational multiplcation
-- def lb_mul_q [hx : ComputableℝSeq x] : CauSeq ℚ qabs :=
--   if q ≥ 0 then hx.lb * CauSeq.const qabs q else hx.ub * CauSeq.const qabs q

-- def ub_mul_q [hx : ComputableℝSeq x] : CauSeq ℚ qabs :=
--   if q ≥ 0 then hx.ub * CauSeq.const qabs q else hx.lb * CauSeq.const qabs q

-- /- Multiplication of two computable sequences. Can't just use CauSeq mul because that
--  no longer gives correct upper/lower bounds. -/
-- def ComputableℝSeqMul [hx : ComputableℝSeq x] : ComputableℝSeq (x * q) where
--   lb := lb_mul_q x q
--   ub := ub_mul_q x q
--   hlb n := by
--     simp_rw [lb_mul_q, min_def]
--     by_cases hq : (q:ℝ) > 0
--     <;> split_ifs with h
--     <;> rify at *
--     <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
--   hub n := by
--     simp_rw [ub_mul_q, max_def]
--     by_cases hq : (q:ℝ) > 0
--     <;> split_ifs with h
--     <;> rify at *
--     <;> nlinarith (config := {splitNe := true}) [hx.hlb n, hx.hub n]
--   heq := by
--     have : (ub_mul_q x q - lb_mul_q x q)
--       = fun n => (abs (ub x n - lb x n)) * (abs q) := by
--       funext n
--       dsimp
--       simp_rw [ub_mul_q, lb_mul_q]
--       simp_rw [min_def, max_def, abs_ite_le]
--       split_ifs <;> nlinarith
--     rw [this]
--     apply IsCauSeq.mul
--     · intro ε hε
--       obtain ⟨i, hi⟩ := hx.hgap ε hε
--       use i
--       intro j hj
--       replace hi := hi j hj
--       simp_rw [abs_ite_le] at hi ⊢
--       split_ifs at hi ⊢
--       <;> dsimp at * <;> linarith
--     · exact IsCauSeq.const _

-- instance instComputableQMul [ComputableℝSeq x] : ComputableℝSeq (q * x) :=
--   mul_comm x q ▸ instComputableMulQ x q


/-- "Bundled" multiplication to give lower and upper bounds. This bundling avoids the need to
  call lb and ub separately for each half (which, in a large product, leads to an exponential
  slowdown). This could be further optimized to use only two ℚ multiplications instead of four,
  when the sign is apparent. -/
def mul' (x : ComputableℝSeq) (y : ComputableℝSeq) : ℕ → ℚInterval :=
  fun n ↦ QInterval.mul_pair (x.lub n) (y.lub n)

/-- More friendly expression for the lower bound for multiplication, as a CauSeq. -/
def mul_lb (x : ComputableℝSeq) (y : ComputableℝSeq) : CauSeq ℚ abs :=
  ((x.lb * y.lb) ⊓ (x.ub * y.lb)) ⊓ ((x.lb * y.ub) ⊓ (x.ub * y.ub))

/-- More friendly expression for the lower bound for multiplication, as a CauSeq. -/
def mul_ub (x : ComputableℝSeq) (y : ComputableℝSeq) : CauSeq ℚ abs :=
  ((x.lb * y.lb) ⊔ (x.ub * y.lb)) ⊔ ((x.lb * y.ub) ⊔ (x.ub * y.ub))

/-- The lower bounds from `mul'` are precisely the same sequence as `mul_lb`. -/
theorem fst_mul'_eq_mul_lb : (fun i ↦ i.fst) ∘ mul' x y = (mul_lb x y).1 := by stop
  ext n
  dsimp
  rw [mul', mul_lb]
  congr

/-- The upper bounds from `mul'` are precisely the same sequence as `mul_ub`. -/
theorem snd_mul'_eq_mul_ub : (fun i ↦ i.snd) ∘ mul' x y = (mul_ub x y).1 := by stop
  ext n
  dsimp
  rw [mul', mul_ub]
  congr

/-- The lower bounds from `mul'` form a Cauchy sequence. -/
theorem mul'_fst_iscau : IsCauSeq abs ((fun i ↦ i.fst) ∘ (mul' x y)) :=
  fst_mul'_eq_mul_lb ▸ Subtype.property _

/-- The upper bounds from `mul'` form a Cauchy sequence. -/
theorem mul'_snd_iscau : IsCauSeq abs ((fun i ↦ i.snd) ∘ (mul' x y)) :=
  snd_mul'_eq_mul_ub ▸ Subtype.property _

theorem lb_ub_mul_equiv (x : ComputableℝSeq) (y : ComputableℝSeq) :
    mul_lb x y ≈ mul_ub x y := by stop
  have : x.lb ≈ x.lb := by rfl
  have : x.ub ≈ x.ub := by rfl
  have : y.lb ≈ y.lb := by rfl
  have : y.ub ≈ y.ub := by rfl
  have := x.heq
  have := Setoid.symm x.heq
  have := y.heq
  have := Setoid.symm y.heq
  dsimp [mul_lb, mul_ub]
  apply CauSeq.inf_equiv_of_equivs
  <;> apply CauSeq.inf_equiv_of_equivs
  <;> apply CauSeq.equiv_sup_of_equivs
  <;> apply CauSeq.equiv_sup_of_equivs
  <;> exact CauSeq.mul_equiv_mul ‹_› ‹_›

theorem mul_lb_is_lb (x : ComputableℝSeq) (y : ComputableℝSeq) (n : ℕ) :
    (mul_lb x y).1 n ≤ x.val * y.val :=
  QInterval.mul_pair_lb_is_lb _ (x.val_mem_interval n) _ (y.val_mem_interval n)

theorem mul_ub_is_ub (x : ComputableℝSeq) (y : ComputableℝSeq) (n : ℕ) :
    (mul_ub x y).1 n ≥ x.val * y.val :=
  QInterval.mul_pair_ub_is_ub _ (x.val_mem_interval n) _ (y.val_mem_interval n)

def mul (x : ComputableℝSeq) (y : ComputableℝSeq) : ComputableℝSeq where
  lub := mul' x y
  hcl := mul'_fst_iscau
  hcu := mul'_snd_iscau
  heq' := by convert lb_ub_mul_equiv x y
  hlub n :=
    let h₀ : Real.mk _ = x.val * y.val := by stop
      apply val_uniq' (mul_lb_is_lb x y) (mul_ub_is_ub x y)
      convert lb_ub_mul_equiv x y
    h₀ ▸ QInterval.mem_mul_pair _ (x.val_mem_interval n) _ (y.val_mem_interval n)

instance instComputableZero : Zero ComputableℝSeq :=
  ⟨(0 : ℕ)⟩

instance instComputableOne : One ComputableℝSeq :=
  ⟨(1 : ℕ)⟩

instance instAdd : Add ComputableℝSeq :=
  ⟨add⟩

instance instNeg : Neg ComputableℝSeq :=
  ⟨neg⟩

instance instSub : Sub ComputableℝSeq :=
  ⟨sub⟩

instance instMul : Mul ComputableℝSeq :=
  ⟨mul⟩

instance instInh : Inhabited ComputableℝSeq :=
  ⟨0⟩

section simps

variable (x y : ComputableℝSeq)

@[simp]
theorem natCast_lb : (Nat.cast n : ComputableℝSeq).lb = n := by stop
  rfl

@[simp]
theorem natCast_ub : (Nat.cast n : ComputableℝSeq).ub = n := by stop
  rfl

@[simp]
theorem val_natCast : (Nat.cast n : ComputableℝSeq).val = n :=
  val_eq_mk_lb _ ▸ natCast_lb ▸ rfl

@[simp]
theorem intCast_lb : (Int.cast z : ComputableℝSeq).lb = z := by stop
  rfl

@[simp]
theorem intCast_ub : (Int.cast z : ComputableℝSeq).ub = z := by stop
  rfl

@[simp]
theorem val_intCast : (Int.cast z : ComputableℝSeq).val = z :=
  val_eq_mk_lb _ ▸ intCast_lb ▸ rfl

theorem ratCast_lb : (Rat.cast q : ComputableℝSeq).lb = CauSeq.const abs q := by stop
  rfl

theorem ratCast_ub : (Rat.cast q : ComputableℝSeq).ub = CauSeq.const abs q := by stop
  rfl

@[simp]
theorem val_ratCast : (Rat.cast q : ComputableℝSeq).val = q :=
  val_eq_mk_lb _ ▸ ratCast_lb ▸ rfl

@[simp]
theorem zero_lb : (0 : ComputableℝSeq).lb = 0 := by stop
  rfl

@[simp]
theorem zero_ub : (0 : ComputableℝSeq).ub = 0 := by stop
  rfl

@[simp]
theorem val_zero : (0 : ComputableℝSeq).val = 0 :=
  val_eq_mk_lb _ ▸ Real.mk_zero

@[simp]
theorem one_lb : (1 : ComputableℝSeq).lb = 1 := by stop
  rfl

@[simp]
theorem one_ub : (1 : ComputableℝSeq).ub = 1 := by stop
  rfl

@[simp]
theorem val_one : (1 : ComputableℝSeq).val = 1 :=
  val_eq_mk_lb _ ▸ Real.mk_one

@[simp]
theorem lb_add : (x + y).lb = x.lb + y.lb :=
  rfl

@[simp]
theorem ub_add : (x + y).ub = x.ub + y.ub :=
  rfl

@[simp]
theorem val_add : (x + y).val = x.val + y.val := by stop
  convert (mk_val_eq_val : (add x y).val = x.val + y.val)

@[simp]
theorem lb_neg : (-x).lb = -x.ub :=
  rfl

@[simp]
theorem ub_neg : (-x).ub = -x.lb := by stop
  rfl

@[simp]
theorem val_neg : (-x).val = -x.val := by stop
  convert (mk_val_eq_val : (neg x).val = -x.val)

@[simp]
theorem lb_sub : (x - y).lb = x.lb - y.ub := by stop
  suffices (sub x y).lb = x.lb - y.ub by stop
    convert this
  rw [sub, add, neg]
  ext
  simp [mk, lb, ub, sub_eq_add_neg]

@[simp]
theorem ub_sub : (x - y).ub = x.ub - y.lb := by stop
  suffices (sub x y).ub = x.ub - y.lb by
    convert this
  rw [sub, add, neg]
  ext
  simp [mk, lb, ub, sub_eq_add_neg]

@[simp]
theorem val_sub : (x - y).val = x.val - y.val := by stop
  suffices (sub x y).val = x.val - y.val by
    convert this
  rw [sub, add, neg, mk_val_eq_val, mk_val_eq_val]
  rfl

theorem lb_mul : (x * y).lb = ((x.lb * y.lb) ⊓ (x.ub * y.lb)) ⊓ ((x.lb * y.ub) ⊓ (x.ub * y.ub)) := by stop
  ext
  rw [← mul_lb, ← fst_mul'_eq_mul_lb]
  rfl

theorem ub_mul : (x * y).ub = ((x.lb * y.lb) ⊔ (x.ub * y.lb)) ⊔ ((x.lb * y.ub) ⊔ (x.ub * y.ub)) := by stop
  ext
  rw [← mul_ub, ← snd_mul'_eq_mul_ub]
  rfl

@[simp]
theorem val_mul : (x * y).val = x.val * y.val := by stop
  suffices (mul x y).val = x.val * y.val by
    convert this
  rw [val_def]
  exact val_uniq' (mul_lb_is_lb x y) (mul_ub_is_ub x y) (lb_ub_mul_equiv x y)

end simps

section signs

private noncomputable instance sign_aux_sound (x : ℝ) :
    Inhabited { s : SignType // s = SignType.sign x } := ⟨SignType.sign x, rfl⟩

/-- Compute the sign of x. Guaranteed to terminate if x is nonzero. If x is zero, it will
  terminate and return zero only if the lower and upper bounds become exactly zero at a finite n.
  Otherwise this becomes an infinite loop. For instance, `Real.pi - Real.pi` will never terminate.
  This ends up providing a `DecidableEq` and `DecidableLT` instance, but "in practice" this should
  only be used to prove nonequality, or check which of two inequal values is the larger -- not to
  prove equality. (The only equalities that will realistically end up being proven are the ones that
  could have been done entirely with rational numbers the whole way.) -/
partial def sign (x : ComputableℝSeq) : SignType :=
  aux 0 where
  aux (n : ℕ) : { s : SignType // s = SignType.sign x.val } :=
    let xun := x.ub n
    if h : xun < 0 then --upper bound is negative so x is negative
      ⟨SignType.neg, by rw [sign_neg]; rfl; rify at h; linarith [x.hub n] ⟩
    else
      let xln := x.lb n
      if h₂ : xln > 0 then --lower bound is posiive so x is positive
        ⟨SignType.pos, by rw [sign_pos]; rfl; rify at h₂; linarith [x.hlb n] ⟩
      else if h₃ : xln = 0 && xun = 0 then --x=0 exactly
        ⟨0, Eq.symm (by
          rw [sign_eq_zero_iff]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h₃
          rify at h₃
          linarith [x.hlb n, x.hub n]
          )⟩
      else --not determined, proceed further in sequence
        aux (n+1)

theorem sign_sound (x : ComputableℝSeq) : x.sign = SignType.sign x.val :=
  (sign.aux x 0).property

theorem sign_pos_iff (x : ComputableℝSeq) : x.sign = SignType.pos ↔ 0 < x.val := by stop
  rw [sign_sound, SignType.pos_eq_one, sign_eq_one_iff]

theorem sign_neg_iff (x : ComputableℝSeq) : x.sign = SignType.neg ↔ x.val < 0 := by stop
  rw [sign_sound, SignType.neg_eq_neg_one, sign_eq_neg_one_iff]

theorem sign_zero_iff (x : ComputableℝSeq) : x.sign = SignType.zero ↔ x.val = 0 := by stop
  rw [sign_sound, SignType.zero_eq_zero, sign_eq_zero_iff]

/-- If x is nonzero, there is eventually a point in the Cauchy sequences where either the lower
or upper bound prove this. This theorem states that this point exists. -/
noncomputable def sign_witness_term (x : ComputableℝSeq) (hnz : x.val ≠ 0) :
    { xq : ℕ × ℚ // (0:ℝ) < xq.2 ∧ xq.2 < abs x.val ∧ ∀ j ≥ xq.1, |(x.lb - x.ub) j| < xq.2} := by stop
    have hsx : abs x.val > 0 := by positivity
    have hq' : ∃(q:ℚ), (0:ℝ) < q ∧ q < abs x.val := exists_rat_btwn hsx
    obtain ⟨q, hq⟩ := Classical.indefiniteDescription _ hq'
    obtain ⟨hq₁, hq₂⟩ := hq
    obtain ⟨i, hi⟩ := Classical.indefiniteDescription _ (x.heq q (Rat.cast_pos.mp hq₁))
    use (i, q)

theorem sign_witness_term_prop (x : ComputableℝSeq) (n : ℕ) (hnz : x.val ≠ 0)
    (hub : ¬(x.ub).val n < 0) (hlb: ¬(x.lb).val n > 0) :
    n + Nat.succ 0 ≤ (x.sign_witness_term hnz).val.1 := by stop
  push_neg at hub hlb
  obtain ⟨⟨k, q⟩, ⟨h₁, h₂, h₃⟩⟩ := x.sign_witness_term hnz
  by_contra hn
  replace h₃ := h₃ n (by linarith)
  simp_rw [CauSeq.sub_apply] at h₃
  rw [abs_ite_le] at h₂ h₃
  have := x.hlb n
  have := x.hub n
  split_ifs at h₂ h₃ with h₄ h₅
  all_goals
    rify at *; linarith (config := {splitNe := true})

/-- With the proof that x≠0, we can also eventually get a sign witness: a number n such that
    either 0 < x and 0 < lb n; or that x < 0 and ub n < 0. Marking it as irreducible because
    in theory all of the info needed is in the return Subtype. -/
irreducible_def sign_witness (x : ComputableℝSeq) (hnz : x.val ≠ 0) :
    { n // (0 < x.val ∧ 0 < x.lb n) ∨ (x.val < 0 ∧ x.ub n < 0)} :=
  sign_witness_aux 0 hnz where
  sign_witness_aux (k : ℕ) (hnz : x.val ≠ 0) : { n // (0 < x.val ∧ 0 < x.lb n) ∨ (x.val < 0 ∧ x.ub n < 0)}:=
    if hub : x.ub k < 0 then
      ⟨k, Or.inr ⟨by rify at hub; linarith [x.hub k], hub⟩⟩
    else if hlb : x.lb k > 0 then
      ⟨k, Or.inl ⟨by rify at hlb; linarith [x.hlb k], hlb⟩⟩
    else
      sign_witness_aux (k+1) hnz
    termination_by
      (x.sign_witness_term hnz).val.fst - k
    decreasing_by
    · decreasing_with
      apply Nat.sub_add_lt_sub _ Nat.le.refl
      exact x.sign_witness_term_prop k hnz hub hlb

/-- With the proof that x≠0, we get a total comparison function. -/
def is_pos {x : ComputableℝSeq} (hnz : x.val ≠ 0) : Bool :=
  0 < x.lb (x.sign_witness hnz)

/-- Proof that `is_pos` correctly determines whether a nonzero computable number is positive. -/
theorem is_pos_iff (x : ComputableℝSeq) (hnz : x.val ≠ 0) : is_pos hnz ↔ 0 < x.val := by stop
  have hsw := (x.sign_witness hnz).property
  have hls := x.hlb (x.sign_witness hnz)
  have hus := x.hub (x.sign_witness hnz)
  constructor
  · intro h
    rw [is_pos, decide_eq_true_eq] at h
    cases hsw
    · tauto
    · rify at *
      linarith
  · intro h
    have := not_lt.mpr (le_of_lt h)
    rw [is_pos, decide_eq_true_eq]
    tauto

theorem neg_of_not_pos {x : ComputableℝSeq} {hnz : x.val ≠ 0} (h : ¬is_pos hnz) : x.val < 0 := by stop
  rw [is_pos_iff] at h
  linarith (config := {splitNe := true})

/- Given computable sequences for a nonzero x, drop the leading terms of both sequences
(lb and ub) until both are nonzero. This gives a new sequence that we can "safely" invert.
-/
def dropTilSigned (x : ComputableℝSeq) (hnz : x.val ≠ 0) : ComputableℝSeq :=
  let start := sign_witness x hnz
  mk (x := x.val)
  (lub := fun n ↦ x.lub (start+n))
  (hcl := (x.lb.drop start).prop)
  (hcu := (x.ub.drop start).prop)
  (hlb := fun n ↦ x.hlb (start+n))
  (hub := fun n ↦ x.hub (start+n))
  (heq := Setoid.trans (
      Setoid.trans (x.lb.drop_equiv_self start) x.heq)
      (Setoid.symm (x.ub.drop_equiv_self start)))

@[simp]
theorem val_dropTilSigned {x : ComputableℝSeq} (h : x.val ≠ 0) : (x.dropTilSigned h).val = x.val := by stop
  rw [val, val, Real.mk_eq]
  apply (lb x).drop_equiv_self

theorem dropTilSigned_nz {x : ComputableℝSeq} (h : x.val ≠ 0) : (x.dropTilSigned h).val ≠ 0 :=
  val_dropTilSigned h ▸ h

theorem sign_dropTilSigned {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    (0 < x.val ∧ 0 < (x.dropTilSigned hnz).lb 0) ∨ (x.val < 0 ∧ (x.dropTilSigned hnz).ub 0 < 0) := by stop
  have := (x.sign_witness hnz).prop
  have := lt_trichotomy x.val 0
  tauto

theorem dropTilSigned_pos {x : ComputableℝSeq} (h : x.val ≠ 0) :
    x.val > 0 ↔ (x.dropTilSigned h).lb 0 > 0 :=
  ⟨fun h' ↦ (Or.resolve_right (sign_dropTilSigned h)
    (not_and.mpr fun a _ => ( not_lt_of_gt h') a)).2,
   fun h' ↦ calc val x = _ := (val_dropTilSigned h).symm
        _ ≥ _ := (x.dropTilSigned h).hlb 0
        _ > 0 := Rat.cast_pos.2 h'⟩

theorem dropTilSigned_neg {x : ComputableℝSeq} (h : x.val ≠ 0) :
    x.val < 0 ↔ (x.dropTilSigned h).ub 0 < 0 :=
  ⟨fun h' ↦ (Or.resolve_left (sign_dropTilSigned h)
    (not_and.mpr fun a _ => ( not_lt_of_gt h') a)).2,
   fun h' ↦ calc val x = _ := (val_dropTilSigned h).symm
        _ ≤ _ := (x.dropTilSigned h).hub 0
        _ < 0 := Rat.cast_lt_zero.2 h'⟩

end signs

section safe_inv

theorem neg_LimZero_lb_of_val {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ¬x.lb.LimZero := by stop
  rw [← CauSeq.Completion.mk_eq_zero]
  rw [val_eq_mk_lb, ←Real.mk_zero, ne_eq, Real.ofCauchy.injEq] at hnz
  exact hnz

theorem neg_LimZero_ub_of_val {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ¬x.ub.LimZero := by stop
  rw [← CauSeq.Completion.mk_eq_zero]
  rw [val_eq_mk_ub, ←Real.mk_zero, ne_eq, Real.ofCauchy.injEq] at hnz
  exact hnz

theorem pos_ub_of_val {x : ComputableℝSeq} (hp : x.val > 0) : x.ub.Pos :=
  Real.mk_pos.1 (val_eq_mk_ub _ ▸ hp)

theorem pos_neg_ub_of_val {x : ComputableℝSeq} (hn : x.val < 0) : (-x.ub).Pos :=
  Real.mk_pos.1 (lb_neg _ ▸ val_eq_mk_lb _ ▸ val_neg _ ▸ Left.neg_pos_iff.mpr hn)

theorem pos_lb_of_val {x : ComputableℝSeq} (hp : x.val > 0) : x.lb.Pos :=
  Real.mk_pos.1 (val_eq_mk_lb _ ▸ hp)

theorem pos_neg_lb_of_val {x : ComputableℝSeq} (hn : x.val < 0) : (-x.lb).Pos :=
  Real.mk_pos.1 (ub_neg _ ▸ val_eq_mk_ub _ ▸ val_neg _ ▸ Left.neg_pos_iff.mpr hn)

/-- The sequence of lower bounds of 1/x. Only functions "correctly" to give lower bounds if we
   assume that hx is already `hx.dropTilSigned` (as proven in `lb_inv_correct`) -- but those
   assumptions aren't need for proving that it's Cauchy. -/
def lb_inv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : CauSeq ℚ abs :=
  if hp : is_pos hnz then --if x is positive, then reciprocals of ub's are always good lb's.
    x.ub.inv (neg_LimZero_ub_of_val hnz)
  else --x is negative, so positive values for ub don't give us any good lb's.
    let ub0 := x.ub 0 --save this first value, it acts as fallback if we get a bad ub
    ⟨fun n ↦
      let ub := x.ub n
      if ub ≥ 0 then
        ub0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        ub⁻¹, fun _ hε ↦
          have hxv : x.val < 0 := by rw [is_pos_iff] at hp; linarith (config:={splitNe:=true})
          let ⟨_, q0, Hq⟩ := pos_neg_ub_of_val hxv
          let ⟨_, K0, HK⟩ := CauSeq.abv_pos_of_not_limZero (neg_LimZero_ub_of_val hnz)
          let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abs hε K0
          let ⟨i, H⟩ := exists_forall_ge_and (exists_forall_ge_and HK (x.ub.cauchy₃ δ0)) Hq
          let ⟨⟨iK, H'⟩, _⟩ := H _ le_rfl
          ⟨i, fun j hj ↦
            have h₁ := CauSeq.neg_apply x.ub _ ▸ H _ le_rfl
            have h₁ := CauSeq.neg_apply x.ub _ ▸ H _ hj
            by
              simp only [(by linarith : ¬x.ub i ≥ 0),(by linarith : ¬x.ub j ≥ 0), ite_false]
              exact Hδ (H _ hj).1.1 iK (H' _ hj)⟩⟩

/-- Analgoous to `lb_inv` for providing upper bounds on 1/x. -/
def ub_inv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : CauSeq ℚ abs :=
  if hp : ¬is_pos hnz then --if x is positive, then reciprocals of ub's are always good lb's.
    x.lb.inv (neg_LimZero_lb_of_val hnz)
  else --x is negative, so positive values for ub don't give us any good lb's.
    let lb0 := x.lb 0 --save this first value, it acts as fallback if we get a bad ub
    ⟨fun n ↦
      let lb := x.lb n
      if lb ≤ 0 then
        lb0⁻¹ --sign is indeterminate, fall back to the starting values
      else
        lb⁻¹, fun _ hε ↦
          have hxv : x.val > 0 := by rw [is_pos_iff, not_not] at hp; linarith (config:={splitNe:=true})
          let ⟨_, q0, Hq⟩ := pos_lb_of_val hxv
          let ⟨_, K0, HK⟩ := CauSeq.abv_pos_of_not_limZero (neg_LimZero_lb_of_val hnz)
          let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abs hε K0
          let ⟨i, H⟩ := exists_forall_ge_and (exists_forall_ge_and HK (x.lb.cauchy₃ δ0)) Hq
          let ⟨⟨iK, H'⟩, _⟩ := H _ le_rfl
          ⟨i, fun j hj ↦
            have h₁ := H _ le_rfl
            have h₁ := H _ hj
            by
              simp only [(by linarith : ¬x.lb i ≤ 0),(by linarith : ¬x.lb j ≤ 0), ite_false]
              exact Hδ (H j hj).1.1 iK (H' j hj)
              ⟩⟩

/-- When applied to a `dropTilSigned`, `lb_inv` is a correct lower bound on x⁻¹. -/
theorem lb_inv_correct {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ∀n,
    (x.dropTilSigned hnz).lb_inv (dropTilSigned_nz hnz) n ≤ x.val⁻¹ := by stop
  intro n
  rw [lb_inv]
  split_ifs with hp
  · simp only [CauSeq.inv_apply, Rat.cast_inv]
    rw [is_pos_iff, val_dropTilSigned] at hp
    apply inv_anti₀ hp
    apply hub
  · have hv : val x < 0 := by rw [is_pos_iff, val_dropTilSigned] at hp; linarith (config:={splitNe:=true})
    dsimp
    split_ifs with h
    <;> simp only [Rat.cast_inv]
    <;> apply (inv_le_inv_of_neg ?_ hv).2 (hub x _)
    · exact_mod_cast (dropTilSigned_neg hnz).1 hv
    · exact_mod_cast not_le.1 h

/-- When applied to a `dropTilSigned`, `ub_inv` is a correct upper bound on x⁻¹. -/
theorem ub_inv_correct {x : ComputableℝSeq} (hnz : x.val ≠ 0) : ∀n,
    (x.dropTilSigned hnz).ub_inv (dropTilSigned_nz hnz) n ≥ x.val⁻¹ := by stop
  intro n
  rw [ub_inv]
  split_ifs with hp
  · have hv : val x > 0 := by rw [is_pos_iff, val_dropTilSigned] at hp; linarith (config:={splitNe:=true})
    dsimp
    split_ifs with h
    <;> simp only [Rat.cast_inv]
    <;> apply inv_anti₀ ?_ ((val_dropTilSigned hnz) ▸ hlb _ _)
    · exact_mod_cast (dropTilSigned_pos hnz).1 hv
    · exact_mod_cast not_le.1 h
  · simp only [CauSeq.inv_apply, Rat.cast_inv]
    replace hp := val_dropTilSigned _ ▸ neg_of_not_pos hp
    rw [ge_iff_le, inv_le_inv_of_neg]
    · exact ((val_dropTilSigned hnz) ▸ hlb _ _)
    · exact hp
    · calc _ ≤ _ := ((val_dropTilSigned hnz) ▸ hlb _ _)
      _ < _ := hp

/-- `x.lb_inv` converges to `(x.val)⁻¹`. -/
theorem lb_inv_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk (x.lb_inv hnz) = x.val⁻¹ := by
  apply Real.ext_cauchy
  rw [Real.cauchy_inv, Real.cauchy, Real.cauchy, Real.mk, val_eq_mk_ub, Real.mk,
    CauSeq.Completion.inv_mk (neg_LimZero_ub_of_val hnz), CauSeq.Completion.mk_eq, lb_inv]
  split_ifs with h
  · rfl
  · exact fun _ hε ↦
      have hxv : x.val < 0 := by
        rw [is_pos_iff] at h
        linarith (config := {splitNe := true})
      let ⟨q, q0, ⟨i, H⟩⟩ := pos_neg_ub_of_val hxv
      ⟨i, fun j hj ↦
        have : ¬x.ub j ≥ 0 := by linarith [CauSeq.neg_apply x.ub _ ▸ H _ hj]
        by simp [this, hε]⟩

/-- When applied to a `dropTilSigned`, `lb_inv` is converges to x⁻¹. -/
theorem lb_inv_signed_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk ((x.dropTilSigned hnz).lb_inv (dropTilSigned_nz hnz)) = x.val⁻¹ := by stop
  simp [lb_inv_converges (dropTilSigned_nz hnz)]

/-- `x.ub_inv` converges to `(x.val)⁻¹`. -/
theorem ub_inv_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk (x.ub_inv hnz) = x.val⁻¹ := by
  apply Real.ext_cauchy
  rw [Real.cauchy_inv, Real.cauchy, Real.cauchy, Real.mk, val_eq_mk_lb, Real.mk,
    CauSeq.Completion.inv_mk (neg_LimZero_lb_of_val hnz), CauSeq.Completion.mk_eq, ub_inv]
  split_ifs with h
  · exact fun _ hε ↦
      have hxv : x.val > 0 := by
        rw [is_pos_iff] at h
        linarith (config := {splitNe := true})
      let ⟨q, q0, ⟨i, H⟩⟩ := pos_lb_of_val hxv
      ⟨i, fun j hj ↦
        have : ¬x.lb j ≤ 0 := by linarith [H _ hj]
        by simp [this, hε]⟩
  · rfl

/-- When applied to a `dropTilSigned`, `ub_inv` is converges to x⁻¹.
TODO: version without hnz hypothesis. -/
theorem ub_inv_signed_converges {x : ComputableℝSeq} (hnz : x.val ≠ 0) :
    Real.mk ((x.dropTilSigned hnz).ub_inv (dropTilSigned_nz hnz)) = x.val⁻¹ := by stop
  simp [ub_inv_converges (dropTilSigned_nz hnz)]

/- An inverse is defined only on reals that we can prove are nonzero. If we can prove they are
 nonzero, then we can prove that at some point we learn the sign, and so can start giving actual
 upper and lower bounds. There is a separate `inv` that uses `sign` to construct the proof of
 nonzeroness by searching along the sequence (but isn't guaranteed to terminate). -/
def safe_inv (x : ComputableℝSeq) (hnz : x.val ≠ 0) : ComputableℝSeq :=
  --TODO currently this passes the sequence to lb_inv and ub_inv separately, which means we evaluate
  --things twice (and this can lead to exponential slowdown for long series of inverses). This should
  --be bundled
  let signed := x.dropTilSigned hnz
  let hnz' := val_dropTilSigned hnz ▸ hnz
  mk (x := x.val⁻¹)
  (lub := fun n ↦ ⟨⟨(signed.lb_inv hnz') n, (signed.ub_inv hnz') n⟩,
    Rat.cast_le.mp ((lb_inv_correct hnz n).trans (ub_inv_correct hnz n))⟩)
  (hcl := (signed.lb_inv hnz').2)
  (hcu := (signed.ub_inv hnz').2)
  (hlb := lb_inv_correct hnz)
  (hub := ub_inv_correct hnz)
  (heq := Real.mk_eq.1 ((lb_inv_signed_converges hnz).trans (ub_inv_signed_converges hnz).symm))

@[simp]
theorem val_safe_inv {x : ComputableℝSeq} (hnz : x.val ≠ 0) : (x.safe_inv hnz).val = x.val⁻¹ := by stop
  rw [safe_inv, mk_val_eq_val]

theorem val_safe_inv_ne_zero {x : ComputableℝSeq} (hnz : x.val ≠ 0) : (x.safe_inv hnz).val ≠ 0 := by stop
  rw [val_safe_inv, ne_eq, inv_eq_zero]
  exact hnz

/-- Subtype of sequences with nonzero values. These admit a (terminating) inverse function. -/
def nzSeq := {x : ComputableℝSeq // x.val ≠ 0}

def inv_nz : nzSeq → nzSeq :=
  fun x ↦ ⟨x.val.safe_inv x.prop, val_safe_inv_ne_zero _⟩

@[simp]
theorem val_inv_nz (x : nzSeq) : (inv_nz x).val.val = x.val.val⁻¹ :=
  val_safe_inv _

instance instNzInv : Inv nzSeq :=
  ⟨inv_nz⟩

end safe_inv

section inv

/-- Inverse of a computable real. Will terminate if the argument is nonzero, or if it is zero and the
  upper and lower bounds become exactly zero at some point. See `ComputableℝSeq.sign`. If you want
  to only call this in a way guaranteed to terminate, use `ComputableℝSeq.safe_inv`. -/
def inv : ComputableℝSeq → ComputableℝSeq :=
  fun x ↦ match h : x.sign with
  | SignType.pos => x.safe_inv (x.sign_pos_iff.1 h).ne'
  | SignType.neg => x.safe_inv (x.sign_neg_iff.1 h).ne
  | SignType.zero => 0

instance instInv : Inv ComputableℝSeq :=
  ⟨inv⟩

instance instDiv : Div ComputableℝSeq :=
  ⟨fun x y ↦ x * y⁻¹⟩

theorem inv_def (x : ComputableℝSeq) : x⁻¹ = x.inv :=
  rfl

/-- The inverse is equal to the `safe_inv`. This is an actual equality of sequences, not just equivalence. -/
theorem inv_eq_safe_inv {x : ComputableℝSeq} (hnz : x.val ≠ 0) : x⁻¹ = x.safe_inv hnz := by stop
  rw [inv_def, inv]
  split
  next h => rfl
  next h => rfl
  next h =>
    absurd h
    rw [sign_zero_iff]
    exact hnz

@[simp]
theorem val_inv (x : ComputableℝSeq) : x⁻¹.val = x.val⁻¹ := by stop
  by_cases h : x.val = 0
  · rw [h, inv_zero, inv_def, inv]
    split
    next h =>
      let _ := (x.sign_pos_iff.1 h).ne'
      contradiction
    next h =>
      let _ := (x.sign_neg_iff.1 h).ne
      contradiction
    next h => exact val_zero
  · rwa [inv_eq_safe_inv, val_safe_inv]

@[simp]
theorem val_div (x y : ComputableℝSeq) : (x / y).val = x.val / y.val := by stop
  change (x * y⁻¹).val = x.val * y.val⁻¹
  simp

end inv

section semiring --proving that computable real *sequences* form a commutative semiring

theorem add_comm (x y: ComputableℝSeq) : x + y = y + x := by stop
  ext <;> simp only [ub_add, lb_add] <;> ring_nf

theorem mul_comm (x y : ComputableℝSeq) : x * y = y * x := by stop
  ext n
  <;> simp only [lb_mul, ub_mul, mul_lb, mul_ub]
  · repeat rw [_root_.mul_comm (lb x)]
    repeat rw [_root_.mul_comm (ub x)]
    dsimp
    rw [inf_assoc, inf_assoc]
    congr 1
    rw [← inf_assoc, ← inf_assoc]
    nth_rw 2 [inf_comm]
  · repeat rw [_root_.mul_comm (lb x)]
    repeat rw [_root_.mul_comm (ub x)]
    dsimp
    rw [sup_assoc, sup_assoc]
    congr 1
    rw [← sup_assoc, ← sup_assoc]
    nth_rw 2 [sup_comm]

theorem mul_assoc (x y z : ComputableℝSeq) : (x * y) * z = x * (y * z) := by
  ext n
  · simp only [lb_mul, ub_mul, mul_lb, mul_ub]
    sorry
  · sorry

/-TODO(mul_assoc)
This theorem is annoying. When it's done, several other theorems follow too.
They're all tagged TODO(mul_assoc).

theorem mul_assoc (x y z : ComputableℝSeq) : (x * y) * z = x * (y * z) := by
  ext n
  · simp only [lb_mul, ub_mul, mul_lb, mul_ub]
    sorry
  · sorry

theorem left_distrib (x y z : ComputableℝSeq) : x * (y + z) = x * y + x * z := by
  ext n
  <;> simp only [lb_mul, ub_mul, mul_lb, mul_ub, lb_add, ub_add]
  · dsimp
    simp only [_root_.left_distrib, add_inf, inf_add, inf_assoc]
    -- congr 1
    repeat sorry
  · sorry

theorem right_distrib (x y z : ComputableℝSeq) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm z y]

-/


theorem neg_mul (x y : ComputableℝSeq) : -x * y = -(x * y) := by
  ext
  · rw [lb_neg, lb_mul, ub_mul]
    simp only [lb_neg, ub_neg, CauSeq.coe_inf, CauSeq.coe_mul, CauSeq.coe_neg, neg_mul,
      Pi.inf_apply, Pi.neg_apply, Pi.mul_apply, CauSeq.neg_apply, CauSeq.coe_sup, Pi.sup_apply, neg_sup]
    nth_rewrite 2 [inf_comm]
    nth_rewrite 3 [inf_comm]
    ring_nf
  · rw [ub_neg, lb_mul, ub_mul]
    simp only [lb_neg, ub_neg, CauSeq.coe_inf, CauSeq.coe_mul, CauSeq.coe_neg, neg_mul,
      Pi.inf_apply, Pi.neg_apply, Pi.mul_apply, CauSeq.neg_apply, CauSeq.coe_sup, Pi.sup_apply, neg_inf]
    nth_rewrite 2 [sup_comm]
    nth_rewrite 3 [sup_comm]
    ring_nf

theorem mul_neg (x y : ComputableℝSeq) : x * -y = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_eq_of_add (x y : ComputableℝSeq) (h : x + y = 0) : -x = y := by
  have hlb : ∀(x y : ComputableℝSeq), x + y = 0 → x.lb = -y.ub := by
    intro x y h
    ext n
    let ⟨h₁, h₂⟩ := ComputableℝSeq.ext_iff.mp h
    specialize h₁ n
    specialize h₂ n
    simp only [lb_add, ub_add, CauSeq.add_apply, zero_lb, zero_ub, CauSeq.zero_apply, CauSeq.neg_apply] at h₁ h₂ ⊢
    have h₃ := x.lb_le_ub n
    have h₄ := y.lb_le_ub n
    linarith (config := {splitNe := true})
  ext
  · rw [lb_neg, CauSeq.neg_apply, hlb y x (add_comm _ _ ▸ h), CauSeq.neg_apply]
  · rw [ub_neg, CauSeq.neg_apply, hlb x y h, CauSeq.neg_apply, neg_neg]

/-- Computable sequences have *most* of the properties of a field, including negation, subtraction,
  multiplication, division, IntCast all working as one would expect, with commutativity/associativity,
  involutive negation, and distributive properties ... except for a few crucial facts that a - a ≠ 0,
  a * a⁻¹ ≠ 1, and (a⁻¹)⁻¹ ≠ a. This typeclass collects all these facts together.

TODO could include mul_inv_rev, inv_eq_of_mul, intCast_ofNat, intCast_negSucc. -/
/-TODO(mul_assoc)
class CompSeqClass (G : Type u) extends
  CommSemiring G, DivInvMonoid G, HasDistribNeg G, SubtractionCommMonoid G, IntCast G, RatCast G
-/

class CompSeqClass (G : Type u) extends
  AddCommMonoid G, CommMagma G, MulZeroOneClass G, Inv G, Div G,
  HasDistribNeg G, SubtractionCommMonoid G, NatCast G, IntCast G, RatCast G

instance instSeqCompSeqClass : CompSeqClass ComputableℝSeq := by
  refine' {
            natCast := fun n => n
            intCast := fun z => z
            ratCast := fun q => q
            zero := 0
            one := 1
            mul := (· * ·)
            add := (· + ·)
            neg := (- ·)
            sub := (· - ·)
            inv := (·⁻¹)
            div := (· / ·)
            nsmul := nsmulRec
            zsmul := zsmulRec
             --inline several of the "harder" proofs that can't be done automatically
            add_comm := add_comm
            mul_comm := mul_comm
            neg_mul := neg_mul
            mul_neg := mul_neg
            neg_eq_of_add := neg_eq_of_add

            -- mul_assoc := mul_assoc
            -- npow := @npowRec _ ⟨(1 : ℕ)⟩ ⟨(· * ·)⟩
            -- left_distrib := left_distrib
            -- right_distrib := right_distrib
            -- zpow := zpowRec
            , .. }
  all_goals
    intros
    first
    | rfl
    | ext
      all_goals
        try simp only [natCast_ub, natCast_lb, Nat.cast_add, Nat.cast_one, CauSeq.add_apply, CauSeq.one_apply,
           CauSeq.zero_apply, CauSeq.neg_apply, lb_add, ub_add, one_ub, one_lb, zero_ub, zero_lb, ub_neg,
           lb_neg, neg_add_rev, neg_neg, zero_add, add_zero]
        try ring_nf
        try rfl
        try {
          rename_i a n
          simp only [lb_mul, ub_mul, zero_lb, zero_ub, mul_zero, zero_mul, one_lb, one_ub, mul_one, one_mul,
            CauSeq.inf_idem, CauSeq.sup_idem, CauSeq.zero_apply, CauSeq.coe_inf, CauSeq.coe_sup,
            Pi.sup_apply, Pi.inf_apply, sup_eq_right, inf_eq_left, lb_le_ub a n]
       }

/-TODO(mul_assoc)
@[simp]
theorem val_natpow (x : ComputableℝSeq) (n : ℕ): (x ^ n).val = x.val ^ n := by
  induction n
  · rw [pow_zero, val_one, pow_zero]
  · rename_i ih
    rw [pow_succ, pow_succ, val_mul, ih]
-/

end semiring


/-- The equivalence relation on ComputableℝSeq's given by converging to the same real value. -/
instance equiv : Setoid (ComputableℝSeq) :=
  ⟨fun f g => f.val = g.val,
    ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

theorem equiv_iff {x y : ComputableℝSeq} : x ≈ y ↔ x.val = y.val :=
  ⟨id, id⟩

end ComputableℝSeq
