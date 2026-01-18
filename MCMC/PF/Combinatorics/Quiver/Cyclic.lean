import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq

namespace Quiver
variable {V : Type*} [Quiver V]

/-!
# Periodicity and Aperiodicity in Quivers

This section defines the concepts of periodicity, the index of imprimitivity,
and aperiodicity for strongly connected quivers, which are essential for understanding
the cyclic structure of irreducible matrices.
-/

-- Definition for the set of lengths of cycles at a vertex i.
-- We require positive length for cycles relevant to periodicity.
def CycleLengths (i : V) : Set ℕ := {k | k > 0 ∧ ∃ p : Path i i, p.length = k}

/-- The set of common divisors of all cycle lengths at `i`. (If there are no cycles this is all
  of `ℕ`, so the least element is `0`.) -/
def commonDivisorsSet (i : V) : Set ℕ := {d | ∀ k ∈ CycleLengths i, d ∣ k}

lemma one_mem_commonDivisorsSet (i : V) :
  1 ∈ commonDivisorsSet i := by
  intro k hk; exact one_dvd _

lemma commonDivisorsSet_nonempty (i : V) : (commonDivisorsSet i).Nonempty :=
  ⟨1, one_mem_commonDivisorsSet i⟩

/-- The period of a vertex `i`: the least common divisor of all cycle lengths at `i`.

If there are no cycles, this is `0` (since then `commonDivisorsSet i = Set.univ`). -/
noncomputable def period (i : V) : ℕ :=
by
  classical
  letI : DecidablePred fun d : ℕ => d ∈ commonDivisorsSet i := Classical.decPred _
  exact Nat.find (commonDivisorsSet_nonempty (i := i))

/-- `period i` is the least element of the set of common divisors of all cycle lengths at `i`. -/
lemma period_min (i : V) :
    period i ∈ commonDivisorsSet i ∧
      ∀ m ∈ commonDivisorsSet i, period i ≤ m := by
  classical
  refine ⟨?mem, ?least⟩
  · simpa [period] using (Nat.find_spec (commonDivisorsSet_nonempty (i := i)))
  · intro m hm
    simpa [period] using (Nat.find_min' (commonDivisorsSet_nonempty (i := i)) hm)

/-- Basic characterization of `period`: divisibility plus minimality.
    TODO: it may be needed a more rigorous characterization-/
lemma period_spec (i : V) :
  (∀ k ∈ CycleLengths i, period i ∣ k) ∧
  (∀ m, (∀ k ∈ CycleLengths i, m ∣ k) → period i ≤ m) := by
  classical
  have h := period_min i
  refine ⟨?div, ?min⟩
  · intro k hk
    exact h.1 k hk
  · intro m hm
    exact h.2 m hm

lemma period_mem_commonDivisorsSet (i : V) :
    period i ∈ commonDivisorsSet i :=
  (period_min i).1

lemma period_le_of_commonDivisor (i : V) {m : ℕ}
    (hm : ∀ k ∈ CycleLengths i, m ∣ k) :
    period i ≤ m :=
  (period_spec i).2 _ hm

lemma divides_cycle_length {i : V} {k : ℕ}
    (hk : k ∈ CycleLengths i) :
    period i ∣ k :=
  (period_spec i).1 _ hk

-- The period divides every cycle length (corollary of `period_spec`).
lemma period_divides_cycle_lengths (i : V) :
  ∀ {k}, k ∈ CycleLengths i → period i ∣ k := by
  intro k hk
  exact (period_spec i).1 k hk

-- If the set of cycle lengths is non-empty, the period is positive.
lemma period_pos_of_nonempty_cycles (i : V) (h_nonempty : (CycleLengths i).Nonempty) :
    period i > 0 := by
  rcases h_nonempty with ⟨k, hk⟩
  have hk_pos : k > 0 := hk.1
  have hdiv : period i ∣ k := (period_spec i).1 k hk
  have hk_ne_zero : k ≠ 0 := (Nat.pos_iff_ne_zero.mp hk_pos)
  rcases hdiv with ⟨t, ht⟩
  have hper_ne_zero : period i ≠ 0 := by
    intro hzero
    have : k = 0 := by simpa [hzero] using ht
    exact hk_ne_zero this
  exact Nat.pos_of_ne_zero hper_ne_zero

/--
**Theorem: In a strongly connected quiver, the period is the same for all vertices**.
-/
theorem period_constant_of_strongly_connected (h_sc : Quiver.IsSStronglyConnected V) :
  ∀ i j : V, period i = period j := by
  intro i j
  classical
  rcases h_sc i j with ⟨p, hp_pos⟩
  rcases h_sc j i with ⟨q, hq_pos⟩
  have h_div_j : ∀ k ∈ CycleLengths j, period i ∣ k := by
    intro k hk
    rcases hk with ⟨hk_pos, ⟨c, hc_len⟩⟩
    let t : ℕ := (p.comp q).length
    have ht_pos : 0 < t := by
      have : p.length ≤ (p.comp q).length := by
        simp [Path.length_comp]
      exact lt_of_lt_of_le hp_pos this
    have ht_mem : t ∈ CycleLengths i := by
      refine ⟨ht_pos, ?_⟩
      refine ⟨p.comp q, rfl⟩
    have h_dvd_t : period i ∣ t := (period_spec i).1 _ ht_mem
    let t' : ℕ := ((p.comp c).comp q).length
    have ht'_pos : 0 < t' := by
      have hle1 : k ≤ k + q.length := Nat.le_add_right _ _
      have hle2 : k + q.length ≤ p.length + (k + q.length) := Nat.le_add_left _ _
      have hle : k ≤ p.length + (k + q.length) := le_trans hle1 hle2
      have : p.length + k + q.length = t' := by
        simp [t', Path.length_comp, hc_len, Nat.add_assoc, Nat.add_comm]
      have hle' : k ≤ t' := by grind
      exact lt_of_lt_of_le hk_pos hle'
    have ht'_mem : t' ∈ CycleLengths i := by
      refine ⟨ht'_pos, ?_⟩
      refine ⟨(p.comp c).comp q, rfl⟩
    have h_dvd_t' : period i ∣ t' := (period_spec i).1 _ ht'_mem
    have : period i ∣ t + k := by
      have h_eq : t' = t + k := by
        simp [t, t', Path.length_comp, hc_len, Nat.add_assoc, Nat.add_comm]
      simpa [h_eq]
        using h_dvd_t'
    have hk_div : period i ∣ k := (Nat.dvd_add_right h_dvd_t).1 this
    exact hk_div
  have h_le_ji : period j ≤ period i := period_le_of_commonDivisor j h_div_j
  have h_div_i : ∀ k ∈ CycleLengths i, period j ∣ k := by
    intro k hk
    rcases hk with ⟨hk_pos, ⟨c, hc_len⟩⟩
    let t : ℕ := (q.comp p).length
    have ht_pos : 0 < t := by
      have : q.length ≤ (q.comp p).length := by
        simp [Path.length_comp]
      exact lt_of_lt_of_le hq_pos this
    have ht_mem : t ∈ CycleLengths j := by
      refine ⟨ht_pos, ?_⟩
      refine ⟨q.comp p, rfl⟩
    have h_dvd_t : period j ∣ t := (period_spec j).1 _ ht_mem
    let t' : ℕ := ((q.comp c).comp p).length
    have ht'_pos : 0 < t' := by
      have hle1 : k ≤ k + p.length := Nat.le_add_right _ _
      have hle2 : k + p.length ≤ q.length + (k + p.length) := Nat.le_add_left _ _
      have hle : k ≤ q.length + (k + p.length) := le_trans hle1 hle2
      have : q.length + k + p.length = t' := by
        simp [t', Path.length_comp, hc_len, Nat.add_comm, Nat.add_left_comm]
      have hle' : k ≤ t' := by grind
      exact lt_of_lt_of_le hk_pos hle'
    have ht'_mem : t' ∈ CycleLengths j := by
      refine ⟨ht'_pos, ?_⟩
      refine ⟨(q.comp c).comp p, rfl⟩
    have h_dvd_t' : period j ∣ t' := (period_spec j).1 _ ht'_mem
    have : period j ∣ t + k := by
      have h_eq : t' = t + k := by
        simp [t, t', Path.length_comp, hc_len, Nat.add_comm, Nat.add_left_comm]
      simpa [h_eq] using h_dvd_t'
    exact (Nat.dvd_add_right h_dvd_t).1 this
  have h_le_ij : period i ≤ period j := period_le_of_commonDivisor i h_div_i
  exact le_antisymm h_le_ij h_le_ji

/-- The index of imprimitivity (h) of a strongly connected quiver,
    defined as the common period of its vertices. Requires Fintype and Nonempty
    to select an arbitrary vertex. -/
noncomputable def index_of_imprimitivity [Fintype V] [Nonempty V] (G : Quiver V) : ℕ := by
  classical
  letI : Quiver V := G
  exact period (Classical.arbitrary V)

/-- A strongly connected quiver is aperiodic if its index of imprimitivity is 1. -/
def IsAperiodic [Fintype V] [Nonempty V] (G : Quiver V) : Prop :=
  index_of_imprimitivity G = 1

/-! # Cyclic Structure and Frobenius Normal Form -/

/-- A cyclic partition of the vertices with period h.
    The partition is represented by a map from V to Fin h.
    Edges only go from one class to the next one cyclically.
    We define the successor within `Fin h` by modular addition of 1 (staying in `Fin h`). -/
def IsCyclicPartition {h : ℕ} (h_pos : h > 0) (partition : V → Fin h) : Prop :=
  let succMod : Fin h → Fin h := fun x => ⟨(x.val + 1) % h, Nat.mod_lt _ h_pos⟩
  ∀ i j : V, Nonempty (i ⟶ j) → partition j = succMod (partition i)

/-- If the right factor of a composed path has positive length, the composed cycle at `i`
belongs to `CycleLengths i`. -/
lemma mem_CycleLengths_of_comp_right {i v : V}
    (p : Path i v) (s : Path v i) (hs_pos : 0 < s.length) :
    (p.comp s).length ∈ CycleLengths i := by
  have hpos : 0 < (p.comp s).length := by
    -- 0 < s.length ≤ p.length + s.length = (p.comp s).length
    have hle : s.length ≤ p.length + s.length := by
      have := Nat.le_add_left s.length p.length
      simp
    exact lt_of_lt_of_le hs_pos (by simp [Path.length_comp])
  exact ⟨hpos, ⟨p.comp s, rfl⟩⟩

/-- Variant: if we first extend a path by a single edge using `cons` and then compose on the right
with a positive-length path back to the base, we still get a cycle length in `CycleLengths`. -/
lemma mem_CycleLengths_of_cons_comp_right {i v w : V}
    (p : Path i v) (e : v ⟶ w) (s : Path w i) (hs_pos : 0 < s.length) :
    (((p.cons e).comp s).length) ∈ CycleLengths i :=
  mem_CycleLengths_of_comp_right (p := p.cons e) (s := s) hs_pos

/--
Theorem: A strongly connected quiver with index of imprimitivity h admits a cyclic partition.
-/
theorem exists_cyclic_partition_of_strongly_connected [Fintype V] [Nonempty V]
    (h_sc : Quiver.IsSStronglyConnected V) :
    ∀ (h_pos : index_of_imprimitivity (inferInstance : Quiver V) > 0),
      ∃ partition : V → Fin (index_of_imprimitivity (inferInstance : Quiver V)),
        IsCyclicPartition h_pos partition := by
  intro h_pos
  classical
  let h := index_of_imprimitivity (inferInstance : Quiver V)
  change ∃ partition : V → Fin h, IsCyclicPartition h_pos partition
  -- we fix a base vertex i₀ compatible with the definition of `index_of_imprimitivity`
  let i0 : V := Classical.arbitrary V
  -- for each vertex, we choose a positive-length path from i₀ to it
  have hpaths : ∀ v : V, ∃ p : Path i0 v, 0 < p.length := fun v => h_sc i0 v
  let chosen : ∀ v : V, { p : Path i0 v // 0 < p.length } :=
    fun v => ⟨Classical.choose (hpaths v), Classical.choose_spec (hpaths v)⟩
  let P : ∀ v : V, Path i0 v := fun v => (chosen v).1
  have hPpos : ∀ v : V, (P v).length > 0 := fun v => (chosen v).2
  -- we define the partition by taking path lengths modulo h
  let partition : V → Fin h := fun v => ⟨(P v).length % h, Nat.mod_lt _ h_pos⟩
  refine ⟨partition, ?_⟩
  dsimp [IsCyclicPartition]
  intro i j hij
  rcases hij with ⟨e⟩
  obtain ⟨s, hs_pos⟩ := h_sc j i0
  have hc1_mem : ((P j).comp s).length ∈ CycleLengths i0 :=
    mem_CycleLengths_of_comp_right (p := P j) (s := s) hs_pos
  have hc2_mem : (((P i).cons e).comp s).length ∈ CycleLengths i0 :=
    mem_CycleLengths_of_cons_comp_right (p := P i) (e := e) (s := s) hs_pos
  have hdvd1 : h ∣ ((P j).comp s).length := by
    have : period i0 ∣ ((P j).comp s).length :=
      (divides_cycle_length (i := i0) (k := ((P j).comp s).length)) hc1_mem
    simpa [index_of_imprimitivity, i0]
  have hdvd2 : h ∣ (((P i).cons e).comp s).length := by
    have : period i0 ∣ (((P i).cons e).comp s).length :=
      (divides_cycle_length (i := i0) (k := (((P i).cons e).comp s).length)) hc2_mem
    simpa [index_of_imprimitivity, i0]
  have len_c1 :
      ((P j).comp s).length = (P j).length + s.length := by
    simp [Path.length_comp]
  have len_c2 :
      (((P i).cons e).comp s).length = (P i).length + 1 + s.length := by
    simp [Path.length_comp, Path.length_cons, Nat.add_assoc]
  have hsum_congr :
      Nat.ModEq h ((P j).length + s.length) ((P i).length + 1 + s.length) := by
    have h1 : Nat.ModEq h ((P j).length + s.length) 0 := by
      have : ((P j).length + s.length) % h = 0 := by
        simpa [len_c1] using Nat.mod_eq_zero_of_dvd hdvd1
      simpa [Nat.ModEq] using this
    have h2 : Nat.ModEq h ((P i).length + 1 + s.length) 0 := by
      have : ((P i).length + 1 + s.length) % h = 0 := by
        simpa [len_c2] using Nat.mod_eq_zero_of_dvd hdvd2
      simpa [Nat.ModEq] using this
    exact h1.trans h2.symm
  have h_congr :
      Nat.ModEq h (P j).length ((P i).length + 1) := by
    dsimp [Nat.add_assoc]
    exact Nat.ModEq.add_right_cancel' s.length hsum_congr
  let succMod : Fin h → Fin h := fun x => ⟨(x.val + 1) % h, Nat.mod_lt _ h_pos⟩
  apply Fin.ext
  simp [partition]
  calc
    (P j).length % h
        = ((P i).length + 1) % h := by
          simpa [Nat.ModEq] using h_congr
    _   = ((P i).length % h + 1 % h) % h := by
          rw [Nat.add_mod]
    _   = ((P i).length % h + 1) % h := by
          by_cases h1 : h = 1
          all_goals aesop

end Quiver
