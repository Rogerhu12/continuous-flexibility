module

public import ContinuousFlexibility.Radial.TailMassResistanceData
public import ContinuousFlexibility.Radial.TailWeightedPoincare

/-!
# The high part of the deep-tail form

A function with a zero on each mass interval obeys a uniform Poincaré
estimate. Weighted zero means will supply these zeros for the high part of
the low-mode decomposition. The separate initial resistance interval is
included with the same trace estimate as every other gap.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

def tailMassNormSq (T : DeepTailData) (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in T.node n..T.massEnd n, T.p x * u x ^ 2

def tailGapNormSq (T : DeepTailData) (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in T.massEnd n..T.node (n + 1), T.p x * u x ^ 2

def tailMassEnergy (T : DeepTailData) (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in T.node n..T.massEnd n, T.p x * deriv u x ^ 2

def tailGapEnergy (T : DeepTailData) (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in T.massEnd n..T.node (n + 1), T.p x * deriv u x ^ 2

def tailInitialNormSq (T : DeepTailData) (u : ℝ → ℝ) : ℝ :=
  ∫ x in T.entrance..T.node 0, T.p x * u x ^ 2

def tailInitialEnergy (T : DeepTailData) (u : ℝ → ℝ) : ℝ :=
  ∫ x in T.entrance..T.node 0, T.p x * deriv u x ^ 2

theorem tailMassEnergy_nonneg {T : DeepTailData} (hT : DeepTailHypotheses T)
    (u : ℝ → ℝ) (n : ℕ) : 0 ≤ tailMassEnergy T u n :=
  intervalIntegral.integral_nonneg (deepTail_node_lt_massEnd hT n).le
    (fun x hx => mul_nonneg (deepTail_pos hT x
      (deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
        (deepTail_massEnd_lt_endpoint hT n) hx)).le (sq_nonneg _))

theorem tailGapEnergy_nonneg {T : DeepTailData} (hT : DeepTailHypotheses T)
    (u : ℝ → ℝ) (n : ℕ) : 0 ≤ tailGapEnergy T u n :=
  intervalIntegral.integral_nonneg (deepTail_massEnd_lt_succ_node hT n).le
    (fun x hx => mul_nonneg (deepTail_pos hT x
      (deepTail_Icc_subset hT
        ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
        (deepTail_node_lt_endpoint hT (n + 1)) hx)).le (sq_nonneg _))

theorem tailInitialEnergy_nonneg {T : DeepTailData} (hT : DeepTailHypotheses T)
    (u : ℝ → ℝ) : 0 ≤ tailInitialEnergy T u :=
  intervalIntegral.integral_nonneg hT.2.1
    (fun x hx => mul_nonneg (deepTail_pos hT x
      (deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0) hx)).le (sq_nonneg _))

theorem tailMass_poincare_trace {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (n : ℕ)
    (hz : ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0) :
    (∀ x ∈ Icc (T.node n) (T.massEnd n),
      u x ^ 2 ≤ tailInnerResistance T n * tailMassEnergy T u n) ∧
      tailMassNormSq T u n ≤
        tailMass T n * tailInnerResistance T n * tailMassEnergy T u n := by
  obtain ⟨z, hz, huz⟩ := hz
  have hs := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_massEnd_lt_endpoint hT n)
  exact tail_poincare_of_zero (deepTail_node_lt_massEnd hT n).le
    ((deepTail_contDiffOn hT).continuousOn.mono hs)
    (fun x hx => deepTail_pos hT x (hs hx)) hu hz huz

theorem tailGap_poincare_trace {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (n : ℕ)
    (hz : ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0) :
    tailGapNormSq T u n ≤
      2 * tailGapMass T n * tailInnerResistance T n * tailMassEnergy T u n +
      2 * tailGapMass T n * tailResistance T n * tailGapEnergy T u n := by
  have hs := deepTail_Icc_subset hT
    ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
    (deepTail_node_lt_endpoint hT (n + 1))
  have htrace := (tailMass_poincare_trace hT hu n hz).1 (T.massEnd n)
    ⟨(deepTail_node_lt_massEnd hT n).le, le_rfl⟩
  simpa only [tailGapNormSq, tailGapMass, tailResistance, tailGapEnergy, mul_assoc] using
    tail_gap_mass_of_trace
    (deepTail_massEnd_lt_succ_node hT n).le
    ((deepTail_contDiffOn hT).continuousOn.mono hs)
    (fun x hx => deepTail_pos hT x (hs hx)) hu
    ⟨le_rfl, (deepTail_massEnd_lt_succ_node hT n).le⟩ htrace

private theorem tail_gap_left_trace_coefficient {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    T.Λ * tailGapMass T n * tailInnerResistance T n ≤ T.η := by
  have hΛ := hT.2.2.1
  have hη := hT.2.2.2.2.1
  have hη1 := hT.2.2.2.2.2.1
  calc
    _ ≤ T.Λ * (T.η * tailMass T n) * tailInnerResistance T n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (deepTail_gap_mass_le_left hT n) hΛ.le)
        (tailInnerResistance_pos hT n).le
    _ = T.η * (T.Λ * tailMass T n * tailInnerResistance T n) := by ring
    _ ≤ T.η * T.η :=
      mul_le_mul_of_nonneg_left (deepTail_mass_resistance_small hT n) hη.le
    _ ≤ T.η := by nlinarith

/-- Uniform estimate on one mass interval and its following gap. -/
theorem tail_cell_high_energy_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (n : ℕ)
    (hz : ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0) :
    T.Λ * (tailMassNormSq T u n + tailGapNormSq T u n) ≤
      3 * T.η * (tailMassEnergy T u n + tailGapEnergy T u n) := by
  have hΛ := hT.2.2.1
  have hη := hT.2.2.2.2.1
  have hEI := tailMassEnergy_nonneg hT u n
  have hEJ := tailGapEnergy_nonneg hT u n
  have hM : T.Λ * tailMassNormSq T u n ≤ T.η * tailMassEnergy T u n := by
    calc
      _ ≤ T.Λ * (tailMass T n * tailInnerResistance T n * tailMassEnergy T u n) :=
        mul_le_mul_of_nonneg_left (tailMass_poincare_trace hT hu n hz).2 hΛ.le
      _ = (T.Λ * tailMass T n * tailInnerResistance T n) * tailMassEnergy T u n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (deepTail_mass_resistance_small hT n) hEI
  have hJ : T.Λ * tailGapNormSq T u n ≤
      2 * T.η * tailMassEnergy T u n + 2 * T.η * tailGapEnergy T u n := by
    calc
      _ ≤ T.Λ * (2 * tailGapMass T n * tailInnerResistance T n * tailMassEnergy T u n +
          2 * tailGapMass T n * tailResistance T n * tailGapEnergy T u n) :=
        mul_le_mul_of_nonneg_left (tailGap_poincare_trace hT hu n hz) hΛ.le
      _ = 2 * (T.Λ * tailGapMass T n * tailInnerResistance T n) * tailMassEnergy T u n +
          2 * (T.Λ * tailGapMass T n * tailResistance T n) * tailGapEnergy T u n := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (tail_gap_left_trace_coefficient hT n) (by norm_num)) hEI)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (deepTail_gap_resistance_small hT n) (by norm_num)) hEJ)
  nlinarith [mul_nonneg hη.le hEJ]

theorem tail_initial_high_energy_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (hz : ∃ z ∈ Icc (T.node 0) (T.massEnd 0), u z = 0) :
    T.Λ * tailInitialNormSq T u ≤
      2 * T.η * (tailInitialEnergy T u + tailMassEnergy T u 0) := by
  have hΛ := hT.2.2.1
  have hη := hT.2.2.2.2.1
  have hη1 := hT.2.2.2.2.2.1
  have hEI := tailMassEnergy_nonneg hT u 0
  have hE0 := tailInitialEnergy_nonneg hT u
  rcases hT.2.2.2.1 with he | ⟨hstart, hsmall, hmass, _⟩
  · simp only [tailInitialNormSq, tailInitialEnergy, he, intervalIntegral.integral_same,
      mul_zero, zero_add]
    positivity
  · have hs := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have htrace := (tailMass_poincare_trace hT hu 0 hz).1 (T.node 0)
      ⟨le_rfl, (deepTail_node_lt_massEnd hT 0).le⟩
    have hbound := tail_gap_mass_of_trace hstart.le
      ((deepTail_contDiffOn hT).continuousOn.mono hs)
      (fun x hx => deepTail_pos hT x (hs hx)) hu ⟨hstart.le, le_rfl⟩ htrace
    have hcoef : T.Λ * tailInitialGapMass T * tailInnerResistance T 0 ≤ T.η := by
      calc
        _ ≤ T.Λ * (T.η * tailMass T 0) * tailInnerResistance T 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hΛ.le)
            (tailInnerResistance_pos hT 0).le
        _ = T.η * (T.Λ * tailMass T 0 * tailInnerResistance T 0) := by ring
        _ ≤ T.η * T.η :=
          mul_le_mul_of_nonneg_left (deepTail_mass_resistance_small hT 0) hη.le
        _ ≤ T.η := by nlinarith
    calc
      _ ≤ T.Λ * (2 * tailInitialGapMass T *
          (tailInnerResistance T 0 * tailMassEnergy T u 0) +
          2 * tailInitialGapMass T * tailInitialResistance T * tailInitialEnergy T u) :=
        mul_le_mul_of_nonneg_left hbound hΛ.le
      _ = 2 * (T.Λ * tailInitialGapMass T * tailInnerResistance T 0) * tailMassEnergy T u 0 +
          2 * (T.Λ * tailInitialGapMass T * tailInitialResistance T) * tailInitialEnergy T u := by ring
      _ ≤ 2 * T.η * tailMassEnergy T u 0 + 2 * T.η * tailInitialEnergy T u :=
        add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hEI)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsmall (by norm_num)) hE0)
      _ = _ := by ring

/-- Exact finite partition into the initial edge, mass intervals, and gaps. -/
theorem tail_integral_partition {T : DeepTailData} (hT : DeepTailHypotheses T)
    {f : ℝ → ℝ} (N : ℕ)
    (hf : ContinuousOn f (Icc T.entrance (T.node N))) :
    (∫ x in T.entrance..T.node N, f x) =
      (∫ x in T.entrance..T.node 0, f x) +
        ∑ n ∈ Finset.range N,
          ((∫ x in T.node n..T.massEnd n, f x) +
            ∫ x in T.massEnd n..T.node (n + 1), f x) := by
  have hmono := (deepTail_node_strictMono hT).monotone
  have hint (n : ℕ) (hn : n < N) :
      IntervalIntegrable f volume (T.node n) (T.node (n + 1)) :=
    (hf.mono (Icc_subset_Icc (deepTail_entrance_le_node hT n)
      (hmono (Nat.succ_le_iff.mpr hn)))).intervalIntegrable_of_Icc
      (hmono (Nat.le_succ n))
  have hsplit (n : ℕ) (hn : n < N) :
      (∫ x in T.node n..T.massEnd n, f x) +
        (∫ x in T.massEnd n..T.node (n + 1), f x) =
          ∫ x in T.node n..T.node (n + 1), f x := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact (hf.mono (Icc_subset_Icc (deepTail_entrance_le_node hT n)
        ((deepTail_massEnd_lt_succ_node hT n).le.trans
          (hmono (Nat.succ_le_iff.mpr hn))))).intervalIntegrable_of_Icc
        (deepTail_node_lt_massEnd hT n).le
    · exact (hf.mono (Icc_subset_Icc
        ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
        (hmono (Nat.succ_le_iff.mpr hn)))).intervalIntegrable_of_Icc
        (deepTail_massEnd_lt_succ_node hT n).le
  have hsum : (∑ n ∈ Finset.range N,
      ((∫ x in T.node n..T.massEnd n, f x) +
        ∫ x in T.massEnd n..T.node (n + 1), f x)) =
      ∫ x in T.node 0..T.node N, f x := by
    calc
      _ = ∑ n ∈ Finset.range N, ∫ x in T.node n..T.node (n + 1), f x :=
        Finset.sum_congr rfl (fun n hn => hsplit n (Finset.mem_range.mp hn))
      _ = _ := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hsum]
  symm
  apply intervalIntegral.integral_add_adjacent_intervals
  · exact (hf.mono (Icc_subset_Icc le_rfl (hmono (Nat.zero_le N)))).intervalIntegrable_of_Icc
      hT.2.1
  · exact (hf.mono (Icc_subset_Icc hT.2.1 le_rfl)).intervalIntegrable_of_Icc
      (hmono (Nat.zero_le N))

/-- The complete high-mode bound on any finite Dirichlet truncation. Its
constant is independent of the number of mass intervals. -/
theorem tail_finite_high_energy_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {N : ℕ} (hN : 0 < N)
    (hz : ∀ n < N, ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0) :
    T.Λ * (∫ x in T.entrance..T.node N, T.p x * u x ^ 2) ≤
      5 * T.η * ∫ x in T.entrance..T.node N, T.p x * deriv u x ^ 2 := by
  have hη := hT.2.2.2.2.1
  have hs := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT N)
  have hp : ContinuousOn T.p (Icc T.entrance (T.node N)) :=
    (deepTail_contDiffOn hT).continuousOn.mono hs
  have hd : Continuous (deriv u) := (contDiff_one_iff_deriv.mp hu).2
  rw [tail_integral_partition (f := fun x => T.p x * u x ^ 2) hT N
      (hp.mul (hu.continuous.pow 2).continuousOn),
    tail_integral_partition (f := fun x => T.p x * deriv u x ^ 2) hT N
      (hp.mul (hd.pow 2).continuousOn)]
  change T.Λ * (tailInitialNormSq T u +
      ∑ n ∈ Finset.range N, (tailMassNormSq T u n + tailGapNormSq T u n)) ≤
    5 * T.η * (tailInitialEnergy T u +
      ∑ n ∈ Finset.range N, (tailMassEnergy T u n + tailGapEnergy T u n))
  have hsum : T.Λ * (∑ n ∈ Finset.range N,
      (tailMassNormSq T u n + tailGapNormSq T u n)) ≤
      3 * T.η * ∑ n ∈ Finset.range N, (tailMassEnergy T u n + tailGapEnergy T u n) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn =>
      tail_cell_high_energy_bound hT hu n (hz n (Finset.mem_range.mp hn))
  have hfirst : tailMassEnergy T u 0 ≤
      ∑ n ∈ Finset.range N, (tailMassEnergy T u n + tailGapEnergy T u n) := by
    calc
      _ ≤ tailMassEnergy T u 0 + tailGapEnergy T u 0 :=
        le_add_of_nonneg_right (tailGapEnergy_nonneg hT u 0)
      _ ≤ _ := Finset.single_le_sum
        (fun n _ => add_nonneg (tailMassEnergy_nonneg hT u n) (tailGapEnergy_nonneg hT u n))
        (Finset.mem_range.mpr hN)
  have hinitial := tail_initial_high_energy_bound hT hu (hz 0 hN)
  have hnonneg := tailInitialEnergy_nonneg hT u
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη.le)
  nlinarith [mul_nonneg hη.le hnonneg]

end ContinuousFlexibility.Radial
