import ContinuousFlexibility.Radial.TailFormCore

/-!
# Consequences of the deep-tail data

All interval masses and resistances are genuine positive integrals on compact
subintervals of the tail. The estimates here only unpack the geometric and
mass--resistance hypotheses; no operator assertion is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- The first low-mode mass interval. If the first mass interval touches the
Dirichlet entrance, its value is controlled by that boundary condition and it
does not contribute an independent low mode. -/
def tailFirstMassIndex (T : DeepTailData) : ℕ :=
  if T.node 0 = T.entrance then 1 else 0

theorem tailFirstMassIndex_le_one (T : DeepTailData) : tailFirstMassIndex T ≤ 1 := by
  unfold tailFirstMassIndex
  split <;> omega

theorem tailFirstMassIndex_eq_one {T : DeepTailData} (h : T.node 0 = T.entrance) :
    tailFirstMassIndex T = 1 := if_pos h

theorem tailFirstMassIndex_eq_zero {T : DeepTailData} (h : T.node 0 ≠ T.entrance) :
    tailFirstMassIndex T = 0 := if_neg h

theorem deepTail_contDiffOn {T : DeepTailData} (hT : DeepTailHypotheses T) :
    ContDiffOn ℝ ∞ T.p (Ico T.entrance T.endpoint) :=
  hT.2.2.2.2.2.2.2.1

theorem deepTail_pos {T : DeepTailData} (hT : DeepTailHypotheses T) :
    ∀ x ∈ Ico T.entrance T.endpoint, 0 < T.p x :=
  hT.2.2.2.2.2.2.2.2.1

theorem deepTail_node_lt_massEnd {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.node n < T.massEnd n :=
  (hT.2.2.2.2.2.2.2.2.2.2 n).1

theorem deepTail_massEnd_lt_succ_node {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.massEnd n < T.node (n + 1) :=
  (hT.2.2.2.2.2.2.2.2.2.2 n).2.1

theorem deepTail_massEnd_lt_endpoint {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.massEnd n < T.endpoint :=
  (deepTail_massEnd_lt_succ_node hT n).trans (deepTail_node_lt_endpoint hT (n + 1))

theorem deepTail_Icc_subset {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hb : b < T.endpoint) :
    Icc a b ⊆ Ico T.entrance T.endpoint :=
  fun _ hx => ⟨ha.trans hx.1, hx.2.trans_lt hb⟩

theorem deepTail_interval_integral_pos {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hab : a < b) (hb : b < T.endpoint) :
    0 < ∫ x in a..b, T.p x := by
  have hs := deepTail_Icc_subset hT ha hb
  apply intervalIntegral.integral_pos hab ((deepTail_contDiffOn hT).continuousOn.mono hs)
  · intro x hx
    exact (deepTail_pos hT x (hs ⟨hx.1.le, hx.2⟩)).le
  · exact ⟨a, ⟨le_rfl, hab.le⟩, deepTail_pos hT a (hs ⟨le_rfl, hab.le⟩)⟩

theorem deepTail_interval_resistance_pos {T : DeepTailData} (hT : DeepTailHypotheses T)
    {a b : ℝ} (ha : T.entrance ≤ a) (hab : a < b) (hb : b < T.endpoint) :
    0 < ∫ x in a..b, (T.p x)⁻¹ := by
  have hs := deepTail_Icc_subset hT ha hb
  have hi : ContinuousOn (fun x => (T.p x)⁻¹) (Icc a b) :=
    ((deepTail_contDiffOn hT).continuousOn.mono hs).inv₀
      (fun x hx => (deepTail_pos hT x (hs hx)).ne')
  apply intervalIntegral.integral_pos hab hi
  · intro x hx
    exact (inv_pos.mpr (deepTail_pos hT x (hs ⟨hx.1.le, hx.2⟩))).le
  · exact ⟨a, ⟨le_rfl, hab.le⟩,
      inv_pos.mpr (deepTail_pos hT a (hs ⟨le_rfl, hab.le⟩))⟩

theorem tailMass_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < tailMass T n :=
  deepTail_interval_integral_pos hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_massEnd hT n) (deepTail_massEnd_lt_endpoint hT n)

theorem tailInnerResistance_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < tailInnerResistance T n :=
  deepTail_interval_resistance_pos hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_massEnd hT n) (deepTail_massEnd_lt_endpoint hT n)

theorem tailGapMass_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < tailGapMass T n :=
  deepTail_interval_integral_pos hT
    ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
    (deepTail_massEnd_lt_succ_node hT n) (deepTail_node_lt_endpoint hT (n + 1))

theorem tailResistance_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < tailResistance T n :=
  deepTail_interval_resistance_pos hT
    ((deepTail_entrance_le_node hT n).trans (deepTail_node_lt_massEnd hT n).le)
    (deepTail_massEnd_lt_succ_node hT n) (deepTail_node_lt_endpoint hT (n + 1))

theorem deepTail_mass_resistance_small {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.Λ * tailMass T n * tailInnerResistance T n ≤ T.η := by
  have h := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.1
  have hnonneg := mul_nonneg
    (mul_nonneg hT.2.2.1.le (tailGapMass_pos hT n).le) (tailResistance_pos hT n).le
  linarith only [h, hnonneg]

theorem deepTail_gap_resistance_small {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : T.Λ * tailGapMass T n * tailResistance T n ≤ T.η := by
  have h := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.1
  have hnonneg := mul_nonneg
    (mul_nonneg hT.2.2.1.le (tailMass_pos hT n).le) (tailInnerResistance_pos hT n).le
  linarith only [h, hnonneg]

theorem deepTail_gap_mass_le_left {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : tailGapMass T n ≤ T.η * tailMass T n :=
  ((hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.2).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hT.2.2.2.2.1.le)

theorem deepTail_gap_mass_le_right {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : tailGapMass T n ≤ T.η * tailMass T (n + 1) :=
  ((hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.2).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hT.2.2.2.2.1.le)

/-- One resistance bound applies to either neighboring mass. -/
theorem tail_inverse_resistance_bound {K Λ μ R : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hlarge : K ≤ Λ * μ * R) :
    R⁻¹ ≤ Λ * μ / K := by
  apply (le_div_iff₀ hK).mpr
  have hdiv := (div_le_iff₀ hR).mpr hlarge
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem deepTail_inverse_resistance_left {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : (tailResistance T n)⁻¹ ≤ T.Λ * tailMass T n / T.K :=
  tail_inverse_resistance_bound (lt_trans zero_lt_one hT.2.2.2.2.2.2.1)
    (tailResistance_pos hT n) (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.1

theorem deepTail_inverse_resistance_right {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : (tailResistance T n)⁻¹ ≤ T.Λ * tailMass T (n + 1) / T.K :=
  tail_inverse_resistance_bound (lt_trans zero_lt_one hT.2.2.2.2.2.2.1)
    (tailResistance_pos hT n) (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.2.2.1

end ContinuousFlexibility.Radial
