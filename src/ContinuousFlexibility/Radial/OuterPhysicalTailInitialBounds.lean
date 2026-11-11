import ContinuousFlexibility.Radial.OuterTailInitialBounds
import ContinuousFlexibility.Radial.OuterPhysicalTailBasis

/-!
# Initial-edge estimates for the same actual physical basis

The reciprocal entrance normalizations cancel in the initial Green
product. The full initial interval is controlled by its actual Poisson
matrix, so it can use the first edge's label in localized estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

namespace MorsePhysicalTailBasis

variable {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
  {entrance η K : ℝ}

/-- The unit Wronskian cancels both entrance normalization factors. -/
theorem log_entry_abs_product
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logQFlux T.entrance| * |F.logP T.entrance| = 1 := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have h := F.log_wronskian T.entrance ⟨le_rfl, hT.1⟩
  rw [F.Q_log_entry, zero_mul, sub_zero] at h
  rw [← abs_mul, h, abs_one]

theorem logQ_initial_node_le_resistance
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logQ (T.node 0)| ≤ |F.logQFlux T.entrance| * tailInitialResistance T :=
  outer_tail_initial_dirichlet_value_le_resistance hT F.Q_log_system F.Q_log_entry

/-- The natural first-node value never exceeds its entrance value. -/
theorem logP_initial_node_le_entry
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hK : 32 ≤ K) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    |F.logP (T.node 0)| ≤ |F.logP T.entrance| := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  rcases hT.2.2.2.1 with heq | hgap
  · rw [heq]
  · have hR := tailInitialResistance_pos hT hgap.1
    have hden : 0 < T.Λ * tailMass T 0 * tailInitialResistance T :=
      mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT 0)) hR
    have hratio : 8 / (T.Λ * tailMass T 0 * tailInitialResistance T) ≤ 1 := by
      apply (div_le_one hden).mpr
      have hK' : (32 : ℝ) ≤ T.K := hK
      exact (show (8 : ℝ) ≤ T.K by linarith only [hK']).trans hgap.2.2.2
    exact (F.P_initial_node_bound hgap.1).trans
      ((mul_le_mul_of_nonneg_right hratio (abs_nonneg _)).trans_eq (one_mul _))

theorem logQ_initial_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) {x : ℝ}
    (hx : x ∈ Icc
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      ((morsePhysicalDeepTail M D right j start entrance η K).node 0)) :
    |F.logQ x| ≤ 2 *
      |F.logQ ((morsePhysicalDeepTail M D right j start entrance η K).node 0)| := by
  have h := outer_tail_initial_state_bound hT
    (hη.trans (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2)) F.Q_log_system hx
  simpa only [F.Q_log_entry, abs_zero, zero_add] using h

theorem logP_initial_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) {x : ℝ}
    (hx : x ∈ Icc
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      ((morsePhysicalDeepTail M D right j start entrance η K).node 0)) :
    |F.logP x| ≤ 4 *
      |F.logP (morsePhysicalDeepTail M D right j start entrance η K).entrance| := by
  have h := outer_tail_initial_state_bound hT
    (hη.trans (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2)) F.P_log_system hx
  have hfirst := F.logP_initial_node_le_entry hT hK
  nlinarith only [h, hfirst]

/-- The same pair has a uniformly bounded initial diagonal product.
The bound is independent of the entrance gauge and all physical scales. -/
theorem log_initial_product_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K)) :
    let T := morsePhysicalDeepTail M D right j start entrance η K
    tailMass T 0 * |F.logP (T.node 0) * F.logQ (T.node 0)| ≤ 8 / T.Λ := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  rcases hT.2.2.2.1 with heq | hgap
  · rw [heq, F.Q_log_entry, mul_zero, abs_zero, mul_zero]
    exact (div_pos (by norm_num) hT.2.2.1).le
  · have hΛ : 0 < T.Λ := hT.2.2.1
    have hμ : 0 < tailMass T 0 := tailMass_pos hT 0
    have hR : 0 < tailInitialResistance T := tailInitialResistance_pos hT hgap.1
    have hp := F.P_initial_node_bound hgap.1
    have hq := F.logQ_initial_node_le_resistance hT
    have hprod := mul_le_mul hp hq (abs_nonneg _)
      (mul_nonneg (div_nonneg (by norm_num) (by positivity)) (abs_nonneg _))
    calc
      _ = tailMass T 0 * (|F.logP (T.node 0)| * |F.logQ (T.node 0)|) := by
        rw [abs_mul]
      _ ≤ tailMass T 0 *
          ((8 / (T.Λ * tailMass T 0 * tailInitialResistance T) * |F.logP T.entrance|) *
            (|F.logQFlux T.entrance| * tailInitialResistance T)) :=
        mul_le_mul_of_nonneg_left hprod hμ.le
      _ = (8 / T.Λ) * (|F.logQFlux T.entrance| * |F.logP T.entrance|) := by
        field_simp [hΛ.ne', hμ.ne', hR.ne'] <;> ring
      _ = 8 / T.Λ := by rw [F.log_entry_abs_product hT, mul_one]

/-- Both points in the actual initial interval cost at most eight times
its resistance, for the same unit-Wronskian logarithmic kernel. -/
theorem log_initial_kernel_bound
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) {x y : ℝ}
    (hx : x ∈ Icc
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      ((morsePhysicalDeepTail M D right j start entrance η K).node 0))
    (hy : y ∈ Icc
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      ((morsePhysicalDeepTail M D right j start entrance η K).node 0)) :
    |F.logQ (min x y) * F.logP (max x y)| ≤
      8 * tailInitialResistance (morsePhysicalDeepTail M D right j start entrance η K) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  have hmin : min x y ∈ Icc T.entrance (T.node 0) :=
    ⟨le_min hx.1 hy.1, (min_le_left _ _).trans hx.2⟩
  have hmax : max x y ∈ Icc T.entrance (T.node 0) :=
    ⟨hx.1.trans (le_max_left _ _), max_le hx.2 hy.2⟩
  have hq0 := F.logQ_initial_node_le_resistance hT
  have hq := (F.logQ_initial_bound hT hη hmin).trans
    (mul_le_mul_of_nonneg_left hq0 (by norm_num : (0 : ℝ) ≤ 2))
  have hp := F.logP_initial_bound hT hη hK hmax
  have hqnonneg : 0 ≤ 2 * (|F.logQFlux T.entrance| * tailInitialResistance T) :=
    mul_nonneg (by norm_num) ((abs_nonneg _).trans hq0)
  calc
    _ = |F.logQ (min x y)| * |F.logP (max x y)| := abs_mul _ _
    _ ≤ (2 * (|F.logQFlux T.entrance| * tailInitialResistance T)) *
        (4 * |F.logP T.entrance|) :=
      mul_le_mul hq hp (abs_nonneg _) hqnonneg
    _ = (8 * tailInitialResistance T) *
        (|F.logQFlux T.entrance| * |F.logP T.entrance|) := by ring
    _ = _ := by rw [F.log_entry_abs_product hT, mul_one]

end MorsePhysicalTailBasis

end ContinuousFlexibility.Radial

