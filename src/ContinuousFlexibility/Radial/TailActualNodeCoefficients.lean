import ContinuousFlexibility.Radial.TailActualPoissonEdge
import ContinuousFlexibility.Radial.TailDeepEdgeBounds
import ContinuousFlexibility.Radial.TailEdgeFluxBounds

/-!
# The actual interior tridiagonal coefficients

The coefficients below use the single Poisson pair chosen on each actual
edge. The interior diagonal is indexed by the preceding edge: its index `n`
belongs to the node `n + 1`. No entrance condition is imposed by this file.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

/-- The coupling supplied by the canonical actual Poisson pair. -/
def tailActualNodeCoupling (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ :=
  tailActualEdgeCoupling T hT n (tailActualEdgePoisson T hT n)

/-- The diagonal at the interior node `n + 1`, with its actual two neighboring edges. -/
def tailActualInteriorDiagonal (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ :=
  -tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) true -
    tailActualEdgeDiagonal T hT (n + 1) (tailActualEdgePoisson T hT (n + 1)) false

theorem tailActualNodeCoupling_lower {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    1 / tailActualEdgeLength T n ≤ tailActualNodeCoupling T hT n := by
  have h := (tailEdge_flux_coupling_bounds (tailActualEdgeLength_pos hT n)
    (tailActualEdgePotential_nonneg hT n) (tailActualEdgeDiagonalSize_lt_one hT n)
    ((tailActualEdgePoisson_spec hT n).differentiable true).continuous
    ((tailActualEdgePoisson_spec hT n).bounds true)).1
  simpa only [tailActualNodeCoupling, tailActualEdgeCoupling, sub_zero, one_div] using h

theorem tailActualNodeCoupling_pos {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : 0 < tailActualNodeCoupling T hT n :=
  (one_div_pos.mpr (tailActualEdgeLength_pos hT n)).trans_le
    (tailActualNodeCoupling_lower hT n)

theorem tailActualNodeCoupling_upper {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (n : ℕ) :
    tailActualNodeCoupling T hT n ≤ 2 / tailResistance T n := by
  have hδ : tailActualEdgeDiagonalSize T hT n ≤ 1 / 2 :=
    (tailActualEdgeDiagonalSize_le hT n).trans (hη.trans (by norm_num))
  have h := tailEdge_flux_coupling_le_two (tailActualEdgeLength_pos hT n)
    (tailActualEdgePotential_nonneg hT n) hδ
    ((tailActualEdgePoisson_spec hT n).differentiable true).continuous
    ((tailActualEdgePoisson_spec hT n).bounds true)
  have hL : tailActualNodeCoupling T hT n ≤ 2 / tailActualEdgeLength T n := by
    simpa only [tailActualNodeCoupling, tailActualEdgeCoupling, sub_zero, one_div] using h
  exact hL.trans (div_le_div_of_nonneg_left (by norm_num) (tailResistance_pos hT n)
    (le_add_of_nonneg_left (tailInnerResistance_pos hT n).le))

theorem tailActualEdgeAffineHeight_continuous (T : DeepTailData) (n : ℕ) (right : Bool) :
    Continuous (tailActualEdgeAffineHeight T n right) := by
  cases right
  · exact (continuous_const.sub continuous_id).div_const _
  · exact (continuous_id.sub continuous_const).div_const _

/-- The same affine comparison covers both endpoint heights. -/
theorem tailActualEdgeAffineHeight_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) :
    0 ≤ tailActualEdgeAffineHeight T n right s ∧ tailActualEdgeAffineHeight T n right s ≤ 1 := by
  cases right
  · refine ⟨tailEdgeLeftHeight_nonneg (tailActualEdgeLength_pos hT n) hs, ?_⟩
    apply (div_le_iff₀ (sub_pos.mpr (tailActualEdgeLength_pos hT n))).mpr
    linarith only [hs.1]
  · refine ⟨tailEdgeRightHeight_nonneg (tailActualEdgeLength_pos hT n) hs, ?_⟩
    apply (div_le_iff₀ (sub_pos.mpr (tailActualEdgeLength_pos hT n))).mpr
    linarith only [hs.2]

theorem tailActualEdge_mass_subset {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    Icc 0 (tailInnerResistance T n) ⊆ Icc 0 (tailActualEdgeLength T n) :=
  Icc_subset_Icc le_rfl (le_add_of_nonneg_right (tailResistance_pos hT n).le)

theorem tailActualEdge_gap_subset {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    Icc (tailInnerResistance T n) (tailActualEdgeLength T n) ⊆
      Icc 0 (tailActualEdgeLength T n) :=
  Icc_subset_Icc (tailInnerResistance_pos hT n).le le_rfl

theorem tailActualEdge_one_sub_ratio_pos {T : DeepTailData} (hT : DeepTailHypotheses T) :
    0 < 1 - T.η / T.K := by
  have hK : 0 < T.K := zero_lt_one.trans hT.2.2.2.2.2.2.1
  apply sub_pos.mpr
  apply (div_lt_iff₀ hK).mpr
  simpa only [one_mul] using hT.2.2.2.2.2.1.trans hT.2.2.2.2.2.2.1

/-- On the mass part, the left height is close to one and the right height is small. -/
theorem tailActualEdgeAffineHeight_mass_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailInnerResistance T n)) :
    (if right then 0 else 1 - T.η / T.K) ≤ tailActualEdgeAffineHeight T n right s ∧
      tailActualEdgeAffineHeight T n right s ≤
        (if right then tailInnerResistance T n / tailActualEdgeLength T n else 1) := by
  have hs' := tailActualEdge_mass_subset hT n hs
  cases right
  · refine ⟨?_, (tailActualEdgeAffineHeight_bounds hT n false hs').2⟩
    change 1 - T.η / T.K ≤
      (tailActualEdgeLength T n - s) / (tailActualEdgeLength T n - 0)
    rw [sub_zero, sub_div, div_self (tailActualEdgeLength_pos hT n).ne']
    exact sub_le_sub_left
      ((div_le_div_of_nonneg_right hs.2 (tailActualEdgeLength_pos hT n).le).trans
        (deepTail_inner_edge_ratio_le hT n)) 1
  · refine ⟨(tailActualEdgeAffineHeight_bounds hT n true hs').1, ?_⟩
    change (s - 0) / (tailActualEdgeLength T n - 0) ≤
      tailInnerResistance T n / tailActualEdgeLength T n
    simpa only [sub_zero] using div_le_div_of_nonneg_right hs.2 (tailActualEdgeLength_pos hT n).le

theorem tailActualEdgePoisson_bounds_eta {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {s : ℝ}
    (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) :
    tailActualEdgeAffineHeight T n right s ≤ tailActualEdgePoisson T hT n right s ∧
      tailActualEdgePoisson T hT n right s ≤ tailActualEdgeAffineHeight T n right s / (1 - T.η) := by
  have h := (tailActualEdgePoisson_spec hT n).bounds right s hs
  exact ⟨h.1, h.2.trans (div_le_div_of_nonneg_left
    (tailActualEdgeAffineHeight_bounds hT n right hs).1 (sub_pos.mpr hT.2.2.2.2.2.1)
    (sub_le_sub_left (tailActualEdgeDiagonalSize_le hT n) 1))⟩

/-- The weighted diagonal pairing on any resistance subinterval. -/
def tailActualEdgePairing (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) (right : Bool) (l r : ℝ) : ℝ :=
  ∫ s in l..r, tailActualEdgeWeight T hT n s * tailActualEdgeAffineHeight T n right s *
    tailActualEdgePoisson T hT n right s

theorem tailActualEdgePairing_interval_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {l r low high : ℝ}
    (hlr : l ≤ r) (hsub : Icc l r ⊆ Icc 0 (tailActualEdgeLength T n))
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hb : ∀ s ∈ Icc l r,
      low ≤ tailActualEdgeAffineHeight T n right s ∧ tailActualEdgeAffineHeight T n right s ≤ high) :
    low ^ 2 * (∫ s in l..r, tailActualEdgeWeight T hT n s) ≤
        tailActualEdgePairing T hT n right l r ∧
      tailActualEdgePairing T hT n right l r ≤
        (high ^ 2 / (1 - T.η)) * (∫ s in l..r, tailActualEdgeWeight T hT n s) :=
  tail_poisson_pairing_integral_bounds hlr hT.2.2.2.2.2.1
    ((tailActualEdgeWeight_continuousOn hT n).mono hsub)
    (tailActualEdgeAffineHeight_continuous T n right).continuousOn
    ((tailActualEdgePoisson_spec hT n).differentiable right).continuous.continuousOn
    (fun s _ => (tailActualEdgeWeight_pos hT n s).le) hlow hhigh hb
    (fun s hs => tailActualEdgePoisson_bounds_eta hT n right (hsub hs))

theorem tailActualEdgePairing_mass_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    (if right then 0 else 1 - T.η / T.K) ^ 2 * tailMass T n ≤
        tailActualEdgePairing T hT n right 0 (tailInnerResistance T n) ∧
      tailActualEdgePairing T hT n right 0 (tailInnerResistance T n) ≤
        ((if right then tailInnerResistance T n / tailActualEdgeLength T n else 1) ^ 2 /
          (1 - T.η)) * tailMass T n := by
  have hlo : 0 ≤ (if right then 0 else 1 - T.η / T.K) := by
    cases right
    · exact (tailActualEdge_one_sub_ratio_pos hT).le
    · exact le_rfl
  have hhi : 0 ≤ (if right then tailInnerResistance T n / tailActualEdgeLength T n else 1) := by
    cases right
    · exact zero_le_one
    · exact (div_pos (tailInnerResistance_pos hT n) (tailActualEdgeLength_pos hT n)).le
  have h := tailActualEdgePairing_interval_bounds hT n right (tailInnerResistance_pos hT n).le
    (tailActualEdge_mass_subset hT n) hlo hhi
    (fun s hs => tailActualEdgeAffineHeight_mass_bounds hT n right hs)
  simpa only [tailActualEdgeWeight_mass] using h

theorem tailActualEdgePairing_gap_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    0 ≤ tailActualEdgePairing T hT n right (tailInnerResistance T n) (tailActualEdgeLength T n) ∧
      tailActualEdgePairing T hT n right (tailInnerResistance T n) (tailActualEdgeLength T n) ≤
        (1 / (1 - T.η)) * tailGapMass T n := by
  have h := tailActualEdgePairing_interval_bounds hT n right (low := 0) (high := 1)
    (l := tailInnerResistance T n) (r := tailActualEdgeLength T n)
    (le_add_of_nonneg_right (tailResistance_pos hT n).le)
    (tailActualEdge_gap_subset hT n) le_rfl zero_le_one
    (fun s hs => tailActualEdgeAffineHeight_bounds hT n right (tailActualEdge_gap_subset hT n hs))
  simpa only [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul, one_pow,
    tailActualEdgeWeight_gapMass] using h

theorem tailActualEdgePairing_split {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    tailActualEdgePairing T hT n right 0 (tailActualEdgeLength T n) =
      tailActualEdgePairing T hT n right 0 (tailInnerResistance T n) +
        tailActualEdgePairing T hT n right (tailInnerResistance T n) (tailActualEdgeLength T n) := by
  have hc := ((tailActualEdgeWeight_continuousOn hT n).mul
    (tailActualEdgeAffineHeight_continuous T n right).continuousOn).mul
    ((tailActualEdgePoisson_spec hT n).differentiable right).continuous.continuousOn
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (tailActualEdge_mass_subset hT n)).intervalIntegrable_of_Icc
      (tailInnerResistance_pos hT n).le)
    ((hc.mono (tailActualEdge_gap_subset hT n)).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right (tailResistance_pos hT n).le))).symm

/-- The left pairing carries the mass of its own node. -/
theorem tailActualEdgePairing_left_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    (1 - T.η / T.K) ^ 2 * tailMass T n ≤
        tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) ∧
      tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) ≤
        ((1 + T.η) / (1 - T.η)) * tailMass T n := by
  have hm := tailActualEdgePairing_mass_bounds hT n false
  have hg := tailActualEdgePairing_gap_bounds hT n false
  simp only [Bool.false_eq_true, ite_false, one_pow] at hm
  constructor
  · rw [tailActualEdgePairing_split]
    linarith only [hm.1, hg.1]
  · calc
      tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) =
          tailActualEdgePairing T hT n false 0 (tailInnerResistance T n) +
            tailActualEdgePairing T hT n false (tailInnerResistance T n) (tailActualEdgeLength T n) :=
        tailActualEdgePairing_split hT n false
      _ ≤ (1 / (1 - T.η)) * tailMass T n + (1 / (1 - T.η)) * tailGapMass T n :=
        add_le_add hm.2 hg.2
      _ = (tailMass T n + tailGapMass T n) / (1 - T.η) := by ring
      _ ≤ ((1 + T.η) * tailMass T n) / (1 - T.η) :=
        div_le_div_of_nonneg_right (by nlinarith only [deepTail_gap_mass_le_left hT n])
          (sub_pos.mpr hT.2.2.2.2.2.1).le
      _ = ((1 + T.η) / (1 - T.η)) * tailMass T n := by ring

/-- The right pairing is small in the mass weight of the following node. -/
theorem tailActualEdgePairing_right_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    0 ≤ tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) ∧
      tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) ≤
        ((T.η + (T.η / T.K) ^ 2) / (1 - T.η)) * tailMass T (n + 1) := by
  have hm := tailActualEdgePairing_mass_bounds hT n true
  have hg := tailActualEdgePairing_gap_bounds hT n true
  simp only [ite_true, show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul] at hm
  have hshift : tailMass T n * (tailInnerResistance T n / tailActualEdgeLength T n) ^ 2 ≤
      (T.η / T.K) ^ 2 * tailMass T (n + 1) := deepTail_shifted_inner_edge_sq_le hT n
  constructor
  · rw [tailActualEdgePairing_split]
    exact add_nonneg hm.1 hg.1
  · calc
      tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) =
          tailActualEdgePairing T hT n true 0 (tailInnerResistance T n) +
            tailActualEdgePairing T hT n true (tailInnerResistance T n) (tailActualEdgeLength T n) :=
        tailActualEdgePairing_split hT n true
      _ ≤ ((tailInnerResistance T n / tailActualEdgeLength T n) ^ 2 / (1 - T.η)) * tailMass T n +
          (1 / (1 - T.η)) * tailGapMass T n := add_le_add hm.2 hg.2
      _ = (tailMass T n * (tailInnerResistance T n / tailActualEdgeLength T n) ^ 2 +
          tailGapMass T n) / (1 - T.η) := by ring
      _ ≤ ((T.η / T.K) ^ 2 * tailMass T (n + 1) + T.η * tailMass T (n + 1)) / (1 - T.η) :=
        div_le_div_of_nonneg_right (add_le_add hshift (deepTail_gap_mass_le_right hT n))
          (sub_pos.mpr hT.2.2.2.2.2.1).le
      _ = ((T.η + (T.η / T.K) ^ 2) / (1 - T.η)) * tailMass T (n + 1) := by ring

theorem tailActualEdgePairing_left_scaled_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    (3 / 4 : ℝ) * (T.Λ * tailMass T n) ≤
        T.Λ * tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) ∧
      T.Λ * tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) ≤
        (3 / 2 : ℝ) * (T.Λ * tailMass T n) := by
  have hp := tailActualEdgePairing_left_bounds hT n
  have hf := tail_poisson_factors_small hT.2.2.2.2.1.le hη hK
  constructor
  · calc
      (3 / 4 : ℝ) * (T.Λ * tailMass T n) = T.Λ * ((3 / 4 : ℝ) * tailMass T n) := by ring
      _ ≤ T.Λ * ((1 - T.η / T.K) ^ 2 * tailMass T n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hf.1 (tailMass_pos hT n).le) hT.2.2.1.le
      _ ≤ T.Λ * tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) :=
        mul_le_mul_of_nonneg_left hp.1 hT.2.2.1.le
  · calc
      T.Λ * tailActualEdgePairing T hT n false 0 (tailActualEdgeLength T n) ≤
          T.Λ * (((1 + T.η) / (1 - T.η)) * tailMass T n) :=
        mul_le_mul_of_nonneg_left hp.2 hT.2.2.1.le
      _ ≤ T.Λ * ((3 / 2 : ℝ) * tailMass T n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hf.2.1 (tailMass_pos hT n).le) hT.2.2.1.le
      _ = (3 / 2 : ℝ) * (T.Λ * tailMass T n) := by ring

theorem tailActualEdgePairing_right_scaled_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    0 ≤ T.Λ * tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) ∧
      T.Λ * tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) ≤
        (1 / 4 : ℝ) * (T.Λ * tailMass T (n + 1)) := by
  have hp := tailActualEdgePairing_right_bounds hT n
  have hf := tail_poisson_factors_small hT.2.2.2.2.1.le hη hK
  refine ⟨mul_nonneg hT.2.2.1.le hp.1, ?_⟩
  calc
    T.Λ * tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) ≤
        T.Λ * (((T.η + (T.η / T.K) ^ 2) / (1 - T.η)) * tailMass T (n + 1)) :=
      mul_le_mul_of_nonneg_left hp.2 hT.2.2.1.le
    _ ≤ T.Λ * ((1 / 4 : ℝ) * tailMass T (n + 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hf.2.2.1 (tailMass_pos hT (n + 1)).le) hT.2.2.1.le
    _ = (1 / 4 : ℝ) * (T.Λ * tailMass T (n + 1)) := by ring

/-- The abstract flux integral is exactly the weighted actual pairing. -/
theorem tailActualEdgeDiagonal_eq_pairing {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) right =
      (tailActualEdgeLength T n)⁻¹ -
        T.Λ * tailActualEdgePairing T hT n right 0 (tailActualEdgeLength T n) := by
  unfold tailActualEdgeDiagonal tailActualEdgePairing
  rw [one_div, ← intervalIntegral.integral_const_mul]
  apply congrArg (fun z : ℝ => (tailActualEdgeLength T n)⁻¹ - z)
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (tailActualEdgeLength_pos hT n).le]
  intro s hs
  dsimp only
  rw [tailActualEdgePotential_extend hT n hs]
  ring

theorem tailActualInteriorDiagonal_eq_pairing {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualInteriorDiagonal T hT n =
      T.Λ * tailActualEdgePairing T hT (n + 1) false 0 (tailActualEdgeLength T (n + 1)) +
        T.Λ * tailActualEdgePairing T hT n true 0 (tailActualEdgeLength T n) -
          (tailActualEdgeLength T n)⁻¹ - (tailActualEdgeLength T (n + 1))⁻¹ := by
  unfold tailActualInteriorDiagonal
  simp only [tailActualEdgeDiagonal_eq_pairing]
  ring

/-- The actual interior diagonal has the required mass scale. -/
theorem tailActualInteriorDiagonal_bounds {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    (T.Λ * tailMass T (n + 1)) / 2 ≤ tailActualInteriorDiagonal T hT n ∧
      tailActualInteriorDiagonal T hT n ≤ 2 * (T.Λ * tailMass T (n + 1)) := by
  have hr₀ : 0 ≤ (tailActualEdgeLength T n)⁻¹ ∧
      (tailActualEdgeLength T n)⁻¹ ≤ T.Λ * tailMass T (n + 1) / T.K :=
    ⟨(inv_pos.mpr (tailActualEdgeLength_pos hT n)).le, deepTail_inverse_edge_right hT n⟩
  have hr₁ : 0 ≤ (tailActualEdgeLength T (n + 1))⁻¹ ∧
      (tailActualEdgeLength T (n + 1))⁻¹ ≤ T.Λ * tailMass T (n + 1) / T.K :=
    ⟨(inv_pos.mpr (tailActualEdgeLength_pos hT (n + 1))).le, deepTail_inverse_edge_left hT (n + 1)⟩
  simp only [tailActualInteriorDiagonal_eq_pairing]
  exact tail_node_diagonal_bounds (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))) hK
    (tailActualEdgePairing_left_scaled_bounds hT hη hK (n + 1))
    (tailActualEdgePairing_right_scaled_bounds hT hη hK n) hr₀ hr₁

theorem tailActualInteriorDiagonal_pos {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) (n : ℕ) :
    0 < tailActualInteriorDiagonal T hT n :=
  (div_pos (mul_pos hT.2.2.1 (tailMass_pos hT (n + 1))) (by norm_num)).trans_le
    (tailActualInteriorDiagonal_bounds hT hη hK n).1

end ContinuousFlexibility.Radial
