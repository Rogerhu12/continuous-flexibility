module

public import ContinuousFlexibility.Radial.MatchedPhysicalSchurRows

/-!
# Density conversion for all four actual physical channels

The existing modal cell maps and scalar projection are indexed together.
Each physical input/output conversion pays only its actual reciprocal
density cost. This includes the two border channels and the scalar block,
so bounds obtained from the actual matching formula apply directly to
the raw kernel used by the weighted Schur test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

def matchedModeChannel (D : ReferenceData) (hP : RadialPartition D) :
    ℕ → RadialModePair D →L[ℝ] RadialModePair D
  | 0 => matchedModeBorder D
  | m + 1 => matchedModeCell D hP m

def matchedChannelDensityCost (D : ReferenceData) (K : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => Real.sqrt (K * radialE (D.cellIndex m) ^ K)

theorem matchedModeBorder_norm (D : ReferenceData) (U : RadialModePair D) :
    ‖matchedModeBorder D U‖ = ‖U.2‖ := by
  rw [matchedModeBorder_apply, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

theorem matchedMode_borderUnit_norm (D : ReferenceData) :
    ‖((0, 1) : RadialModePair D)‖ = 1 := by
  simp only [Prod.norm_def, norm_zero, norm_one, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem matchedPhysicalScalarRow_density_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (m : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B) :
    ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L G ∘L
        matchedPhysicalSourceCell D hD hP m‖ ≤
      Real.sqrt B * ‖matchedModeBorder D ∘L G ∘L matchedModeCell D hP m‖ := by
  let S := matchedPhysicalSourceFactor D hD hP m
  let A := matchedModeBorder D ∘L G ∘L matchedModeCell D hP m
  have hS : ‖S‖ ≤ Real.sqrt B := norm_matchedPhysicalSourceFactor_le hD hP m hB hbound
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg A))
  intro f
  change ‖(G (matchedModeCell D hP m (S f))).2‖ ≤ (Real.sqrt B * ‖A‖) * ‖f‖
  have hSf : ‖S f‖ ≤ Real.sqrt B * ‖f‖ :=
    (S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg f))
  calc
    _ = ‖A (S f)‖ := (matchedModeBorder_norm D _).symm
    _ ≤ ‖A‖ * ‖S f‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (Real.sqrt B * ‖f‖) := mul_le_mul_of_nonneg_left hSf (norm_nonneg A)
    _ = _ := by ring

theorem matchedPhysicalBorderColumn_density_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells k, (matchingDensity D r)⁻¹ ≤ B) :
    ‖matchedPhysicalOutputCell D hD hP k (G (0, 1))‖ ≤
      Real.sqrt B * ‖matchedModeCell D hP k ∘L G ∘L matchedModeBorder D‖ := by
  let R := matchedPhysicalFieldFactor D hD hP k
  let A := matchedModeCell D hP k ∘L G ∘L matchedModeBorder D
  have hR : ‖R‖ ≤ Real.sqrt B := norm_matchedPhysicalFieldFactor_le hD hP k hB hbound
  have hunit : A (0, 1) = matchedModeCell D hP k (G (0, 1)) := by
    change matchedModeCell D hP k (G (matchedModeBorder D (0, 1))) = _
    rw [matchedModeBorder_apply]
  change ‖R (matchedModeCell D hP k (G (0, 1)))‖ ≤ Real.sqrt B * ‖A‖
  rw [← hunit]
  calc
    _ ≤ ‖R‖ * ‖A (0, 1)‖ := R.le_opNorm _
    _ ≤ Real.sqrt B * ‖A (0, 1)‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ ≤ Real.sqrt B * (‖A‖ * ‖((0, 1) : RadialModePair D)‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (Real.sqrt_nonneg B)
    _ = _ := by rw [matchedMode_borderUnit_norm, mul_one]

theorem matchedPhysicalScalarBlock_modal_bound (D : ReferenceData)
    (G : RadialModePair D →L[ℝ] RadialModePair D) :
    ‖(G (0, 1)).2‖ ≤ ‖matchedModeBorder D ∘L G ∘L matchedModeBorder D‖ := by
  let A := matchedModeBorder D ∘L G ∘L matchedModeBorder D
  have he : ‖(G (0, 1)).2‖ = ‖A (0, 1)‖ := by
    change ‖(G (0, 1)).2‖ = ‖matchedModeBorder D (G (matchedModeBorder D (0, 1)))‖
    rw [matchedModeBorder_apply D (0, 1), matchedModeBorder_norm]
  calc
    _ = ‖A (0, 1)‖ := he
    _ ≤ ‖A‖ * ‖((0, 1) : RadialModePair D)‖ := A.le_opNorm _
    _ = _ := by rw [matchedMode_borderUnit_norm, mul_one]

/-- One reciprocal-density coefficient works for every operator and all
four channel combinations. These are the actual raw blocks. -/
theorem exists_matchedPhysicalRawKernel_density_cost {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ),
        matchedPhysicalRawKernel D hD hP G k m ≤
          matchedChannelDensityCost D K k * matchedChannelDensityCost D K m *
            ‖matchedModeChannel D hP k ∘L G ∘L matchedModeChannel D hP m‖ := by
  obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
  have hcost (m : ℕ) : 0 ≤ K * radialE (D.cellIndex m) ^ K :=
    mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  refine ⟨K, hK, ?_⟩
  intro G k m
  cases k with
  | zero =>
      cases m with
      | zero =>
          change ‖(G (0, 1)).2‖ ≤
            1 * 1 * ‖matchedModeBorder D ∘L G ∘L matchedModeBorder D‖
          rw [one_mul, one_mul]
          exact matchedPhysicalScalarBlock_modal_bound D G
      | succ m =>
          change ‖(ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ) ∘L G ∘L
            matchedPhysicalSourceCell D hD hP m‖ ≤
            1 * Real.sqrt (K * radialE (D.cellIndex m) ^ K) *
              ‖matchedModeBorder D ∘L G ∘L matchedModeCell D hP m‖
          rw [one_mul]
          exact matchedPhysicalScalarRow_density_bound hD hP G m (hcost m) (hbound m)
  | succ k =>
      cases m with
      | zero =>
          change ‖matchedPhysicalOutputCell D hD hP k (G (0, 1))‖ ≤
            Real.sqrt (K * radialE (D.cellIndex k) ^ K) * 1 *
              ‖matchedModeCell D hP k ∘L G ∘L matchedModeBorder D‖
          rw [mul_one]
          exact matchedPhysicalBorderColumn_density_bound hD hP G k (hcost k) (hbound k)
      | succ m =>
          exact matchedPhysicalCellBlock_norm_le hD hP G k m
            (hcost k) (hcost m) (hbound k) (hbound m)

end ContinuousFlexibility.Radial
