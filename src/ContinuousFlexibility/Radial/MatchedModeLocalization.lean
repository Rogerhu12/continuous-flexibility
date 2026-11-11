import ContinuousFlexibility.Radial.ModeLocalMeasure
import ContinuousFlexibility.Radial.MorseChainScales
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.Holder

/-!
# Actual modal cell localizers

The cell maps multiply by the localizers of ReferenceData on its actual
radial Hilbert measure. The scalar border has its own projection, so it is
not counted once for every radial cell. The coefficient bound on reciprocal
density follows from the frozen profile bounds and is independent of the
frequency.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Statements
open scoped ENNReal BigOperators RealInnerProductSpace InnerProductSpace

theorem matchedRadialLocalizer_le_one {D : ReferenceData}
    (hD : RadialPartition D) (m : ℕ) (r : ℝ) : D.localizer m r ≤ 1 := by
  by_cases hz : D.localizer m r = 0
  · rw [hz]
    norm_num
  · have hr : r ∈ radialCore D := hD.2.2.2.1 m (hD.2.2.1 m hz)
    have hs := (hD.2.2.2.2.1 r hr).1.le_tsum m (fun n _ => hD.2.1 n r)
    simpa only [(hD.2.2.2.2.1 r hr).2] using hs

theorem matchedRadialLocalizer_abs_le_one {D : ReferenceData}
    (hD : RadialPartition D) (m : ℕ) (r : ℝ) : |D.localizer m r| ≤ 1 := by
  rw [abs_of_nonneg (hD.2.1 m r)]
  exact matchedRadialLocalizer_le_one hD m r

/-- The actual cell cutoff as an element of L-infinity for the radial measure. -/
def matchedModeCellWeight (D : ReferenceData) (hD : RadialPartition D) (m : ℕ) :
    Lp ℝ ∞ (radialHilbertMeasure D) :=
  (memLp_top_of_bound (μ := radialHilbertMeasure D)
    (hD.1 m).continuous.measurable.aestronglyMeasurable 1
    (.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using matchedRadialLocalizer_abs_le_one hD m r)).toLp
      (D.localizer m)

theorem matchedModeCellWeight_ae (D : ReferenceData) (hD : RadialPartition D) (m : ℕ) :
    matchedModeCellWeight D hD m =ᵐ[radialHilbertMeasure D] D.localizer m :=
  MemLp.coeFn_toLp _

/-- Multiplication by the actual radial cell localizer on the actual mode L² space. -/
def matchedModeCellL2 (D : ReferenceData) (hD : RadialPartition D) (m : ℕ) :
    RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (radialHilbertMeasure D) ∞ 2 2
    (matchedModeCellWeight D hD m)

theorem matchedModeCellL2_ae (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) :
    matchedModeCellL2 D hD m u =ᵐ[radialHilbertMeasure D]
      fun r => D.localizer m r * u r := by
  have hm : matchedModeCellL2 D hD m u =ᵐ[radialHilbertMeasure D]
      fun r => matchedModeCellWeight D hD m r * u r := by
    simpa only [matchedModeCellL2, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply'] using
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
        (matchedModeCellWeight D hD m) u
  filter_upwards [hm, matchedModeCellWeight_ae D hD m] with r hr hw
  rw [hr, hw]

theorem matchedModeCellL2_norm_apply_le (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) : ‖matchedModeCellL2 D hD m u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [matchedModeCellL2_ae D hD m u] with r hr
  rw [hr, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (matchedRadialLocalizer_abs_le_one hD m r)
    (abs_nonneg (u r))).trans_eq (one_mul _)

theorem norm_matchedModeCellL2_le_one (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) : ‖matchedModeCellL2 D hD m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun u => by simpa only [one_mul] using matchedModeCellL2_norm_apply_le D hD m u)

theorem matchedModeCellL2_inner (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (u v : RadialModeL2 D) :
    ⟪matchedModeCellL2 D hD m u, v⟫_ℝ =
      ⟪u, matchedModeCellL2 D hD m v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matchedModeCellL2_ae D hD m u, matchedModeCellL2_ae D hD m v]
    with r hu hv
  rw [hu, hv]
  simp only [Real.inner_apply]
  ring

/-- A field cell has zero scalar component; the border is a separate cell. -/
def matchedModeCell (D : ReferenceData) (hD : RadialPartition D) (m : ℕ) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  ((matchedModeCellL2 D hD m).comp
    (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ)).prod 0

@[simp] theorem matchedModeCell_apply (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (U : RadialModePair D) :
    matchedModeCell D hD m U = (matchedModeCellL2 D hD m U.1, 0) := rfl

def matchedModeBorder (D : ReferenceData) : RadialModePair D →L[ℝ] RadialModePair D :=
  (0 : RadialModePair D →L[ℝ] RadialModeL2 D).prod
    (ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ)

@[simp] theorem matchedModeBorder_apply (D : ReferenceData) (U : RadialModePair D) :
    matchedModeBorder D U = (0, U.2) := rfl

theorem matchedModeCell_norm_apply_le (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (U : RadialModePair D) : ‖matchedModeCell D hD m U‖ ≤ ‖U‖ := by
  rw [matchedModeCell_apply, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)]
  exact (matchedModeCellL2_norm_apply_le D hD m U.1).trans (le_max_left _ _)

theorem norm_matchedModeCell_le_one (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) : ‖matchedModeCell D hD m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun U => by simpa only [one_mul] using matchedModeCell_norm_apply_le D hD m U)

theorem norm_matchedModeBorder_le_one (D : ReferenceData) : ‖matchedModeBorder D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro U
  rw [matchedModeBorder_apply, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _), one_mul]
  exact le_max_right _ _

theorem matchedModeCell_pairing (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (U F : RadialModePair D) :
    modePairing D U (matchedModeCell D hD m F) =
      modePairing D (matchedModeCell D hD m U) F := by
  simp only [modePairing, matchedModeCell_apply, mul_zero, zero_mul, add_zero]
  exact (matchedModeCellL2_inner D hD m U.1 F.1).symm

theorem matchedModeBorder_pairing (D : ReferenceData) (U F : RadialModePair D) :
    modePairing D U (matchedModeBorder D F) =
      modePairing D (matchedModeBorder D U) F := by
  simp only [modePairing, matchedModeBorder_apply, inner_zero_right,
    inner_zero_left, zero_add]

/-- Localization retains the exact square integral, with the actual density. -/
theorem matchedModeCellL2_norm_sq (D : ReferenceData) (hD : RadialPartition D)
    (m : ℕ) (u : RadialModeL2 D) :
    ‖matchedModeCellL2 D hD m u‖ ^ 2 =
      ∫ r, (D.localizer m r * u r) ^ 2 ∂radialHilbertMeasure D := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matchedModeCellL2_ae D hD m u] with r hr
  rw [hr]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem matchedModeCellL2_norm_sq_physical {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    (u : RadialModeL2 D) :
    ‖matchedModeCellL2 D hP m u‖ ^ 2 =
      ∫ r in D.a..D.b, matchingDensity D r * (D.localizer m r * u r) ^ 2 := by
  rw [matchedModeCellL2_norm_sq, matchingDensity_integral hD]

/-- A single coefficient exponent bounds the reciprocal density on every
actual cell. It depends on the profile, and not on a frequency or a source. -/
theorem matchedDensity_inv_coefficient_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ K : ℝ, 0 < K ∧ ∀ m r, r ∈ D.cells m →
      (matchingDensity D r)⁻¹ ≤ K * radialE (D.cellIndex m) ^ K := by
  obtain ⟨C, hC⟩ := hD
  rcases hC with ⟨hgeom, hpart, hpos, _, _, _, _, _, _, hinv, _, _, _⟩
  let A : ℝ := D.b ^ 2 / 12 * C 0
  let K : ℝ := max 1 (max (C 0) A)
  have hK₁ : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK₁
  have hCK : C 0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hAK : A ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro m r hr
  have hcore := hpart.2.2.2.1 m hr
  have hr₀ : 0 < r := hgeom.1.trans hcore.1
  have hw : 0 < D.w r := hgeom.2.2.2.2.1 r hcore
  have hrb : r ^ 2 ≤ D.b ^ 2 := pow_le_pow_left₀ hr₀.le hcore.2.le 2
  have hwbound := hinv m r hr 0
  change |(D.w r)⁻¹| ≤ C 0 * radialE (D.cellIndex m) ^ (C 0) at hwbound
  rw [abs_of_pos (inv_pos.mpr hw)] at hwbound
  have hE : 1 ≤ radialE (D.cellIndex m) :=
    one_le_exp_iff.mpr ((sq_nonneg _).trans (radial_nat_sq_le_Q _))
  have hcost : (matchingDensity D r)⁻¹ ≤ A * radialE (D.cellIndex m) ^ (C 0) := by
    calc
      (matchingDensity D r)⁻¹ = r ^ 2 / 12 * (D.w r)⁻¹ := by
        unfold matchingDensity
        field_simp [hw.ne', hr₀.ne']
        <;> ring
      _ ≤ (D.b ^ 2 / 12) * (C 0 * radialE (D.cellIndex m) ^ (C 0)) :=
        mul_le_mul (div_le_div_of_nonneg_right hrb (by norm_num)) hwbound
          (inv_nonneg.mpr hw.le) (by positivity)
      _ = A * radialE (D.cellIndex m) ^ (C 0) := by dsimp only [A]; ring
  exact hcost.trans
    (mul_le_mul hAK (Real.rpow_le_rpow_of_exponent_le hE hCK)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) hK.le)

end ContinuousFlexibility.Radial
