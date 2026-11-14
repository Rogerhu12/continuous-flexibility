module

public import ContinuousFlexibility.Radial.MatchedModeDensityConversion
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Physical cell operators for the actual modal inverse

The source multiplier is minus the reciprocal Hilbert density, restricted
to the measurable support of the actual smooth localizer. The output
multiplier forgets the density on that same support. Neither construction
requires the containing cell itself to be measurable.

Composing these maps with the actual modal cell maps recovers exactly
minus theta times the physical source divided by the density, and theta
times the resulting field. Their operator norms cost square roots of the
cellwise reciprocal-density bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Statements
open scoped ENNReal RealInnerProductSpace InnerProductSpace

abbrev MatchedPhysicalL2 (D : ReferenceData) :=
  Lp ℝ 2 (volume.restrict (radialCore D))

private theorem physicalL2_norm_sq (μ : Measure ℝ) (u : Lp ℝ 2 μ) :
    ‖u‖ ^ 2 = ∫ r, u r ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun r => by simp only [Real.inner_apply]; ring)

private theorem physicalL2_indicator_sq_le (μ : Measure ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) (u : Lp ℝ 2 μ) :
    (∫ r, (s.indicator u r) ^ 2 ∂μ) ≤ ‖u‖ ^ 2 := by
  rw [physicalL2_norm_sq]
  apply integral_mono_ae ((Lp.memLp u).indicator hs).integrable_sq
    (Lp.memLp u).integrable_sq
  exact .of_forall (fun r => by
    by_cases hr : r ∈ s
    · simp only [Set.indicator_of_mem hr, le_refl]
    · simpa only [Set.indicator_of_notMem hr, zero_pow (by decide : (2 : ℕ) ≠ 0)]
        using sq_nonneg (u r))

private def densityMultiplierValue (μ ν : Measure ℝ) (c : ℝ → ℝ)
    (hmem : ∀ u : Lp ℝ 2 ν, MemLp (fun r => c r * u r) 2 μ)
    (u : Lp ℝ 2 ν) : Lp ℝ 2 μ :=
  (hmem u).toLp (fun r => c r * u r)

private theorem densityMultiplierValue_ae (μ ν : Measure ℝ) (c : ℝ → ℝ)
    (hmem : ∀ u : Lp ℝ 2 ν, MemLp (fun r => c r * u r) 2 μ)
    (u : Lp ℝ 2 ν) :
    densityMultiplierValue μ ν c hmem u =ᵐ[μ] fun r => c r * u r :=
  MemLp.coeFn_toLp _

private theorem densityMultiplierValue_norm_sq (μ ν : Measure ℝ) (c : ℝ → ℝ)
    (hmem : ∀ u : Lp ℝ 2 ν, MemLp (fun r => c r * u r) 2 μ)
    (u : Lp ℝ 2 ν) :
    ‖densityMultiplierValue μ ν c hmem u‖ ^ 2 = ∫ r, (c r * u r) ^ 2 ∂μ := by
  rw [physicalL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [densityMultiplierValue_ae μ ν c hmem u] with r hr
  rw [hr]

private def densityMultiplierLinear (μ ν : Measure ℝ) (hμν : μ ≪ ν) (c : ℝ → ℝ)
    (hmem : ∀ u : Lp ℝ 2 ν, MemLp (fun r => c r * u r) 2 μ) :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := densityMultiplierValue μ ν c hmem
  map_add' u v := by
    apply Lp.ext
    filter_upwards [densityMultiplierValue_ae μ ν c hmem (u + v),
      densityMultiplierValue_ae μ ν c hmem u,
      densityMultiplierValue_ae μ ν c hmem v,
      Lp.coeFn_add (densityMultiplierValue μ ν c hmem u)
        (densityMultiplierValue μ ν c hmem v),
      hμν.ae_eq (Lp.coeFn_add u v)] with r hsum hu hv hadd hin
    rw [hadd, Pi.add_apply, hsum, hu, hv, hin, Pi.add_apply]
    ring
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [densityMultiplierValue_ae μ ν c hmem (a • u),
      densityMultiplierValue_ae μ ν c hmem u,
      Lp.coeFn_smul a (densityMultiplierValue μ ν c hmem u),
      hμν.ae_eq (Lp.coeFn_smul a u)] with r hsmul hu hout hin
    simp only [RingHom.id_apply]
    rw [hout, Pi.smul_apply, hsmul, hu, hin, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

private def physicalCellIndicator (D : ReferenceData) (m : ℕ) : ℝ → ℝ :=
  (Function.support (D.localizer m)).indicator (fun _ => 1)

private theorem physicalCellIndicator_mul (D : ReferenceData) (m : ℕ)
    (f : ℝ → ℝ) (r : ℝ) :
    physicalCellIndicator D m r * f r =
      (Function.support (D.localizer m)).indicator f r := by
  by_cases hr : r ∈ Function.support (D.localizer m)
  · simp only [physicalCellIndicator, Set.indicator_of_mem hr, one_mul]
  · simp only [physicalCellIndicator, Set.indicator_of_notMem hr, zero_mul]

private theorem physicalCellSupport_measurable {D : ReferenceData}
    (hP : RadialPartition D) (m : ℕ) :
    MeasurableSet (Function.support (D.localizer m)) :=
  measurableSet_support (hP.1 m).continuous.measurable

private theorem physicalCellIndicator_mem_cell {D : ReferenceData}
    (hP : RadialPartition D) (m : ℕ) (f : ℝ → ℝ) {r : ℝ}
    (hr : (Function.support (D.localizer m)).indicator f r ≠ 0) : r ∈ D.cells m := by
  by_cases hs : r ∈ Function.support (D.localizer m)
  · exact hP.2.2.1 m hs
  · exact False.elim (hr (Set.indicator_of_notMem hs f))

private def physicalCellSourceCoefficient (D : ReferenceData) (m : ℕ) (r : ℝ) : ℝ :=
  -physicalCellIndicator D m r / matchingDensity D r

private theorem physicalCellSourceCoefficient_mul (D : ReferenceData) (m : ℕ)
    (f : ℝ → ℝ) (r : ℝ) :
    physicalCellSourceCoefficient D m r * f r =
      -((Function.support (D.localizer m)).indicator f r) / matchingDensity D r := by
  rw [← physicalCellIndicator_mul]
  dsimp only [physicalCellSourceCoefficient]
  ring

private theorem physicalCellField_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    (u : RadialModeL2 D) :
    MemLp (fun r => physicalCellIndicator D m r * u r) 2
      (volume.restrict (radialCore D)) := by
  obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
  have hB : 0 ≤ K * radialE (D.cellIndex m) ^ K :=
    mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hs := physicalCellSupport_measurable hP m
  have h := matchedMode_output_of_support hD hB
    ((Function.support (D.localizer m)).indicator u)
    ((Lp.memLp u).indicator hs)
    (fun r _ hne => hbound m r (physicalCellIndicator_mem_cell hP m u hne))
  simpa only [physicalCellIndicator_mul] using h.1

private theorem physicalCellSource_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    (f : MatchedPhysicalL2 D) :
    MemLp (fun r => physicalCellSourceCoefficient D m r * f r) 2
      (radialHilbertMeasure D) := by
  obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
  have hB : 0 ≤ K * radialE (D.cellIndex m) ^ K :=
    mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hs := physicalCellSupport_measurable hP m
  have h := matchedMode_source_of_support hD hB
    ((Function.support (D.localizer m)).indicator f)
    ((Lp.memLp f).indicator hs)
    (fun r _ hne => hbound m r (physicalCellIndicator_mem_cell hP m f hne))
  simpa only [physicalCellSourceCoefficient_mul] using h.1

private theorem physicalCellField_value_norm_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B)
    (u : RadialModeL2 D) :
    ‖densityMultiplierValue (volume.restrict (radialCore D)) (radialHilbertMeasure D)
      (physicalCellIndicator D m) (physicalCellField_memLp hD hP m) u‖ ≤
        Real.sqrt B * ‖u‖ := by
  have hs := physicalCellSupport_measurable hP m
  have h := matchedMode_output_of_support hD hB
    ((Function.support (D.localizer m)).indicator u)
    ((Lp.memLp u).indicator hs)
    (fun r _ hne => hbound r (physicalCellIndicator_mem_cell hP m u hne))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg u))).mp
  rw [densityMultiplierValue_norm_sq, mul_pow, Real.sq_sqrt hB]
  simp only [physicalCellIndicator_mul]
  exact h.2.trans (mul_le_mul_of_nonneg_left
    (physicalL2_indicator_sq_le (radialHilbertMeasure D) _ hs u) hB)

private theorem physicalCellSource_value_norm_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B)
    (f : MatchedPhysicalL2 D) :
    ‖densityMultiplierValue (radialHilbertMeasure D) (volume.restrict (radialCore D))
      (physicalCellSourceCoefficient D m) (physicalCellSource_memLp hD hP m) f‖ ≤
        Real.sqrt B * ‖f‖ := by
  have hs := physicalCellSupport_measurable hP m
  have h := matchedMode_source_of_support hD hB
    ((Function.support (D.localizer m)).indicator f)
    ((Lp.memLp f).indicator hs)
    (fun r _ hne => hbound r (physicalCellIndicator_mem_cell hP m f hne))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg f))).mp
  rw [densityMultiplierValue_norm_sq, mul_pow, Real.sq_sqrt hB]
  simp only [physicalCellSourceCoefficient_mul]
  exact h.2.trans (mul_le_mul_of_nonneg_left
    (physicalL2_indicator_sq_le (volume.restrict (radialCore D)) _ hs f) hB)

/-- The physical source factor on the actual support of a cell localizer.
Its scalar coordinate is zero; the physical border is treated separately. -/
def matchedPhysicalSourceFactor (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ) :
    MatchedPhysicalL2 D →L[ℝ] RadialModePair D :=
  ((densityMultiplierLinear (radialHilbertMeasure D) (volume.restrict (radialCore D))
    (withDensity_absolutelyContinuous _ _) (physicalCellSourceCoefficient D m)
    (physicalCellSource_memLp hD hP m)).mkContinuousOfExistsBound (by
      obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
      have hB : 0 ≤ K * radialE (D.cellIndex m) ^ K :=
        mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
      exact ⟨Real.sqrt (K * radialE (D.cellIndex m) ^ K),
        physicalCellSource_value_norm_le hD hP m hB (hbound m)⟩)).prod 0

/-- The output conversion on the same actual support. -/
def matchedPhysicalFieldFactor (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ) :
    RadialModePair D →L[ℝ] MatchedPhysicalL2 D :=
  ((densityMultiplierLinear (volume.restrict (radialCore D)) (radialHilbertMeasure D)
    (matchedModeLebesgue_absolutelyContinuous hD) (physicalCellIndicator D m)
    (physicalCellField_memLp hD hP m)).mkContinuousOfExistsBound (by
      obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
      have hB : 0 ≤ K * radialE (D.cellIndex m) ^ K :=
        mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _)
      exact ⟨Real.sqrt (K * radialE (D.cellIndex m) ^ K),
        physicalCellField_value_norm_le hD hP m hB (hbound m)⟩)).comp
          (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ)

theorem matchedPhysicalSourceFactor_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (f : MatchedPhysicalL2 D) :
    (matchedPhysicalSourceFactor D hD hP m f).1 =ᵐ[radialHilbertMeasure D]
      fun r => -((Function.support (D.localizer m)).indicator f r) / matchingDensity D r := by
  change (densityMultiplierValue (radialHilbertMeasure D)
    (volume.restrict (radialCore D)) (physicalCellSourceCoefficient D m)
    (physicalCellSource_memLp hD hP m) f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] _
  simpa only [physicalCellSourceCoefficient_mul] using
    densityMultiplierValue_ae (radialHilbertMeasure D) (volume.restrict (radialCore D))
      (physicalCellSourceCoefficient D m) (physicalCellSource_memLp hD hP m) f

@[simp] theorem matchedPhysicalSourceFactor_scalar {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (f : MatchedPhysicalL2 D) :
    (matchedPhysicalSourceFactor D hD hP m f).2 = 0 := rfl

theorem matchedPhysicalFieldFactor_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (U : RadialModePair D) :
    matchedPhysicalFieldFactor D hD hP m U =ᵐ[volume.restrict (radialCore D)]
      (Function.support (D.localizer m)).indicator U.1 := by
  change (densityMultiplierValue (volume.restrict (radialCore D))
    (radialHilbertMeasure D) (physicalCellIndicator D m)
    (physicalCellField_memLp hD hP m) U.1 : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] _
  simpa only [physicalCellIndicator_mul] using
    densityMultiplierValue_ae (volume.restrict (radialCore D)) (radialHilbertMeasure D)
      (physicalCellIndicator D m) (physicalCellField_memLp hD hP m) U.1

theorem norm_matchedPhysicalSourceFactor_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B) :
    ‖matchedPhysicalSourceFactor D hD hP m‖ ≤ Real.sqrt B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  change ‖(densityMultiplierValue (radialHilbertMeasure D)
    (volume.restrict (radialCore D)) (physicalCellSourceCoefficient D m)
    (physicalCellSource_memLp hD hP m) f, (0 : ℝ))‖ ≤ _
  rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  exact physicalCellSource_value_norm_le hD hP m hB hbound f

theorem norm_matchedPhysicalFieldFactor_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) (m : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ B) :
    ‖matchedPhysicalFieldFactor D hD hP m‖ ≤ Real.sqrt B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro U
  change ‖densityMultiplierValue (volume.restrict (radialCore D))
    (radialHilbertMeasure D) (physicalCellIndicator D m)
    (physicalCellField_memLp hD hP m) U.1‖ ≤ _
  exact (physicalCellField_value_norm_le hD hP m hB hbound U.1).trans
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg B))

/-- Composing the source factor with the actual modal localizer gives
the exact physical source conversion, without a squared localizer. -/
theorem matchedPhysicalCellSource_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (f : MatchedPhysicalL2 D) :
    (matchedModeCell D hP m (matchedPhysicalSourceFactor D hD hP m f)).1
      =ᵐ[radialHilbertMeasure D]
        fun r => -(D.localizer m r * f r) / matchingDensity D r := by
  filter_upwards [matchedModeCellL2_ae D hP m
    (matchedPhysicalSourceFactor D hD hP m f).1,
    matchedPhysicalSourceFactor_ae hD hP m f] with r hcell hsource
  change matchedModeCellL2 D hP m
    (matchedPhysicalSourceFactor D hD hP m f).1 r = _
  rw [hcell, hsource]
  by_cases hr : r ∈ Function.support (D.localizer m)
  · rw [Set.indicator_of_mem hr]
    ring
  · have hz : D.localizer m r = 0 := by
      by_contra hne
      exact hr hne
    simp only [hz, zero_mul, neg_zero, zero_div]

/-- The output factor after localization is the actual physical field. -/
theorem matchedPhysicalCellField_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (m : ℕ) (U : RadialModePair D) :
    matchedPhysicalFieldFactor D hD hP m (matchedModeCell D hP m U)
      =ᵐ[volume.restrict (radialCore D)] fun r => D.localizer m r * U.1 r := by
  filter_upwards [matchedPhysicalFieldFactor_ae hD hP m (matchedModeCell D hP m U),
    (radialHilbertMeasure_ae_iff hD).mp (matchedModeCellL2_ae D hP m U.1)]
      with r hfield hcell
  rw [hfield]
  by_cases hr : r ∈ Function.support (D.localizer m)
  · rw [Set.indicator_of_mem hr]
    exact hcell
  · have hz : D.localizer m r = 0 := by
      by_contra hne
      exact hr hne
    simp only [Set.indicator_of_notMem hr, hz, zero_mul]

/-- The physical block associated with the same modal inverse and cells. -/
def matchedPhysicalCellBlock (D : ReferenceData)
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ) :
    MatchedPhysicalL2 D →L[ℝ] MatchedPhysicalL2 D :=
  matchedPhysicalFieldFactor D hD hP k ∘L
    (matchedModeCell D hP k ∘L G ∘L matchedModeCell D hP m) ∘L
      matchedPhysicalSourceFactor D hD hP m

theorem matchedPhysicalCellBlock_norm_le {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D)
    (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ)
    {Bₖ Bₘ : ℝ} (hBₖ : 0 ≤ Bₖ) (hBₘ : 0 ≤ Bₘ)
    (hk : ∀ r ∈ D.cells k, (matchingDensity D r)⁻¹ ≤ Bₖ)
    (hm : ∀ r ∈ D.cells m, (matchingDensity D r)⁻¹ ≤ Bₘ) :
    ‖matchedPhysicalCellBlock D hD hP G k m‖ ≤
      Real.sqrt Bₖ * Real.sqrt Bₘ *
        ‖matchedModeCell D hP k ∘L G ∘L matchedModeCell D hP m‖ := by
  let A := matchedModeCell D hP k ∘L G ∘L matchedModeCell D hP m
  let R := matchedPhysicalFieldFactor D hD hP k
  let S := matchedPhysicalSourceFactor D hD hP m
  have hR : ‖R‖ ≤ Real.sqrt Bₖ := norm_matchedPhysicalFieldFactor_le hD hP k hBₖ hk
  have hS : ‖S‖ ≤ Real.sqrt Bₘ := norm_matchedPhysicalSourceFactor_le hD hP m hBₘ hm
  have hAS : ‖A ∘L S‖ ≤ ‖A‖ * Real.sqrt Bₘ :=
    (A.opNorm_comp_le S).trans (mul_le_mul_of_nonneg_left hS (norm_nonneg A))
  change ‖R ∘L A ∘L S‖ ≤ _
  exact (R.opNorm_comp_le (A ∘L S)).trans
    ((mul_le_mul hR hAS (norm_nonneg _) (Real.sqrt_nonneg _)).trans_eq (by dsimp only [A]; ring))

/-- The reciprocal-density loss is uniform over all cells and all
frequencies. No estimate of the inverse is assumed here. -/
theorem exists_matchedPhysicalCellBlock_cost {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hP : RadialPartition D) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ),
        ‖matchedPhysicalCellBlock D hD hP G k m‖ ≤
          Real.sqrt (K * radialE (D.cellIndex k) ^ K) *
            Real.sqrt (K * radialE (D.cellIndex m) ^ K) *
              ‖matchedModeCell D hP k ∘L G ∘L matchedModeCell D hP m‖ := by
  obtain ⟨K, hK, hbound⟩ := matchedDensity_inv_coefficient_bound hD
  refine ⟨K, hK, ?_⟩
  intro G k m
  exact matchedPhysicalCellBlock_norm_le hD hP G k m
    (mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _))
    (mul_nonneg hK.le (Real.rpow_nonneg (Real.exp_pos _).le _))
    (hbound k) (hbound m)

end ContinuousFlexibility.Radial
