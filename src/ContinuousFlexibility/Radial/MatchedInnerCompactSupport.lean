import ContinuousFlexibility.Radial.MatchingGraphRestrictions
import ContinuousFlexibility.Radial.MatchedPhysicalChannelComparison
import ContinuousFlexibility.Radial.MatchedPhysicalScalarGate

/-!
# Exact compact support of the existing inner channels

The frozen local realizations already make the inner inverse and
inner Poisson columns vanish outside the two cuts. An actual localizer
which vanishes on that compact interval therefore gives the zero output
channel, or the zero restricted input. These are equalities of the
original L² elements and operators.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory ContinuousFlexibility.Statements

private theorem matchedInner_supported_of_outer_imp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D) (U : RadialModePair D)
    (hzero : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ matchingOuterRegion D M → U.1 r = 0) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Icc M.innerLeft M.innerRight → U.1 r = 0 := by
  have hcore : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ radialCore D :=
    (radialHilbertMeasure_ae_iff hD).mpr (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hzero, hcore] with r hz hr
  intro hout
  apply hz
  rcases lt_or_ge r M.innerLeft with hleft | hleft
  · exact Or.inl ⟨hr.1, hleft⟩
  · exact Or.inr ⟨lt_of_not_ge (fun hright => hout ⟨hleft, hright⟩), hr.2⟩

theorem matchedInnerInverse_field_supported {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) (F : RadialModePair D) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Icc M.innerLeft M.innerRight →
      (M.innerInverse (M.sourceInner F)).1 r = 0 := by
  rcases hM.2.2.2.2.1 F with ⟨hrep, _, _, _, _, _, hzero, _⟩
  apply matchedInner_supported_of_outer_imp hD M
  filter_upwards [hrep] with r hr
  intro hout
  rw [hr, hzero r hout]

theorem matchedInnerPoisson_field_supported {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) (i : Fin 2) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Icc M.innerLeft M.innerRight →
      (M.innerPoisson i).1 r = 0 :=
  matchedInner_supported_of_outer_imp hD M (M.innerPoisson i)
    (ae_imp_of_ae_restrict (hM.2.2.2.2.2 i).2.2.1)

/-- This uses the actual localizer, with no assumption on an enlarged
cell set. The scalar component of a field channel is already zero. -/
theorem matchedModeCell_eq_zero_of_compact_support {D : ReferenceData}
    (hP : RadialPartition D) {K : Set ℝ} (m : ℕ) (U : RadialModePair D)
    (hlocal : ∀ r ∈ K, D.localizer m r = 0)
    (hU : ∀ᵐ r ∂radialHilbertMeasure D, r ∉ K → U.1 r = 0) :
    matchedModeCell D hP m U = 0 := by
  apply Prod.ext
  · change matchedModeCellL2 D hP m U.1 = 0
    apply Lp.ext
    filter_upwards [matchedModeCellL2_ae D hP m U.1, hU,
      Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hcell hu hzero
    rw [hcell, hzero]
    by_cases hr : r ∈ K
    · rw [hlocal r hr, zero_mul]
    · rw [hu hr, mul_zero]
  · rfl

/-- An inactive actual field localizer gives a zero restricted source,
also after the existing scalar gate. -/
theorem matchedInnerSource_cell_eq_zero {D : ReferenceData}
    (hP : RadialPartition D) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) (active : Bool) (m : ℕ)
    (hlocal : ∀ r ∈ Icc M.innerLeft M.innerRight, D.localizer m r = 0)
    (F : RadialModePair D) :
    M.sourceInner (matchedModeScalarGate D active (matchedModeCell D hP m F)) = 0 := by
  have hgate : matchedModeScalarGate D active (matchedModeCell D hP m F) =
      matchedModeCell D hP m F :=
    matchedModeScalarGate_eq_self D active _ (fun _ => rfl)
  rw [hgate]
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(hM.2.2.2.1 (matchedModeCell D hP m F)).2.2.1,
      matchedModeCellL2_ae D hP m F.1, Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)]
      with r hsource hcell hzero
    change (M.sourceInner (matchedModeCell D hP m F)).1 r = (0 : RadialModeL2 D) r
    rw [hsource, hzero]
    by_cases hr : r ∈ Ioo M.innerLeft M.innerRight
    · rw [if_pos hr]
      change (matchedModeCellL2 D hP m F.1) r = 0
      rw [hcell, hlocal r (Ioo_subset_Icc_self hr), zero_mul]
    · rw [if_neg hr]
  · change (M.sourceInner (matchedModeCell D hP m F)).2 = 0
    rw [(hM.2.2.2.1 _).1]
    rfl

theorem matchedCompact_channel_norm_apply_le (D : ReferenceData) (hP : RadialPartition D)
    (k : ℕ) (U : RadialModePair D) : ‖matchedModeChannel D hP k U‖ ≤ ‖U‖ := by
  cases k with
  | zero =>
      change ‖matchedModeBorder D U‖ ≤ ‖U‖
      rw [matchedModeBorder_norm, Prod.norm_def]
      exact le_max_right _ _
  | succ m => exact matchedModeCell_norm_apply_le D hP m U

/-- Localization does not increase the norm of the given operator. -/
theorem matchedCompact_channel_block_norm_le (D : ReferenceData) (hP : RadialPartition D)
    (A : RadialModePair D →L[ℝ] RadialModePair D) (k m : ℕ) :
    ‖matchedModeChannel D hP k ∘L A ∘L matchedModeChannel D hP m‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro F
  change ‖matchedModeChannel D hP k (A (matchedModeChannel D hP m F))‖ ≤ ‖A‖ * ‖F‖
  exact (matchedCompact_channel_norm_apply_le D hP k _).trans
    ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (matchedCompact_channel_norm_apply_le D hP m F) (norm_nonneg A)))

end ContinuousFlexibility.Radial
