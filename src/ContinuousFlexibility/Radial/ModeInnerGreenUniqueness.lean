import ContinuousFlexibility.Radial.ModeWeakGreen
import ContinuousFlexibility.Radial.ModeInnerSourcePairing
import ContinuousFlexibility.Radial.ModeRegionWeakEquation

/-!
# The actual inner right inverse determines every frozen weak solution

The finite Green identity applies to the C1 representatives required by
the frozen graph, even for arbitrary L2 forcing. The endpoint values and
the actual scalar rows make this graph symmetric. Pairing the difference
of two solutions with a right-inverse solution proves uniqueness without
assuming that the arbitrary frozen solution lies in another energy domain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem modeInnerDirichletGraph_source_fixed {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    {U F : RadialModePair D} (hU : ModeInnerDirichletGraph D M U F) :
    modeInnerSource D M.innerLeft M.innerRight U = U := by
  obtain ⟨u, hrep, _, hout, _, _⟩ := hU.2.2
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(modeRegionSources_spec D M.innerLeft M.innerRight U).2.2.1,
      hrep, matching_ae_inner_or_outer hD M] with r hsrc hr hloc
    rcases hloc with hin | houter
    · rw [hsrc, if_pos hin]
    · rw [hsrc, if_neg (matchingOuterRegion_not_mem_inner houter), hr, hout r houter]
  · exact (modeRegionSources_spec D M.innerLeft M.innerRight U).1

/-- The source indicator changes neither the local equation nor its scalar row. -/
theorem modeInnerDirichletGraph_modeInnerSource_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D} {U F : RadialModePair D} :
    ModeInnerDirichletGraph D M U (modeInnerSource D M.innerLeft M.innerRight F) ↔
      ModeInnerDirichletGraph D M U F := by
  constructor
  · rintro ⟨he, hr, hu⟩
    refine ⟨(modeLocalEquation_modeInnerSource_iff hD).mp he, ?_, hu⟩
    simpa only [modeInnerSource] using hr
  · rintro ⟨he, hr, hu⟩
    refine ⟨(modeLocalEquation_modeInnerSource_iff hD).mpr he, ?_, hu⟩
    simpa only [modeInnerSource] using hr

private theorem inner_field_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h : ℝ} (hlh : l ≤ h)
    (hsub : Icc l h ⊆ radialCore D) (U F : RadialModePair D)
    (hfix : modeInnerSource D l h U = U) :
    (∫ r in l..h, matchingDensity D r * U.1 r * F.1 r) = ⟪U.1, F.1⟫_ℝ := by
  rw [matchingMode_inner_eq_integral hD]
  calc
    _ = ∫ r in l..h, (matchingDensity D r * F.1 r) * U.1 r := by
      apply intervalIntegral.integral_congr
      intro r _
      ring
    _ = ∫ r in D.a..D.b, (matchingDensity D r * F.1 r) * U.1 r :=
      (modeInnerSource_integral_fixed hD hlh hsub U hfix
        (fun r => matchingDensity D r * F.1 r)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r _
      ring

/-- Green symmetry of the frozen graph follows from its true differential
equation, its actual border row and its two zero boundary values. -/
theorem modeInnerDirichletGraph_green {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    {U F V K : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) (hV : ModeInnerDirichletGraph D M V K) :
    modePairing D U K = modePairing D V F := by
  have hUfix := modeInnerDirichletGraph_source_fixed hD hU
  have hVfix := modeInnerDirichletGraph_source_fixed hD hV
  rcases hU with ⟨heU, hrU, u, hu, huc, _, hul, huh⟩
  rcases hV with ⟨heV, hrV, v, hv, hvc, _, hvl, hvh⟩
  have hgreen := modeLocalEquation_green_pair_on_compact hD hB heU heV hu hv
    hlh hsub (fun _ hx => hx) huc hvc
  simp only [huh, hvh, hul, hvl, zero_mul, sub_self] at hgreen
  have hI :
      (∫ r in M.innerLeft..M.innerRight,
        U.1 r * (V.2 * referenceColumn D r - matchingDensity D r * K.1 r) -
          V.1 r * (U.2 * referenceColumn D r - matchingDensity D r * F.1 r)) = 0 := by
    calc
      _ = ∫ r in M.innerLeft..M.innerRight,
          u r * (V.2 * referenceColumn D r - matchingDensity D r * K.1 r) -
            v r * (U.2 * referenceColumn D r - matchingDensity D r * F.1 r) := by
        apply matchingSubinterval_congr_ae hD hlh.le hsub
        filter_upwards [hu, hv] with r hur hvr
        simp only [hur, hvr]
      _ = 0 := hgreen
  have hinterval : uIcc M.innerLeft M.innerRight ⊆ uIcc D.a D.b := by
    rw [uIcc_of_le hlh.le, uIcc_of_le (matchingProfileGeometry hD).2.1.le]
    exact hsub.trans Ioo_subset_Icc_self
  have hi (Y Z : RadialModeL2 D) :
      IntervalIntegrable (fun r => matchingDensity D r * Y r * Z r)
        volume M.innerLeft M.innerRight :=
    (matchingModeProduct_intervalIntegrable hD Y Z).mono_set hinterval
  have hc (Y : RadialModeL2 D) :
      IntervalIntegrable (fun r => referenceColumn D r * Y r)
        volume M.innerLeft M.innerRight := by
    apply (matchingMode_intervalIntegrable hD Y hlh.le hsub).continuousOn_mul
    rw [uIcc_of_le hlh.le]
    exact (matchingColumn_continuousOn hD hB).mono (hsub.trans Ioo_subset_Icc_self)
  have hexpand :
      (∫ r in M.innerLeft..M.innerRight,
        U.1 r * (V.2 * referenceColumn D r - matchingDensity D r * K.1 r) -
          V.1 r * (U.2 * referenceColumn D r - matchingDensity D r * F.1 r)) =
      V.2 * (∫ r in M.innerLeft..M.innerRight, referenceColumn D r * U.1 r) -
        (∫ r in M.innerLeft..M.innerRight, matchingDensity D r * U.1 r * K.1 r) -
        (U.2 * (∫ r in M.innerLeft..M.innerRight, referenceColumn D r * V.1 r) -
          ∫ r in M.innerLeft..M.innerRight, matchingDensity D r * V.1 r * F.1 r) := by
    calc
      _ = ∫ r in M.innerLeft..M.innerRight,
          (V.2 * (referenceColumn D r * U.1 r) - matchingDensity D r * U.1 r * K.1 r) -
            (U.2 * (referenceColumn D r * V.1 r) - matchingDensity D r * V.1 r * F.1 r) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hc U.1).const_mul V.2 |>.sub (hi U.1 K.1))
          ((hc V.1).const_mul U.2 |>.sub (hi V.1 F.1)),
          intervalIntegral.integral_sub ((hc U.1).const_mul V.2) (hi U.1 K.1),
          intervalIntegral.integral_sub ((hc V.1).const_mul U.2) (hi V.1 F.1),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hexpand, inner_field_pairing hD hlh.le hsub U K hUfix,
    inner_field_pairing hD hlh.le hsub V F hVfix,
    ← modeInnerSource_integral_fixed hD hlh.le hsub U hUfix (referenceColumn D),
    ← modeInnerSource_integral_fixed hD hlh.le hsub V hVfix (referenceColumn D)] at hI
  by_cases hj : M.frequency = 2
  · simp only [hj, ite_true] at hrU hrV
    rw [hrU, hrV] at hI
    unfold modePairing
    linarith only [hI]
  · simp only [if_neg hj] at hrU hrV
    simp only [modePairing, hrU.1, hrU.2, hrV.1, hrV.2, zero_mul, mul_zero, add_zero] at hI ⊢
    linarith only [hI]

theorem modePairing_self_eq_zero_iff {D : ReferenceData} (U : RadialModePair D) :
    modePairing D U U = 0 ↔ U = 0 := by
  constructor
  · intro h
    change ⟪U.1, U.1⟫_ℝ + U.2 * U.2 = 0 at h
    have hf : 0 ≤ ⟪U.1, U.1⟫_ℝ := real_inner_self_nonneg
    have hz : ⟪U.1, U.1⟫_ℝ = 0 := by nlinarith only [h, hf, sq_nonneg U.2]
    have hu : U.1 = 0 := inner_self_eq_zero.mp hz
    rw [hz, zero_add] at h
    exact Prod.ext hu (mul_self_eq_zero.mp h)
  · rintro rfl
    simp only [modePairing, Prod.fst_zero, Prod.snd_zero, inner_zero_left, mul_zero, add_zero]

/-- A true right inverse is automatically the left inverse on every frozen
inner graph element. No density or regularity premise is added to that graph. -/
theorem modeInnerDirichletGraph_unique_of_right_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (hG : ∀ F, (M.frequency ≠ 2 → F.2 = 0) → ModeInnerDirichletGraph D M (G F) F)
    {U F : RadialModePair D} (hU : ModeInnerDirichletGraph D M U F) : G F = U := by
  have hF : M.frequency ≠ 2 → F.2 = 0 := by
    intro hj
    exact (by simpa only [if_neg hj] using hU.2.1 : U.2 = 0 ∧ F.2 = 0).2
  have hV := hG F hF
  let W : RadialModePair D := U - G F
  have hW : M.frequency ≠ 2 → W.2 = 0 := by
    intro hj
    have hu := (by simpa only [if_neg hj] using hU.2.1 : U.2 = 0 ∧ F.2 = 0).1
    have hv := (by simpa only [if_neg hj] using hV.2.1 : (G F).2 = 0 ∧ F.2 = 0).1
    simp only [W, Prod.snd_sub, hu, hv, sub_self]
  have hZ := hG W hW
  have h₁ := modeInnerDirichletGraph_green hD hB hlh hsub hU hZ
  have h₂ := modeInnerDirichletGraph_green hD hB hlh hsub hV hZ
  have hz : modePairing D W W = 0 := by
    change modePairing D (U - G F) W = 0
    rw [modePairing_sub_left, h₁, h₂, sub_self]
  exact (sub_eq_zero.mp ((modePairing_self_eq_zero_iff W).mp hz)).symm

/-- The projected right-inverse output supplied by the physical construction
has the same uniqueness consequence on arbitrary ambient forcing. -/
theorem modeInnerDirichletGraph_unique_of_projected_right_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hlh : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (G : RadialModePair D →L[ℝ] RadialModePair D)
    (hsource : ∀ F, G (modeInnerSource D M.innerLeft M.innerRight F) = G F)
    (hG : ∀ F, (M.frequency ≠ 2 → F.2 = 0) →
      ModeInnerDirichletGraph D M (G (modeInnerSource D M.innerLeft M.innerRight F))
        (modeInnerSource D M.innerLeft M.innerRight F))
    {U F : RadialModePair D} (hU : ModeInnerDirichletGraph D M U F) : G F = U := by
  apply modeInnerDirichletGraph_unique_of_right_inverse hD hB hlh hsub G _ hU
  intro H hH
  have hh := (modeInnerDirichletGraph_modeInnerSource_iff hD).mp (hG H hH)
  simpa only [hsource H] using hh

end ContinuousFlexibility.Radial
