import ContinuousFlexibility.Radial.MatchedOuterWholeHilbert
import ContinuousFlexibility.Radial.MatchedOuterPhysicalFlux
import ContinuousFlexibility.Radial.MatchedOuterTraceTransport

/-!
# The actual normalized outer natural columns

The column is the existing whole-tail natural L² vector, divided by the
square root of the unchanged boundary scale and extended by the existing
physical extension. Its representative uses the same natural function
on its side and zero on the other side and the open inner interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

def matchedOuterNaturalPoisson (D : ReferenceData) (right : Bool) (entry lam : ℝ)
    (V : ℝ → ℝ) (hV : MemLp V 2 (outerWholeMeasure D right entry)) :
    RadialModePair D :=
  (matchedOuterWholeExtend D right entry ((sqrt lam)⁻¹ • hV.toLp V), 0)

def matchedOuterNaturalFunction {D : ReferenceData} (M : RadialMatchingData D)
    (right : Bool) (lam : ℝ) (V : ℝ → ℝ) : ℝ → ℝ :=
  if right then
    matchedOuterSideGlue M.innerLeft M.innerRight (fun _ => 0)
      (fun r => V (outerOutwardRadius right r) / sqrt lam)
  else
    matchedOuterSideGlue M.innerLeft M.innerRight
      (fun r => V (outerOutwardRadius right r) / sqrt lam) (fun _ => 0)

theorem matchedOuterNaturalPoisson_scalar (D : ReferenceData) (right : Bool)
    (entry lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right entry)) :
    (matchedOuterNaturalPoisson D right entry lam V hV).2 = 0 := rfl

theorem matchedOuterNaturalPoisson_ae (D : ReferenceData) (right : Bool)
    (entry lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right entry)) :
    ((matchedOuterNaturalPoisson D right entry lam V hV).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D]
      (radialTailInterval D right entry).indicator
        (fun r => V (outerOutwardRadius right r) / sqrt lam) := by
  apply matchedOuterWholeExtend_representative
  filter_upwards [Lp.coeFn_smul (sqrt lam)⁻¹ (hV.toLp V), hV.coeFn_toLp] with x hs hx
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hx, div_eq_mul_inv, mul_comm]

theorem matchedOuterNaturalPoisson_ae_on (D : ReferenceData) (right : Bool)
    (entry lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right entry)) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ radialTailInterval D right entry) :
    ((matchedOuterNaturalPoisson D right entry lam V hV).1 : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict s]
        fun r => V (outerOutwardRadius right r) / sqrt lam := by
  filter_upwards [(matchedOuterNaturalPoisson_ae D right entry lam V hV).filter_mono
      (Measure.restrict_le_self).ae_le, ae_restrict_mem hs] with r hr hrs
  exact hr.trans (indicator_of_mem (hsub hrs) _)

theorem matchedOuterNaturalPoisson_ae_zero_on (D : ReferenceData) (right : Bool)
    (entry lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right entry)) {s : Set ℝ}
    (hs : MeasurableSet s) (hdisjoint : ∀ r ∈ s, r ∉ radialTailInterval D right entry) :
    ((matchedOuterNaturalPoisson D right entry lam V hV).1 : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict s] fun _ => 0 := by
  filter_upwards [(matchedOuterNaturalPoisson_ae D right entry lam V hV).filter_mono
      (Measure.restrict_le_self).ae_le, ae_restrict_mem hs] with r hr hrs
  exact hr.trans (indicator_of_notMem (hdisjoint r hrs) _)

theorem matchedOuterNaturalFunction_inner {D : ReferenceData} (M : RadialMatchingData D)
    (right : Bool) (lam : ℝ) (V : ℝ → ℝ) {r : ℝ}
    (hr : r ∈ Ioo M.innerLeft M.innerRight) :
    matchedOuterNaturalFunction M right lam V r = 0 := by
  cases right
  · exact matchedOuterSideGlue_inner _ _ hr
  · exact matchedOuterSideGlue_inner _ _ hr

theorem matchedOuterNaturalFunction_contDiffOn {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    (right : Bool) (lam : ℝ) (V : ℝ → ℝ) {n : ℕ∞ω}
    (hu : ContDiffOn ℝ n (fun x => V x / sqrt lam)
      (Ico (outerOutwardRadius right (if right then M.innerRight else M.innerLeft))
        (outerOutwardRadius right (tailPhysicalEndpoint D right)))) :
    ContDiffOn ℝ n (matchedOuterNaturalFunction M right lam V)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
  have hp := matchedOuterWhole_contDiff_physical hu
  cases right
  · exact matchedOuterSideGlue_contDiffOn hm hp contDiffOn_const
  · exact matchedOuterSideGlue_contDiffOn hm contDiffOn_const hp

theorem matchedOuterNaturalPoisson_inner_zero {D : ReferenceData}
    (M : RadialMatchingData D) (right : Bool) (lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft))) :
    ((matchedOuterNaturalPoisson D right
      (if right then M.innerRight else M.innerLeft) lam V hV).1 : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)]
        fun _ => 0 := by
  apply matchedOuterNaturalPoisson_ae_zero_on _ _ _ _ _ _ measurableSet_Ioo
  intro r hr ht
  cases right
  · exact (not_lt_of_gt hr.1) ht.2
  · exact (not_lt_of_gt hr.2) ht.1

theorem matchedOuterNaturalPoisson_other_zero {D : ReferenceData}
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    (right : Bool) (lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft))) :
    ((matchedOuterNaturalPoisson D right
      (if right then M.innerRight else M.innerLeft) lam V hV).1 : ℝ → ℝ)
      =ᵐ[(radialHilbertMeasure D).restrict
        (radialTailInterval D (!right) (if right then M.innerLeft else M.innerRight))]
        fun _ => 0 := by
  apply matchedOuterNaturalPoisson_ae_zero_on _ _ _ _ _ _
    (by cases right <;> exact measurableSet_Ioo)
  intro r hr ht
  cases right
  · exact (not_lt_of_gt (hm.trans hr.1)) ht.2
  · exact (not_lt_of_gt (hr.2.trans hm)) ht.1

theorem matchedOuterNaturalPoisson_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (hm : M.innerLeft < M.innerRight) (right : Bool) (lam : ℝ) (V : ℝ → ℝ)
    (hV : MemLp V 2 (outerWholeMeasure D right
      (if right then M.innerRight else M.innerLeft))) :
    ((matchedOuterNaturalPoisson D right
      (if right then M.innerRight else M.innerLeft) lam V hV).1 : ℝ → ℝ)
      =ᵐ[radialHilbertMeasure D] matchedOuterNaturalFunction M right lam V := by
  have hactive := matchedOuterNaturalPoisson_ae_on D right
    (if right then M.innerRight else M.innerLeft) lam V hV
    (by cases right <;> exact measurableSet_Ioo) (Subset.refl _)
  have hother := matchedOuterNaturalPoisson_other_zero hm right lam V hV
  have hinner := matchedOuterNaturalPoisson_inner_zero M right lam V hV
  cases right
  · exact matchedOuterSideGlue_representative hD hm hactive hother hinner
  · exact matchedOuterSideGlue_representative hD hm hother hactive hinner

private theorem matchedOuterNatural_flux_scale {lam w z : ℝ}
    (hlam : 0 < lam) (hw : w ≠ 0) :
    w * (lam / w * (z / sqrt lam)) / sqrt lam = z := by
  have hs : sqrt lam ≠ 0 := (sqrt_pos.mpr hlam).ne'
  calc
    _ = lam * z / (sqrt lam) ^ 2 := by field_simp [hw, hs]; ring
    _ = z := by rw [sq_sqrt hlam.le]; field_simp [hlam.ne']

/-- Smoothness, the original weak flux equation and normalized entrance
state follow from the actual first-order solution; there is no boundary
value division. -/
theorem matchedOuterNatural_state {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {right : Bool} {entry c lam : ℝ} {j : ℕ}
    (hentry : entry ∈ radialCore D) (hlam : 0 < lam)
    {P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right entry) c
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    ContDiffOn ℝ ∞ (fun x => H.V x / sqrt lam)
        (Ico (outerOutwardRadius right entry)
          (outerOutwardRadius right (tailPhysicalEndpoint D right))) ∧
      HasIntervalWeakDerivative (outerOutwardRadius right entry)
        (outerOutwardRadius right (tailPhysicalEndpoint D right))
        (fun x => outerTailOutwardWeight D right x *
          deriv (fun y => H.V y / sqrt lam) x)
        (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / x *
          (H.V x / sqrt lam)) ∧
      H.V (outerOutwardRadius right entry) / sqrt lam = H.entrance.1 / sqrt lam ∧
      D.w entry *
        derivWithin (fun x => H.V x / sqrt lam)
          (Ico (outerOutwardRadius right entry)
            (outerOutwardRadius right (tailPhysicalEndpoint D right)))
          (outerOutwardRadius right entry) / sqrt lam = H.entrance.2 := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let w := outerTailOutwardWeight D right
  let u : ℝ → ℝ := fun x => H.V x / sqrt lam
  let z : ℝ → ℝ := fun x => H.ZV x / sqrt lam
  have hab : a < b := outerWhole_interval hentry
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hwne : ∀ x ∈ Ico a b, w x ≠ 0 :=
    fun x hx => (outerWhole_weight_pos (matchingProfileGeometry hD) hentry hx).ne'
  have hxne : ∀ x ∈ Ico a b, x ≠ 0 :=
    fun x hx => outerWhole_coordinate_ne_zero (matchingProfileGeometry hD) hentry hx
  have hs : OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => (j : ℝ) ^ 2 * deriv w x / (lam * x)) u z (Ico a b) := by
    simpa only [u, z, div_eq_mul_inv, mul_comm] using H.V_system.const_mul (sqrt lam)⁻¹
  have hc := outerWhole_coefficients_smooth (right := right) (J := (j : ℝ) ^ 2)
    (matchingProfileGeometry hD) hentry hlam.ne'
  have hreg := hs.contDiffOn (uniqueDiffOn_Ico a b) hc.1 hc.2
  have hweak : HasIntervalWeakDerivative a b (fun x => lam * z x)
      (fun x => lam * ((j : ℝ) ^ 2 * deriv w x / (lam * x) * u x)) := by
    apply hasIntervalWeakDerivative_of_locallyAC_ae hab
    · intro l hl r hr
      exact (((contDiffOn_const.mul hreg.2).of_le (by simp)).mono
        ((ordConnected_Ioo.uIcc_subset hl hr).trans Ioo_subset_Ico_self)).absolutelyContinuousOnInterval
    · intro l hl r hr
      exact ae_of_all _ (fun x hx =>
        ((hs x (Ioo_subset_Ico_self (ordConnected_Ioo.uIcc_subset hl hr hx))).2.const_mul lam))
  refine ⟨hreg.1, ?_, ?_, ?_⟩
  · apply hweak.congr_restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (outerFirstOrderSystem_physical_flux hs hwne x (Ioo_subset_Ico_self hx)).symm
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      dsimp only
      field_simp [hlam.ne', hxne x (Ioo_subset_Ico_self hx)]
      ring
  · rw [show H.V a = H.entrance.1 from congrArg Prod.fst H.V_initial]
  · have hwa : w a = D.w entry := by
      cases right <;> simp [w, a, outerTailOutwardWeight, outerTailSign, outerOutwardRadius]
    have hd := (hs a ha).1.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ico a b a ha)
    change D.w entry * derivWithin u (Ico a b) a / sqrt lam = H.entrance.2
    rw [hd, ← hwa]
    exact (matchedOuterNatural_flux_scale hlam (hwne a ha)).trans
      (congrArg Prod.snd H.V_initial)

end ContinuousFlexibility.Radial
