import ContinuousFlexibility.Radial.MatchedOuterPhysicalRadiusState
import ContinuousFlexibility.Radial.MatchedOuterRadiusMeasure
import ContinuousFlexibility.Radial.MatchedOuterScaledRobinLine
import ContinuousFlexibility.Radial.SelectedFirstNaturalTransport
import ContinuousFlexibility.Radial.MatchedOuterModalCells
import ContinuousFlexibility.Radial.MatchedFiniteEnvelope

/-!
# Quantitative witnesses for the actual whole exterior problem

This proposition packages only existing objects: an actual physical
fundamental pair, its natural L² vector and its all-source Green operator.
The label reference is kept explicit because the retained reference may
have floored cell labels. No replacement inverse or measure is defined.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def MatchedOuterTailEnvelope (D E : ReferenceData) (hP : RadialPartition E)
    (right : Bool) (cut : ℝ) (j transition : ℕ) (C A : ℝ) : Prop :=
  let lam := standInBoundaryScale ((j : ℝ) ^ 2) (E.w cut) cut
  ∃ c : ℝ, ∃ P ZP Q ZQ : ℝ → ℝ,
    ∃ H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight E right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight E right) x / (lam * x))
      P ZP Q ZQ (outerOutwardRadius right cut) c
      (outerOutwardRadius right (tailPhysicalEndpoint E right)),
    ∃ hV : MemLp H.V 2 (outerWholeMeasure E right cut),
    ∃ R : OuterWholeL2 E right cut →L[ℝ] OuterWholeL2 E right cut,
      (∀ f, (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure E right cut] fun x =>
        ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure E right cut) ∧
      (∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → RadialNaturalTail E right j cut u →
        ∀ z, outerStatePair H.entrance z = 0 ↔
          outerStatePair (outerUnitState
            (selectedBoundaryState E j (r07OutwardSign right) cut u)) z = 0) ∧
      (∀ k m,
        ‖(matchedOuterCell E hP right (outerWholeMeasure E right cut) k).comp
          (R.comp (matchedOuterCell E hP right (outerWholeMeasure E right cut) m))‖ ≤
          C * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
            |radialS (D.cellIndex k) - radialS (D.cellIndex m)|)) ∧
      (∀ m, ‖matchedOuterCell E hP right (outerWholeMeasure E right cut) m
        ((sqrt lam)⁻¹ • hV.toLp H.V)‖ ≤
        C * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
          |radialS (D.cellIndex m) - radialS transition|))

theorem MatchedOuterTailEnvelope.mono
    {D E : ReferenceData} {hP : RadialPartition E} {right : Bool}
    {cut C C' A A' : ℝ} {j transition : ℕ}
    (h : MatchedOuterTailEnvelope D E hP right cut j transition C A)
    (hC : 0 ≤ C) (hCC : C ≤ C') (hAA : A ≤ A') :
    MatchedOuterTailEnvelope D E hP right cut j transition C' A' := by
  obtain ⟨c, P, ZP, Q, ZQ, H, hV, R, hR, hline, hkernel, hcolumn⟩ := h
  refine ⟨c, P, ZP, Q, ZQ, H, hV, R, hR, hline, ?_, ?_⟩
  · intro k m
    exact (hkernel k m).trans (matchedEnvelope_mono hC hCC hAA _ _)
  · intro m
    exact (hcolumn m).trans (matchedEnvelope_mono hC hCC hAA _ _)

/-- Transport the same proved physical pair and all-source kernel. The
two quantitative premises are supplied by the actual selected or fixed
frequency kernel estimates, before this adapter is used. -/
theorem matchedOuterTailEnvelope_of_radius_data
    {M : MorseChainData} {D E : ReferenceData} {right : Bool} {j start : ℕ}
    {deep η K cut lam κ β C A : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (hD : IsAccumulatingProfile D) (hE : IsAccumulatingProfile E)
    (hP : RadialPartition E) (hj : 2 ≤ j)
    (hcut : cut ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (hac : outerOutwardRadius right cut < outerOutwardRadius right deep)
    (hlam : 0 < lam)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start deep η K) right j start)
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right cut) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hV : MemLp H.V 2 (outerWholeMeasure D right cut))
    (R : OuterWholeL2 D right cut →L[ℝ] OuterWholeL2 D right cut)
    (hR : ∀ f, (R f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right cut] fun x =>
      ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure D right cut)
    (hκ : 0 < κ) (hβ : 0 < β) (hcutE : κ * cut ∈ radialCore E)
    (hend : tailPhysicalEndpoint E right = κ * tailPhysicalEndpoint D right)
    (hprofile : ∀ r ∈ radialTailInterval D right cut,
      E.w (κ * r) = (β * κ) * D.w r)
    (hprofileCut : E.w (κ * cut) = (β * κ) * D.w cut)
    (hscale : standInBoundaryScale ((j : ℝ) ^ 2) (E.w (κ * cut)) (κ * cut) = β * lam)
    (transition : ℕ)
    (hkernel : ∀ k m,
      ‖(matchedOuterCell E hP right (outerWholeMeasure E right (κ * cut)) k).comp
        ((inverseRadiusOperator hκ.ne' hβ
          (outerWholeMeasure_radiusScale hκ hβ hcut hcutE hend hprofile) R).comp
          (matchedOuterCell E hP right (outerWholeMeasure E right (κ * cut)) m))‖ ≤
        C * exp (A * (radialQ (D.cellIndex k) + radialQ (D.cellIndex m)) -
          |radialS (D.cellIndex k) - radialS (D.cellIndex m)|))
    (hcolumn : ∀ U : OuterWholeL2 E right (κ * cut),
      (U : ℝ → ℝ) =ᵐ[outerWholeMeasure E right (κ * cut)]
        (fun x => H.V (x / κ) / sqrt (β * lam)) →
      ∀ m, ‖matchedOuterCell E hP right (outerWholeMeasure E right (κ * cut)) m U‖ ≤
        C * exp (A * (radialQ (D.cellIndex m) + radialQ transition) -
          |radialS (D.cellIndex m) - radialS transition|)) :
    MatchedOuterTailEnvelope D E hP right (κ * cut) j transition C A := by
  let H' := H.physicalRadiusScale hD hE hκ hβ hlam.ne' hcut hend hprofile hprofileCut
  have hV' : MemLp H'.V 2 (outerWholeMeasure E right (κ * cut)) :=
    outerWhole_memLp_radiusScale hκ hβ hcut hcutE hend hprofile hV
  let R' := inverseRadiusOperator hκ.ne' hβ
    (outerWholeMeasure_radiusScale hκ hβ hcut hcutE hend hprofile) R
  unfold MatchedOuterTailEnvelope
  rw [hscale]
  refine ⟨outerOutwardRadius right (κ * deep), (fun x => F.P (x / κ)),
    (fun x => F.ZP lam (x / κ)), (fun x => F.Q (x / κ)),
    (fun x => F.ZQ lam (x / κ)), H', hV', R', ?_, ?_, hkernel, ?_⟩
  · exact outerWhole_inverseRadiusOperator_kernel hκ hβ hcut hcutE hend hprofile
      R lam H.U H.V hR
  · intro u hu hN z
    have hjn : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have hsign : r07OutwardSign right = outerTailSign right := by cases right <;> rfl
    have hne := selectedBoundaryState_ne_zero_of_natural (ε := r07OutwardSign right)
      (matchingProfileGeometry hE) hjn hcutE
      (by cases right <;> norm_num [r07OutwardSign]) hu hN
    have hrobin := F.scaledNatural_robin_iff (E := E) (κ := κ) (β := β)
      hD hcut hdeep (by simpa only [outerOutwardRadius_eq_sign] using hac)
      hlam.ne' hT hphysical hη hK
    rw [← outerOutwardRadius_eq_sign right cut,
      ← outerOutwardRadius_eq_sign right deep,
      ← outerOutwardRadius_eq_sign right (tailPhysicalEndpoint D right)] at hrobin
    have hi := hrobin H hκ hβ hcutE hend hprofile hprofileCut hu hN
      (by simpa only [selectedBoundaryState, outerFluxState, hsign, hscale] using hne) z
    simpa only [selectedBoundaryState, outerFluxState, hsign, hscale] using hi
  · have hVeq : H'.V = fun x => H.V (x / κ) :=
      (H.physicalRadiusScale_fields hD hE hκ hβ hlam.ne' hcut hend
        hprofile hprofileCut).2.2.1
    have hnormalized :
        (((sqrt (β * lam))⁻¹ • hV'.toLp H'.V : OuterWholeL2 E right (κ * cut)) : ℝ → ℝ)
          =ᵐ[outerWholeMeasure E right (κ * cut)]
            fun x => H.V (x / κ) / sqrt (β * lam) := by
      filter_upwards [Lp.coeFn_smul (sqrt (β * lam))⁻¹ (hV'.toLp H'.V), hV'.coeFn_toLp]
        with x hs hx
      rw [hs]
      change (sqrt (β * lam))⁻¹ * (hV'.toLp H'.V) x = H.V (x / κ) / sqrt (β * lam)
      rw [hx, congrFun hVeq x]
      exact (mul_comm (sqrt (β * lam))⁻¹ (H.V (x / κ))).trans
        (div_eq_mul_inv (H.V (x / κ)) (sqrt (β * lam))).symm
    exact hcolumn ((sqrt (β * lam))⁻¹ • hV'.toLp H'.V) hnormalized

end ContinuousFlexibility.Radial
