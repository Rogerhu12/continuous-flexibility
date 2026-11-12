import ContinuousFlexibility.Analysis.CanonicalRootTravelDomain
import ContinuousFlexibility.Analysis.RootAiryCoordinateIdentification
import ContinuousFlexibility.Analysis.CharacteristicPairMaterialJets
import ContinuousFlexibility.Analysis.AiryInteriorChartMaterialJets
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Actual negative chart jets from the two actual first integrals

The true chart is recovered on its actual open domain by inverting the
Airy travel coordinate. Both radial orientations use the same estimates:
subtracting travel from the terminal constant changes no positive jet
norm. The low order and derivative loss precede every component and
every positive travel interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem canonicalCutPair_chart_eq_rootTravel
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) {q : PolarPoint}
    (hq : q ∈ physicalPieceOpen S K z
      (if side then (K.cutPair m).2 else (K.cutPair m).1)) :
    K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1) q =
      (rootTravelPower (canonicalGluedRootTravel S K z m side q),
        (canonicalGluedAiryIntegral S K z m 1 q +
          canonicalGluedAiryIntegral S K z m (-1) q) / 2) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hvalues := canonicalCutPair_chartValues_of_gluedIntegrals
    m side (hB.1.2 z hz hs m).2.2.1 hq
  obtain ⟨_, _, _, _, _, _, hl₀, hl₁, _, _⟩ := hB.1.1 m
  have hl : K.left i = 0 := by cases side <;> assumption
  have hξ : 0 < (K.chart z i q).1 := by
    simpa only [hl] using ((hA.charts z hz hs i).1 hq).1.1
  apply Prod.ext
  · calc
      _ = rootTravelPower (airyTravelPrimitive (K.chart z i q).1) :=
        (rootTravelPower_airyTravelPrimitive hξ.le).symm
      _ = _ := congrArg rootTravelPower hvalues.2
  · exact hvalues.1

/-- The quantitative inputs are the actual transported labels. The
actual chart and its full positive jet tower are conclusions. -/
theorem n03_cutPair_interiorChart_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (hS : IsPhysicalSpaces D T S)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      ∀ l u : ℝ, 0 < l → l ≤ u →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m : ℕ, ∀ side : Bool, ∀ q : PolarPoint,
      q ∈ physicalPieceOpen S K z (if side then (K.cutPair m).2 else (K.cutPair m).1) →
      (∀ plus : Bool,
        ContDiffAt ℝ ∞ (canonicalGluedAiryIntegral S K z m (if plus then -1 else 1)) q ∧
        PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) inputLoss A
          (z - (C.referenceState, 0))
          (fun y => canonicalGluedAiryIntegral S K z m (if plus then -1 else 1) y - y.2) q) →
      canonicalGluedRootTravel S K z m side q ∈ Icc l u →
      let i := if side then (K.cutPair m).2 else (K.cutPair m).1
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) outLoss B
        (z - (C.referenceState, 0)) (fun y => (K.chart z i y).1) q ∧
      ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (K.chart z i) q‖ ≤ B n *
        (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
          (z - (C.referenceState, 0))) := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hbound⟩ := airyInteriorChart_fixed_loss_bound hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hApos l u hl hlu
  obtain ⟨B, hBpos, hjet⟩ := hbound A hApos l u hl hlu
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs hlow m side q hq hlabels hvalue
  let U := canonicalGluedAiryIntegral S K z m 1
  let V := canonicalGluedAiryIntegral S K z m (-1)
  let t : PolarPoint → ℝ := fun y => (U y - V y) / 2
  let φ : PolarPoint → ℝ := fun y => (U y + V y) / 2
  let τ := canonicalGluedRootTravel S K z m side
  have hU : ContDiffAt ℝ ∞ U q := (hlabels false).1
  have hV : ContDiffAt ℝ ∞ V q := (hlabels true).1
  have ht : ContDiffAt ℝ ∞ t q := (hU.sub hV).div_const 2
  have hφ : ContDiffAt ℝ ∞ φ q := (hU.add hV).div_const 2
  have hj := characteristicPair_material_jets hU hV (hlabels false).2 (hlabels true).2
  have hτ : ContDiffAt ℝ ∞ τ q := by
    cases side with
    | false => exact ht
    | true => exact contDiffAt_const.sub ht
  have hτjets (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n τ q‖ ≤ A n * (1 + p (n + inputLoss) (z - (C.referenceState, 0))) := by
    cases side with
    | false => exact hj.1 n
    | true =>
        change ‖iteratedFDeriv ℝ n ((fun _ => 2 * airyTravelPrimitive (K.cutRadius m)) - t) q‖ ≤ _
        rw [iteratedFDeriv_sub_apply contDiffAt_const
          (ht.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
        cases n with
        | zero => omega
        | succ n =>
            simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, zero_sub, norm_neg] using hj.1 (n + 1)
  have hb := hjet (z - (C.referenceState, 0)) hlow τ φ q hτ hφ hvalue hτjets hj.2
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have he : K.chart z i =ᶠ[𝓝 q]
      (fun y => (((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ), φ y)) := by
    filter_upwards [(hA.domains z hz hs i).1.mem_nhds hq] with y hy
    exact canonicalCutPair_chart_eq_rootTravel hA hB hz hs m side hy
  constructor
  · intro n
    have he₁ : (fun y => (K.chart z i y).1) =ᶠ[𝓝 q]
        (fun y => ((3 / 2 : ℝ) * τ y) ^ (2 / 3 : ℝ)) := he.mono (fun _ h => congrArg Prod.fst h)
    rw [(he₁.iteratedFDeriv ℝ n).self_of_nhds]
    exact hb.2.1 n
  · intro n hn
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
    exact hb.2.2 n hn

end ContinuousFlexibility.Analysis
