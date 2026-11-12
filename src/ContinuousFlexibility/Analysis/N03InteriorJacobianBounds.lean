import ContinuousFlexibility.Analysis.N03InteriorChartJets
import ContinuousFlexibility.Analysis.CanonicalCutFullFaithfulness
import ContinuousFlexibility.Analysis.InteriorTravelJacobian

/-!
# A quantitative Jacobian for the actual two negative charts

The true glued first integrals satisfy the stored transport equations
on the whole negative component. Their genuine first derivatives and
the actual chart germ give the same absolute determinant formula on
both halves. Numerical speed and angular lower bounds then imply the
required lower bound for the actual chart, without a Jacobian premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

section Actual

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hN03 : N03Properties D T S C R L base ε)
  (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1) (m : ℕ) (side : Bool) {q : PolarPoint}
  (hq : q ∈ physicalPieceOpen S K z
    (if side then (K.cutPair m).2 else (K.cutPair m).1))

include hS hT hN01 hN02 hN03 hA hB hz hs hq

theorem canonicalCutPair_abs_jacobian_eq_characteristic_product :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    |planeJacobian (K.chart z i) q| =
      |(plusCharacteristicSpeed (L.coefficients z) q -
          minusCharacteristicSpeed (L.coefficients z) q) *
        angularPartial (canonicalGluedAiryIntegral S K z m (-1)) q *
        angularPartial (canonicalGluedAiryIntegral S K z m 1) q / 2| /
          Real.sqrt (K.chart z i q).1 := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let U := canonicalGluedAiryIntegral S K z m (-1)
  let V := canonicalGluedAiryIntegral S K z m 1
  let P := characteristicTravelChart U V
  let F : PolarPoint → PolarPoint := if side then
    (fun y => (2 * airyTravelPrimitive (K.cutRadius m) - (P y).1, (P y).2)) else P
  have hqN : q ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    have hu : q ∈ physicalPieceOpen S K z (K.cutPair m).1 ∪
        physicalPieceOpen S K z (K.cutPair m).2 := by
      cases side with
      | false => exact Or.inl hq
      | true => exact Or.inr hq
    rw [(hB.1.2 z hz hs m).2.2.2.1] at hu
    exact hu.1
  have hdiff (σ : ℝ) : DifferentiableAt ℝ (canonicalGluedAiryIntegral S K z m σ) q :=
    (((contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ) q hqN).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hqN)).differentiableAt_one
  have hP : DifferentiableAt ℝ P q :=
    (((hdiff 1).sub (hdiff (-1))).const_mul (1 / 2 : ℝ)).prodMk
      (((hdiff (-1)).add (hdiff 1)).const_mul (1 / 2 : ℝ))
  have hF : DifferentiableAt ℝ F q := by
    cases side with
    | false => exact hP
    | true => exact ((differentiableAt_const
        (2 * airyTravelPrimitive (K.cutRadius m))).sub hP.fst).prodMk hP.snd
  have hcoords : (fun y => (canonicalGluedRootTravel S K z m side y,
      (canonicalGluedAiryIntegral S K z m 1 y +
        canonicalGluedAiryIntegral S K z m (-1) y) / 2)) = F := by
    funext y
    cases side <;> apply Prod.ext <;>
      dsimp only [F, P, U, V, canonicalGluedRootTravel, characteristicTravelChart,
        Bool.false_eq_true, ↓reduceIte] <;> ring
  have he : K.chart z i =ᶠ[𝓝 q] rootPowerTravelChart F := by
    filter_upwards [(hA.domains z hz hs i).1.mem_nhds hq] with y hy
    rw [canonicalCutPair_chart_eq_rootTravel hA hB hz hs m side hy]
    exact Prod.ext (congrArg rootTravelPower (congrArg Prod.fst (congrFun hcoords y)))
      (congrArg Prod.snd (congrFun hcoords y))
  obtain ⟨_, _, _, _, _, _, hl₀, hl₁, _, _⟩ := hB.1.1 m
  have hl : K.left i = 0 := by cases side <;> assumption
  have hξ : 0 < (K.chart z i q).1 := by
    simpa only [hl] using ((hA.charts z hz hs i).1 hq).1.1
  have hvalues := canonicalCutPair_chartValues_of_gluedIntegrals
    m side (hB.1.2 z hz hs m).2.2.1 hq
  have hτ : 0 < (F q).1 := by
    rw [← congrArg Prod.fst (congrFun hcoords q), ← hvalues.2]
    exact mul_pos (by norm_num : (0 : ℝ) < 2 / 3) (Real.rpow_pos_of_pos hξ _)
  have htransport := canonicalGluedAiryIntegral_stored_characteristic_transport
    hS hT hN01 hN02 hN03 hA hB hz hs m hqN
  have hPJ := planeJacobian_characteristicTravelChart_speed_gap
    (hdiff (-1)) (hdiff 1) htransport.2 htransport.1
  have hFJ : |planeJacobian F q| = |planeJacobian P q| := by
    cases side with
    | false => rfl
    | true => exact (congrArg abs (planeJacobian_reflected_travel hP
        (2 * airyTravelPrimitive (K.cutRadius m)))).trans (abs_neg _)
  have hJ : planeJacobian (K.chart z i) q = planeJacobian (rootPowerTravelChart F) q := by
    simp only [planeJacobian, he.fderiv_eq (𝕜 := ℝ)]
  have hroot : rootTravelPower (F q).1 = (K.chart z i q).1 :=
    (congrArg Prod.fst he.self_of_nhds).symm
  rw [hJ, abs_planeJacobian_rootPowerTravelChart hF hτ, hFJ, hPJ, hroot]

theorem canonicalCutPair_jacobian_lower_of_speed_and_angular_bounds
    {δ l u : ℝ} (hδ : 0 ≤ δ) (hl : 0 ≤ l)
    (hgap : δ ≤ plusCharacteristicSpeed (L.coefficients z) q -
      minusCharacteristicSpeed (L.coefficients z) q)
    (hU : l ≤ angularPartial (canonicalGluedAiryIntegral S K z m (-1)) q)
    (hV : l ≤ angularPartial (canonicalGluedAiryIntegral S K z m 1) q)
    (hu : Real.sqrt
      (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1) q).1 ≤ u) :
    δ * l * l / (2 * u) ≤
      |planeJacobian (K.chart z (if side then (K.cutPair m).2 else (K.cutPair m).1)) q| := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  obtain ⟨_, _, _, _, _, _, hl₀, hl₁, _, _⟩ := hB.1.1 m
  have hleft : K.left i = 0 := by cases side <;> assumption
  have hξ : 0 < (K.chart z i q).1 := by
    simpa only [hleft] using ((hA.charts z hz hs i).1 hq).1.1
  have hv : 0 < Real.sqrt (K.chart z i q).1 := Real.sqrt_pos.mpr hξ
  have hn : 0 ≤ δ * l * l / 2 := by positivity
  have hproduct : δ * l * l / 2 ≤
      |(plusCharacteristicSpeed (L.coefficients z) q -
          minusCharacteristicSpeed (L.coefficients z) q) *
        angularPartial (canonicalGluedAiryIntegral S K z m (-1)) q *
        angularPartial (canonicalGluedAiryIntegral S K z m 1) q / 2| :=
    (div_le_div_of_nonneg_right
      (mul_le_mul (mul_le_mul hgap hU hl (hδ.trans hgap)) hV hl
        (mul_nonneg (hδ.trans hgap) (hl.trans hU)))
      (by norm_num : (0 : ℝ) ≤ 2)).trans (le_abs_self _)
  rw [canonicalCutPair_abs_jacobian_eq_characteristic_product
    hS hT hN01 hN02 hN03 hA hB hz hs m side hq]
  calc
    δ * l * l / (2 * u) = (δ * l * l / 2) / u := by ring
    _ ≤ (δ * l * l / 2) / Real.sqrt (K.chart z i q).1 :=
      div_le_div_of_nonneg_left hn hv hu
    _ ≤ _ := div_le_div_of_nonneg_right hproduct hv.le

end Actual

end ContinuousFlexibility.Analysis
