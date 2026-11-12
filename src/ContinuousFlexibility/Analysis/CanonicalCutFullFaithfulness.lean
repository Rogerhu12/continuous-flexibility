import ContinuousFlexibility.Analysis.CanonicalStoredSliceBijection
import ContinuousFlexibility.Analysis.CanonicalCutCoefficientMatching
import ContinuousFlexibility.Analysis.RootPhysicalTransport

/-!
# Stored coefficients on the whole actual cut

Every stored angular flow slice is a genuine bijection. Differentiating
the already proved first-integral identities along those actual
trajectories therefore gives both transport equations at every interior
point, including the cut axes. The true common first jet at the cut then
identifies the two stored characteristic speeds with those of the smooth
effective field. Its positive discriminant and the known radial
coefficient recover both remaining stored coefficients.

This argument uses the actual time ODE at the cut. Even test functions
alone do not determine the stored angular coefficient there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem scalar_coefficients_eq_of_characteristicSpeeds
    {a b c b' c' : ℝ} (ha : a ≠ 0) (hdisc : 0 < b' ^ 2 - a * c')
    (hm : b / a - Real.sqrt (b ^ 2 - a * c) / a =
      b' / a - Real.sqrt (b' ^ 2 - a * c') / a)
    (hp : b / a + Real.sqrt (b ^ 2 - a * c) / a =
      b' / a + Real.sqrt (b' ^ 2 - a * c') / a) :
    b = b' ∧ c = c' := by
  field_simp [ha] at hm hp
  have hb : b = b' := by linarith only [hm, hp]
  have hroot : Real.sqrt (b ^ 2 - a * c) = Real.sqrt (b' ^ 2 - a * c') := by
    linarith only [hm, hp]
  have hpositive : 0 < Real.sqrt (b ^ 2 - a * c) := by
    rw [hroot]
    exact Real.sqrt_pos.mpr hdisc
  have hsquare := congrArg (fun x : ℝ => x ^ 2) hroot
  rw [Real.sq_sqrt (Real.sqrt_pos.mp hpositive).le, Real.sq_sqrt hdisc.le] at hsquare
  have hprod : a * c = a * c' := by
    rw [hb] at hsquare
    linarith only [hsquare]
  exact ⟨hb, mul_left_cancel₀ ha hprod⟩

private theorem speed_eq_of_two_transport_equations
    {q u v w : ℝ} (hq : q ≠ 0) (hu : u = -v * q) (hw : u = -w * q) :
    v = w :=
  neg_injective (mul_right_cancel₀ hq (hu.symm.trans hw))

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
  (hs : stateSector S z.1)

include hS hT hN01 hN02 hN03 hA hB hz hs

/-- Both stored transport equations hold on the whole open negative
component. Actual trajectory differentiation includes the two cut axes. -/
theorem canonicalGluedAiryIntegral_stored_characteristic_transport
    (m : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    radialPartial (canonicalGluedAiryIntegral S K z m 1) p =
        -minusCharacteristicSpeed (L.coefficients z) p *
          angularPartial (canonicalGluedAiryIntegral S K z m 1) p ∧
      radialPartial (canonicalGluedAiryIntegral S K z m (-1)) p =
        -plusCharacteristicSpeed (L.coefficients z) p *
          angularPartial (canonicalGluedAiryIntegral S K z m (-1)) p := by
  rcases p with ⟨r, θ⟩
  have honto := (n03CharacteristicSlice_bijective
    hS hT hN01 hN03 hA hB hz hs hN02 m hp.1).2
  have hplusonto : Function.Surjective (fun η => -L.minusFlow z m r (-η)) := by
    intro η
    obtain ⟨φ, hφ⟩ := honto (-η)
    refine ⟨-φ, ?_⟩
    simp only [neg_neg, hφ]
  obtain ⟨θm, hθm⟩ := honto θ
  obtain ⟨θp, hθp⟩ := hplusonto θ
  have hUd (σ η : ℝ) :
      DifferentiableAt ℝ (canonicalGluedAiryIntegral S K z m σ) (r, η) :=
    (((contDiffOn_canonicalGluedAiryIntegral hA hB hz hs m σ)
      (r, η) ⟨hp.1, mem_univ _⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp.1, mem_univ _⟩)).differentiableAt_one
  have hmconst : (fun t => canonicalGluedAiryIntegral S K z m 1
        (t, L.minusFlow z m t θm)) =ᶠ[𝓝 r] (fun _ => stateLeftChart S z.1 m θm) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with t ht
    exact (canonicalGluedAiryIntegral_on_n03Flows
      hS hT hN01 hN02 hN03 hA hB hz hs m ht θm).1
  have hpconst : (fun t => canonicalGluedAiryIntegral S K z m (-1)
        (t, -L.minusFlow z m t (-θp))) =ᶠ[𝓝 r] (fun _ => stateLeftChart S z.1 m θp) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with t ht
    exact (canonicalGluedAiryIntegral_on_n03Flows
      hS hT hN01 hN02 hN03 hA hB hz hs m ht θp).2
  have hmODE := (hN03.2.2.2.2.1 z hz hs m θm).2.2.1 r hp.1
  have hpODE : HasDerivAt (fun t => -L.minusFlow z m t (-θp))
      (plusCharacteristicSpeed (L.coefficients z) (r, -L.minusFlow z m r (-θp))) r := by
    obtain ⟨ha, hb, hc⟩ := hN03.2.2.2.1 z hz hs r (L.minusFlow z m r (-θp))
    have hd := ((hN03.2.2.2.2.1 z hz hs m (-θp)).2.2.1 r hp.1).fun_neg
    rw [neg_minusCharacteristicSpeed_eq_plus_of_reflection ha hb hc] at hd
    exact hd
  change -L.minusFlow z m r (-θp) = θ at hθp
  have hm := transport_of_constant_along_characteristic (hUd 1 θ) hmODE hθm hmconst
  have hplus := transport_of_constant_along_characteristic (hUd (-1) θ) hpODE hθp hpconst
  rw [hθm] at hm
  rw [hθp] at hplus
  exact ⟨hm, hplus⟩

/-- At every actual cut point the two stored characteristic speeds equal
those of the left smooth effective field, including on the reflection axes. -/
theorem canonicalCut_characteristicSpeeds_eq_closed
    (m : ℕ) (θ : ℝ) :
    let p := canonicalCutPoint S K z m θ
    let B := negativeCanonicalClosedCoefficients S K z (K.cutPair m).1
    minusCharacteristicSpeed (L.coefficients z) p = minusCharacteristicSpeed B p ∧
      plusCharacteristicSpeed (L.coefficients z) p = plusCharacteristicSpeed B p := by
  let p := canonicalCutPoint S K z m θ
  let B := negativeCanonicalClosedCoefficients S K z (K.cutPair m).1
  have hpN : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
    (hB.1.2 z hz hs m).2.1 (mem_range_self θ)
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hpN.1.1, hpN.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hcut := canonicalCut_closed_and_chart hA hB hz hs m false θ
  have hboundary := (hA.boundary z hz hs (K.cutPair m).1).2.2.2.2.1 p hcut.1
  have hBa : B.a p ≠ 0 := by
    rw [negativeCanonicalClosedCoefficients_radial_eq_original_on_closure
      hS hT hN01 hN03 hA hB hz hs (K.cutPair m).1 (hB.1.1 m).1 hcut.1 hpAnn]
    exact (n01_originalRadialCoefficient_pos hN01 hz hs hpAnn).ne'
  have hξ : 0 < (K.chart z (K.cutPair m).1 p).1 := by
    rw [hcut.2]
    exact (hB.1.1 m).2.2.2.2.2.1
  have hJ := (canonicalCutPair_planeJacobian_signs hA hB.1 hz hs m).1 p hcut.1
  have heffective := airyFirstIntegral_characteristic_transport
    (hboundary.1.differentiableAt (by simp)) hJ hboundary.2.2.2.ne' hξ hBa
  have hjet (σ : ℝ) := canonicalGluedAiryIntegral_fderiv_on_cut hA hB hz hs m σ θ
  have hparts (σ : ℝ) :
      radialPartial (canonicalGluedAiryIntegral S K z m σ) p =
          radialPartial (airyFirstIntegral (K.chart z (K.cutPair m).1) σ) p ∧
        angularPartial (canonicalGluedAiryIntegral S K z m σ) p =
          angularPartial (airyFirstIntegral (K.chart z (K.cutPair m).1) σ) p :=
    ⟨congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (hjet σ),
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) (hjet σ)⟩
  have hstored := canonicalGluedAiryIntegral_stored_characteristic_transport
    hS hT hN01 hN02 hN03 hA hB hz hs m hpN
  have hnonzero (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :=
    canonicalGluedAiryIntegral_angularPartial_ne_zero
      hS hT hN01 hN03 hA hB hz hs m hσ hpN
  constructor
  · apply speed_eq_of_two_transport_equations (hnonzero 1 (Or.inl rfl)) hstored.1
    rw [(hparts 1).1, (hparts 1).2]
    exact heffective.1
  · apply speed_eq_of_two_transport_equations (hnonzero (-1) (Or.inr rfl)) hstored.2
    rw [(hparts (-1)).1, (hparts (-1)).2]
    exact heffective.2

/-- Both closed half fields agree with the stored coefficients on the
entire current cut. No non-axis restriction or stored c regularity is assumed. -/
theorem negativeCutPair_coefficients_eq_closed_on_cut
    (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let p := canonicalCutPoint S K z m θ
    (L.coefficients z).a p = (negativeCanonicalClosedCoefficients S K z i).a p ∧
      (L.coefficients z).b p = (negativeCanonicalClosedCoefficients S K z i).b p ∧
      (L.coefficients z).c p = (negativeCanonicalClosedCoefficients S K z i).c p := by
  let p := canonicalCutPoint S K z m θ
  let B := negativeCanonicalClosedCoefficients S K z (K.cutPair m).1
  have hcut := canonicalCut_closed_and_chart hA hB hz hs m false θ
  have hpN := (hB.1.2 z hz hs m).2.1 (mem_range_self θ)
  have hbounds := hN01.2.2.2.1.1 m
  have hpAnn : p ∈ annularOpen D :=
    ⟨⟨hbounds.1.trans hpN.1.1, hpN.1.2.trans hbounds.2.2⟩, mem_univ _⟩
  have hBa := negativeCanonicalClosedCoefficients_radial_eq_original_on_closure
    hS hT hN01 hN03 hA hB hz hs (K.cutPair m).1 (hB.1.1 m).1 hcut.1 hpAnn
  have ha : (L.coefficients z).a p = B.a p := (hN03.1 z hz hs p).trans hBa.symm
  have hapos : 0 < B.a p := by
    rw [hBa]
    exact n01_originalRadialCoefficient_pos hN01 hz hs hpAnn
  have hh := ((hA.boundary z hz hs (K.cutPair m).1).2.2.2.2.1 p hcut.1).2.2.2
  have hξ : (K.chart z (K.cutPair m).1 p).1 = K.cutRadius m := congrArg Prod.fst hcut.2
  have hdisc : 0 < B.b p ^ 2 - B.a p * B.c p := by
    have hquot : 0 < (K.chart z (K.cutPair m).1 p).1 / K.height z (K.cutPair m).1 p ^ 4 :=
      div_pos (by rw [hξ]; exact (hB.1.1 m).2.2.2.2.2.1) (pow_pos hh 4)
    have he := negativeCanonicalClosedCoefficients_determinant hA hz hs
      (K.cutPair m).1 hcut.1
    rw [neg_div] at he
    linarith only [he, hquot]
  have hspeeds := canonicalCut_characteristicSpeeds_eq_closed
    hS hT hN01 hN02 hN03 hA hB hz hs m θ
  obtain ⟨hb, hc⟩ := scalar_coefficients_eq_of_characteristicSpeeds hapos.ne' hdisc
    (by simpa only [minusCharacteristicSpeed, ha] using hspeeds.1)
    (by simpa only [plusCharacteristicSpeed, ha] using hspeeds.2)
  cases side with
  | false => exact ⟨ha, hb, hc⟩
  | true =>
      have hmatch := canonicalCut_closedCoefficients_match hA hB hz hs m θ
      exact ⟨ha.trans hmatch.1.symm, hb.trans hmatch.2.1.symm, hc.trans hmatch.2.2.symm⟩

end Actual

end ContinuousFlexibility.Analysis
