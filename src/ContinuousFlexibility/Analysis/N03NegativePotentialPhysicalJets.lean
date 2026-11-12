import ContinuousFlexibility.Analysis.InverseFieldsPhysicalJetClosure
import ContinuousFlexibility.Analysis.CanonicalNegativePotentialJets
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation
import ContinuousFlexibility.Analysis.N04bFieldRegularity

/-!
# Physical jet estimates give the actual negative canonical potential

The stored inverse satisfies both genuine inverse germs on the open
canonical domain. The constant-test operator identity identifies the
stored potential with the explicit inverse field. Thus physical
coefficient, chart, and height estimates, together with the actual
Jacobian lower bound, control every mixed derivative of the potential.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The eventual negative-component conclusion on one common state
neighborhood. Its constants may depend on the component and order. -/
def NegativeCanonicalPotentialJetBounds
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∀ s i : ℕ, K.positive i = false → ∃ B : ℝ, 0 < B ∧
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ q ∈ canonicalOpen S K i, ∀ a b : ℕ, a + b ≤ s →
      |mixedDerivative a b (K.potential z i) q| ≤
        B * (1 + pairGrading (stateGrading S) realGrading (s + loss)
          (z - (C.referenceState, 0)))

def NegativePotentialPhysicalJetEstimate
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (base low inputLoss outLoss : ℕ) (ε κ : ℝ) (A B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
    ∀ m : ℕ, K.positive m = false → ∀ q ∈ canonicalOpen S K m,
      κ ≤ |planeJacobian (K.chart z m) (K.inverseChart z m q)| →
      (∀ i : Fin 3, PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        inputLoss A (z - (C.referenceState, 0))
        (canonicalCoefficientComponent i (L.coefficients z)) (K.inverseChart z m q)) →
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        inputLoss A (z - (C.referenceState, 0)) (K.height z m) (K.inverseChart z m q) →
      (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n (K.chart z m) (K.inverseChart z m q)‖ ≤
        A n * (1 + pairGrading (stateGrading S) realGrading (n + inputLoss)
          (z - (C.referenceState, 0)))) →
    ∀ a b : ℕ, |mixedDerivative a b (K.potential z m) q| ≤
      B (a + b) * (1 + pairGrading (stateGrading S) realGrading (a + b + outLoss)
        (z - (C.referenceState, 0)))

theorem n03_negativePotential_from_physicalJets_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (inputLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∀ κ : ℝ, 0 < κ → ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        NegativePotentialPhysicalJetEstimate S C L K base low inputLoss outLoss ε κ A B := by
  let p := pairGrading (stateGrading S) realGrading
  have hp : Monotone p :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hclosure⟩ := inverseFields_from_physicalJets_fixed_loss_bound
    (E := AnnularState S × ℝ) (p := p) hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hApos κ hκ
  obtain ⟨B, hBpos, hbound⟩ := hclosure A hApos κ hκ
  refine ⟨B, hBpos, ?_⟩
  intro z hz hs hlow m hm q hq hJlower hcoeffjets hhjets hFjets a b
  have hU : IsOpen (physicalPieceOpen S K z m) := (hA.domains z hz hs m).1
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  rcases hA.charts z hz hs m with ⟨hFV, hGU, hGF, hFG, hF, hG, hh, hpoint⟩
  have hx : K.inverseChart z m q ∈ physicalPieceOpen S K z m := hGU hq
  have hcoeff (i : Fin 3) : ContDiffOn ℝ ∞
      (canonicalCoefficientComponent i (L.coefficients z)) (physicalPieceOpen S K z m) := by
    have hraw := hfield.smooth_coefficients z hz hs
    have hsub := (hA.domains z hz hs m).2.2.1
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hraw.1.mono hsub
    · exact hraw.2.1.mono hsub
    · exact hraw.2.2.mono hsub
  have hJne (y : PolarPoint) (hy : y ∈ physicalPieceOpen S K z m) :
      planeJacobian (K.chart z m) y ≠ 0 := (hpoint y hy).2.1
  have hright : K.chart z m ∘ K.inverseChart z m =ᶠ[𝓝 q]
      (id : PolarPoint → PolarPoint) := by
    filter_upwards [hV.mem_nhds hq] with y hy
    exact hFG y hy
  have hleft : K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 (K.inverseChart z m q)]
      (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hGF y hy
  have hjets := hbound (z - (C.referenceState, 0)) hlow (L.coefficients z)
    (K.chart z m) (K.inverseChart z m) (K.height z m)
    (physicalPieceOpen S K z m) hU hcoeff hF hh hJne q hx
    (hG.contDiffAt (hV.mem_nhds hq)) hright hleft hJlower hcoeffjets hhjets hFjets (a + b)
  have hprimitive := contDiffOn_coordinatePrimitiveJetField_of_fields hU hcoeff hF hh hJne
  have hphysical := (contDiffOn_coordinatePhysicalFields hU
    (L.coefficients z) (K.chart z m) (K.height z m) hprimitive).1
  have hsmooth : ContDiffOn ℝ ∞
      (inverseChartPotential (L.coefficients z) (K.chart z m)
        (K.inverseChart z m) (K.height z m)) (canonicalOpen S K m) := by
    unfold inverseChartPotential
    simpa only [Function.comp_def] using hphysical.comp hG hGU
  rw [negativeCanonicalPotential_mixedDerivative_eq hB hz hs m hm a b hq]
  exact (abs_mixedDerivative_le_norm_iteratedFDeriv hV hsmooth a b hq).trans hjets.1

end ContinuousFlexibility.Analysis
