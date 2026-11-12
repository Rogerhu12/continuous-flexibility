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

private theorem coefficientComponents_contDiffOn_of_subset
    {V U : Set PolarPoint} {P : SymmetricCoefficients} (hUV : U ⊆ V)
    (hP : ContDiffOn ℝ ∞ P.a V ∧ ContDiffOn ℝ ∞ P.b V ∧
      ContDiffOn ℝ ∞ P.c V) :
    ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i P) U := by
  intro i
  unfold canonicalCoefficientComponent
  split_ifs
  · exact hP.1.mono hUV
  · exact hP.2.1.mono hUV
  · exact hP.2.2.mono hUV

private theorem inversePotential_mixedDerivative_le_of_physicalJets
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {low inputLoss outLoss : ℕ}
    {A B : ℕ → ℝ} {κ : ℝ}
    (hbound : InverseFieldsFromPhysicalJetsEstimate p low inputLoss outLoss A κ B)
    (z : E) (hlow : p low z ≤ 1)
    (P : SymmetricCoefficients) (F G : PolarPoint → PolarPoint)
    (h v : PolarPoint → ℝ) (U V : Set PolarPoint)
    (hU : IsOpen U) (hV : IsOpen V)
    (hP : ∀ i : Fin 3, ContDiffOn ℝ ∞ (canonicalCoefficientComponent i P) U)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G V)
    (hh : ContDiffOn ℝ ∞ h U) (hJ : ∀ y ∈ U, planeJacobian F y ≠ 0)
    (hGU : MapsTo G V U) (hGF : ∀ y ∈ U, G (F y) = y)
    (hFG : ∀ y ∈ V, F (G y) = y)
    (hv : EqOn v (inverseChartPotential P F G h) V)
    (q : PolarPoint) (hq : q ∈ V) (hJlower : κ ≤ |planeJacobian F (G q)|)
    (hPjets : ∀ i : Fin 3, PointwiseMaterialJetBound p inputLoss A z
      (canonicalCoefficientComponent i P) (G q))
    (hhjets : PointwiseMaterialJetBound p inputLoss A z h (G q))
    (hFjets : ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G q)‖ ≤
      A n * (1 + p (n + inputLoss) z)) (a b : ℕ) :
    |mixedDerivative a b v q| ≤
      B (a + b) * (1 + p (a + b + outLoss) z) := by
  have hx : G q ∈ U := hGU hq
  have hright : F ∘ G =ᶠ[𝓝 q] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hV.mem_nhds hq] with y hy
    exact hFG y hy
  have hleft : G ∘ F =ᶠ[𝓝 (G q)] (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hGF y hy
  have hjets := hbound z hlow P F G h U hU hP hF hh hJ q hx
    (hG.contDiffAt (hV.mem_nhds hq)) hright hleft hJlower hPjets hhjets hFjets (a + b)
  have hprimitive := contDiffOn_coordinatePrimitiveJetField_of_fields hU hP hF hh hJ
  have hphysical := (contDiffOn_coordinatePhysicalFields hU P F h hprimitive).1
  have hsmooth : ContDiffOn ℝ ∞ (inverseChartPotential P F G h) V := by
    unfold inverseChartPotential
    simpa only [Function.comp_def] using hphysical.comp hG hGU
  exact (congrArg abs (mixedDerivative_eqOn_of_isOpen hV hv a b hq)).trans_le
    ((abs_mixedDerivative_le_norm_iteratedFDeriv hV hsmooth a b hq).trans hjets.1)

private theorem n03_negativePotential_physicalJets_of_bound
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base low inputLoss outLoss : ℕ} {ε κ : ℝ} {A B : ℕ → ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hbound : InverseFieldsFromPhysicalJetsEstimate (pairGrading (stateGrading S) realGrading)
      low inputLoss outLoss A κ B) :
    NegativePotentialPhysicalJetEstimate S C L K base low inputLoss outLoss ε κ A B := by
  intro z hz hs hlow m hm q hq hJlower hcoeffjets hhjets hFjets a b
  rcases hA.charts z hz hs m with ⟨_hFV, hGU, hGF, hFG, hF, hG, hh, hpoint⟩
  exact inversePotential_mixedDerivative_le_of_physicalJets
    (E := AnnularState S × ℝ) (p := pairGrading (stateGrading S) realGrading)
    hbound (z - (C.referenceState, 0)) hlow (L.coefficients z)
    (K.chart z m) (K.inverseChart z m) (K.height z m) (K.potential z m)
    (physicalPieceOpen S K z m) (canonicalOpen S K m)
    (hA.domains z hz hs m).1 (isOpen_Ioo.prod isOpen_univ)
    (coefficientComponents_contDiffOn_of_subset (hA.domains z hz hs m).2.2.1
      (hfield.smooth_coefficients z hz hs))
    hF hG hh (fun y hy => (hpoint y hy).2.1) hGU hGF hFG
    (negativeCanonicalPotential_eqOn_inverseChartPotential hB hz hs m hm)
    q hq hJlower hcoeffjets hhjets hFjets a b

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
  have hI : HasInterpolation p := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨low, outLoss, hclosure⟩ := inverseFields_from_physicalJets_fixed_loss_bound
    (E := AnnularState S × ℝ) (p := p) hp hI inputLoss
  refine ⟨low, outLoss, ?_⟩
  intro A hApos κ hκ
  obtain ⟨B, hBpos, hbound⟩ := hclosure A hApos κ hκ
  exact ⟨B, hBpos, n03_negativePotential_physicalJets_of_bound hA hB hfield hbound⟩

end ContinuousFlexibility.Analysis
