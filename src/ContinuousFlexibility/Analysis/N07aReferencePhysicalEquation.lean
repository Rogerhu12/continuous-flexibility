import ContinuousFlexibility.Analysis.N07aPhysicalPairingLinear
import ContinuousFlexibility.Analysis.N07aReferenceTestOperator
import ContinuousFlexibility.Analysis.N07aReferenceNuColumn

/-!
# The reference graph tested by an actual even pullback

N03 is applied only to the genuinely even compact height test it accepts.
The actual zero return residual and ν-column derivative identify its
operator and border term with the original radial reference graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07aPhysicalTestPullback_even
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : ∀ r θ, W (r, -θ) = W (r, θ)) :
    ∀ r θ, n07aPhysicalTestPullback S K z m W (r, -θ) =
      n07aPhysicalTestPullback S K z m W (r, θ) := by
  intro r θ
  by_cases hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  · have hp : (r, θ) ∈ physicalPieceOpen S K m := ⟨hr, mem_univ _⟩
    obtain ⟨hc, hh, _⟩ := h04.2.2.2.2.2.2.2.2.2.1 z hz hs m (r, θ) hp
    simp only [n07aPhysicalTestPullback, ite_eq_left hr, hc, hh, hW]
  · simp only [n07aPhysicalTestPullback, ite_eq_right hr]

theorem n07a_referenceGraph_pulledTest_equation
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    {γ M₀ M₁ : ℝ} {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {η f : PolarPoint → ℝ}
    (hrep : HasCanonicalRepresentation D S C K (C.referenceState, 0) U F η f)
    (hgraph : ReferenceGraph D γ M₀ M₁ (η, U.2.2.1)
      ((fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0))
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (hWeven : ∀ r θ, W (r, -θ) = W (r, θ)) :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
        divergenceOperator (L.coefficients (C.referenceState, 0))
          (n07aPhysicalTestPullback S K (C.referenceState, 0) m W) (r, θ))) +
      U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C (C.referenceState, 0) (r, θ) *
          n07aPhysicalTestPullback S K (C.referenceState, 0) m W (r, θ))) +
      U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) *
          n07aPhysicalTestPullback S K (C.referenceState, 0) m W (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        f (r, θ) * n07aPhysicalTestPullback S K (C.referenceState, 0) m W (r, θ)) := by
  let φ := n07aPhysicalTestPullback S K (C.referenceState, 0) m W
  let ψ := (S.height (3 / 4 : ℝ)).decode S.psi
  have hz := n07a_reference_mem_stateNeighborhood h01
  have hs := h01.2.2.1.stateSector
  have htest := n07aPhysicalTestPullback_test h04 hz hs hW
  have hφeven := n07aPhysicalTestPullback_even (m := m) h04 hz hs hWeven
  have hdiv := n07a_reference_divergence_even_test hS hT h01 h02 h03
    htest.1.1 hφeven htest.2.1 htest.1.2.2
  have hψp : Function.Periodic ψ (0, Real.pi) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1
  have hfp : Function.Periodic f (0, Real.pi) := by
    intro p
    have hg := hgraph.2.1.2.2.1 p
    change f (p + (0, Real.pi)) - U.2.2.2 * ψ (p + (0, Real.pi)) =
      f p - U.2.2.2 * ψ p at hg
    rw [hψp p] at hg
    linarith only [hg]
  have hm := (h04.2.2.2.1 m).2.1
  let col := n07aReferenceScalarOpenCoefficient hJ m hm 2
  have hψsrc : canonicalSource S K (C.referenceState, 0) m ψ = col.value := rfl
  have hiψ : Integrable (fun p => canonicalSource S K (C.referenceState, 0) m ψ p * W p)
      (canonicalMeasure S K m) := by
    rw [hψsrc]
    exact col.memLp.integrable_mul (n07a_canonicalTest_memLp hW)
  have hsub := n07a_pulledTest_source_sub hab h04 hz hs hW
    (fun p _ => hfp p) (fun p _ => hψp p)
    (n07a_canonicalRepresentation_source_integrable hrep hW) hiψ U.2.2.2
  have hop :
      (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
        divergenceOperator (L.coefficients (C.referenceState, 0)) φ (r, θ))) =
      radialWeakPairing D η φ := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro r hr
    apply congrArg radialAngularMean
    funext θ
    rw [hdiv ⟨hr, mem_univ _⟩]
  have hnu :
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C (C.referenceState, 0) (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * Radial.cosineMode 2 θ * φ (r, θ)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro r hr
    apply congrArg radialAngularMean
    funext θ
    rw [n07a_nuColumnField_reference hS hT h01 ⟨hr, mem_univ _⟩]
  have h := hgraph.2.2.2 φ htest.1
  rw [← hop, ← hnu] at h
  change _ = (∫ r in D.a..D.b, radialAngularMean
    (fun θ => (f (r, θ) - U.2.2.2 * ψ (r, θ)) * φ (r, θ))) at h
  rw [hsub] at h
  linarith only [h]

end ContinuousFlexibility.Analysis
