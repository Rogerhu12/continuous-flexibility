module

public import ContinuousFlexibility.Analysis.N01FlowGermLocality
public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualCompatibility

/-!
# The actual residual error does not see the height trace constant

The physical height pair contains a cutoff trace term. On every negative
component the supplied physical cutoff is constant, and the independent
coefficient error vanishes off those components. Both actual fluxes
therefore use only derivatives of the decoded height-space component.
This is a global identity of the flux functions, before differentiating.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

theorem N01Properties.heightPairField_partials_on_negative_component
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (η : HeightPair S) (m : ℕ)
    {p : PolarPoint} (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    radialPartial (heightPairField S η) p =
        radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) p ∧
      angularPartial (heightPairField S η) p =
        angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨c, hc⟩ := hS.2.2.1.constant_on_negative_component (hC.2.2.2.1 m)
  have heq : heightPairField S η =ᶠ[𝓝 p]
      (fun q => (S.height (3 / 4 : ℝ)).decode η.1 q + η.2 * c) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds hp.1 hp.2)] with q hq
    simp only [heightPairField, hc q.1 hq]
  have hfd : fderiv ℝ (heightPairField S η) p =
      fderiv ℝ ((S.height (3 / 4 : ℝ)).decode η.1) p := by
    simpa only [fderiv_add_const] using heq.fderiv_eq (𝕜 := ℝ)
  exact ⟨congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hfd,
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hfd⟩

theorem N01Properties.returnCorrectionErrorFluxes_eq_decoded_height
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionRadialErrorFlux D S C R χ z ρ η =
        (fun p => (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p) ∧
      returnCorrectionAngularErrorFlux D S C R χ z ρ η =
        (fun p => (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
          radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) p +
          (returnCorrectionCoefficientError D S C R χ z p ρ).2 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p) := by
  classical
  have hpoint (p : PolarPoint) :
      returnCorrectionRadialErrorFlux D S C R χ z ρ η p =
        (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p ∧
      returnCorrectionAngularErrorFlux D S C R χ z ρ η p =
        (returnCorrectionCoefficientError D S C R χ z p ρ).1 *
          radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) p +
          (returnCorrectionCoefficientError D S C R χ z p ρ).2 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p := by
    by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) p.1 ≠ 0
    · obtain ⟨hr, ht⟩ := hN.heightPairField_partials_on_negative_component hS η
        (Classical.choose hex) (Classical.choose_spec hex).1
      simp only [returnCorrectionRadialErrorFlux, returnCorrectionAngularErrorFlux, hr, ht,
        and_self]
    · have hzero : returnCorrectionCoefficientError D S C R χ z p = 0 := by
        simp only [returnCorrectionCoefficientError, dif_neg hex]
      simp only [returnCorrectionRadialErrorFlux, returnCorrectionAngularErrorFlux, hzero,
        LinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, zero_add, and_self]
  exact ⟨funext fun p => (hpoint p).1, funext fun p => (hpoint p).2⟩

theorem N01Properties.returnCorrectionResidualErrorField_eq_decoded_divergence
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hp : p ∈ annularOpen D) :
    returnCorrectionResidualErrorField D S C R χ z ρ η p =
      radialPartial (fun q => (returnCorrectionCoefficientError D S C R χ z q ρ).1 *
        angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p +
      angularPartial (fun q => (returnCorrectionCoefficientError D S C R χ z q ρ).1 *
        radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) q +
        (returnCorrectionCoefficientError D S C R χ z q ρ).2 *
        angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p := by
  classical
  obtain ⟨hF, hG⟩ := hN.returnCorrectionErrorFluxes_eq_decoded_height hS R χ z ρ η
  have hactual : returnCorrectionResidualErrorField D S C R χ z ρ η p =
      radialPartial (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p +
      angularPartial (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p :=
    if_pos hp
  exact hactual.trans (congrArg₂ (fun a b : ℝ => a + b)
    (congrArg (fun f : PolarPoint → ℝ => radialPartial f p) hF)
    (congrArg (fun f : PolarPoint → ℝ => angularPartial f p) hG))

end ContinuousFlexibility.Statements
