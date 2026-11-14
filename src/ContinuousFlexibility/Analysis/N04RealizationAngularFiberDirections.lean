module

public import ContinuousFlexibility.Analysis.N04RealizationPositiveAngularInverse
public import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
public import ContinuousFlexibility.Analysis.AngularFiberEndpointJets
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Actual fiber pullback and its finite boundary traces

The inverse is the literal angular inverse constructed from the finite
endpoint data. The state and physical radius are unchanged under the
pullback. Differentiating the resulting genuine joint tower and freezing
the same endpoint gives the actual radial boundary traces used by the
existing radial collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

/-- Compose the supplied physical field with the same actual angular inverse. -/
def n04Realization_angularFiberPullback_jointDirections
    [LocallyConvexSpace ℝ E] (hU : IsOpen U)
    (φ X : E → PolarPoint → ℝ)
    (Jinv : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => parameterizedCircleInverse (φ p.1) p.2))
    (JX : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => X p.1 p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => angularFiberPullback (φ p.1) (X p.1) p.2) := by
  have hdomain : IsOpen (U ×ˢ (univ : Set PolarPoint)) := hU.prod isOpen_univ
  let P : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JP : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.1) :=
    (smoothDirectionsLinearOn P hdomain).congrOn (fun _ _ => by
      simp only [P, ContinuousLinearMap.coe_fst'])
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R hdomain).congrOn (fun _ _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let G := smoothDirectionsUniformProd JP (smoothDirectionsUniformProd JR Jinv)
  exact (smoothDirections_realCompTVS G JX
    (fun p hp => ⟨hp.1, mem_univ _⟩)).congrOn (fun _ _ => rfl)

/-- A radial boundary trace of a genuine joint tower is jointly smooth
in the original state and angle; the endpoint is frozen only after
taking the actual radial derivatives. -/
def n04Realization_radialBoundaryJointDirections
    (hU : IsOpen U) (hc : Convex ℝ U)
    (f : E → PolarPoint → ℝ)
    (J : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => f p.1 p.2))
    (c : ℝ) (j : ℕ) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => radialBoundaryJet (f p.1) c j p.2) := by
  let L : (E × ℝ) →L[ℝ] E × PolarPoint :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod
      ((0 : (E × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ E ℝ))
  let a : E × PolarPoint := (0, (c, 0))
  have hL (p : E × ℝ) : a + L p = (p.1, (c, p.2)) := by
    simp only [a, L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.mk_add_mk, zero_add, add_zero]
  have hdomain : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hmap : MapsTo (fun p => a + L p) (U ×ˢ univ) (U ×ˢ univ) := by
    intro p hp
    change a + L p ∈ U ×ˢ (univ : Set PolarPoint)
    rw [hL]
    exact ⟨hp.1, mem_univ _⟩
  let K := (n04Realization_jointMixedTower J isOpen_univ
    (hc.prod convex_univ) j 0).compAffine L a hdomain hmap
  apply K.congrOn
  intro p hp
  change mixedDerivative j 0 (f (a + L p).1) (a + L p).2 = _
  rw [hL]
  simp only [mixedDerivative, iteratedDeriv_zero, radialBoundaryJet]

end ContinuousFlexibility.Analysis
