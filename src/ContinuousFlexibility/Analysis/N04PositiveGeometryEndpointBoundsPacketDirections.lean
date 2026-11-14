module

public import ContinuousFlexibility.Analysis.N04RealizationRootAbsorbedJoint
public import ContinuousFlexibility.Analysis.N04RealizationJointSpatialEvaluation
public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootHeight
public import ContinuousFlexibility.Analysis.N01cAngularJetTowers
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
public import ContinuousFlexibility.Analysis.BoundaryMixedJets
public import ContinuousFlexibility.Analysis.CircleCompositionFaaBounds

/-!
# The actual radial packet traces and their angular parameter towers

The finite radial packet uses the literal absorbed coordinates. The
joint tower is obtained from their existing spatial tower by the fixed
radial evaluation, and its angular slices are identified with the
actual mixed spatial derivatives. The four variable entries are exactly
the original q-weighted normalized height inputs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

section RadialRestriction

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}

/-- Additional angular derivatives add to the intrinsic angular index
of the same actual radial trace. -/
theorem n04PositiveGeometry_iteratedDeriv_mixedTrace
    {g : PolarPoint → ℝ} (hΩ : IsOpen Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (r : ℝ) (hr : ∀ θ, (r, θ) ∈ Ω) (a d b : ℕ) (θ : ℝ) :
    iteratedDeriv b (fun η => mixedDerivative a d g (r, η)) θ =
      mixedDerivative a (b + d) g (r, θ) := by
  have he : (fun η => mixedDerivative a d g (r, η)) =
      iteratedDeriv d (radialBoundaryJet g r a) :=
    funext (fun η => (iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
      hΩ hg r hr a d η).symm)
  rw [he, circle_iteratedDeriv_iteratedDeriv]
  exact iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hΩ hg r hr a (b + d) θ

/-- A fixed radial trace retains the original state-angle domain. -/
def n04PositiveGeometry_radialTrace_joint
    (J : SmoothDirections (U ×ˢ Ω) (fun z => f z.1 z.2))
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω)
    (r : ℝ) (hr : ∀ θ, (r, θ) ∈ Ω) (a : ℕ) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun z => radialBoundaryJet (f z.1) r a z.2) := by
  let L : (X × ℝ) →L[ℝ] X × PolarPoint :=
    (ContinuousLinearMap.fst ℝ X ℝ).prod
      ((0 : X × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ X ℝ))
  let c : X × PolarPoint := (0, r, 0)
  have hpoint (z : X × ℝ) : c + L z = (z.1, r, z.2) := by
    simp only [c, L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.zero_apply,
      Prod.mk_add_mk, zero_add, add_zero]
  have hmap : MapsTo (fun z => c + L z) (U ×ˢ univ) (U ×ˢ Ω) := by
    intro z hz
    change c + L z ∈ U ×ˢ Ω
    rw [hpoint]
    exact ⟨hz.1, hr z.2⟩
  let JA := n04Realization_jointSpatialJet_directions J a (fun _ => (1, 0))
  apply (JA.compAffine L c (hU.prod isOpen_univ) hmap).congr
  intro z hz
  change iteratedFDeriv ℝ a (f (c + L z).1) (c + L z).2 (fun _ => (1, 0)) = _
  rw [hpoint]
  have he := iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ
    (hf z.1 hz.1) a (hr z.2) (fun _ => (0 : Fin 2))
  have hm : iteratedFDeriv ℝ a (f z.1) (r, z.2) (fun _ => (1, 0)) =
      mixedDerivative a 0 (f z.1) (r, z.2) := by
    simpa [cylinderBasisVector] using he
  exact hm.trans (by simp only [mixedDerivative, iteratedDeriv_zero, radialBoundaryJet])

/-- Angular slices of that same tower are the literal mixed jets. -/
def n04PositiveGeometry_radialTrace_parameter
    (J : SmoothDirections (U ×ˢ Ω) (fun z => f z.1 z.2))
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω)
    (r : ℝ) (hr : ∀ θ, (r, θ) ∈ Ω) (a b : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => mixedDerivative a b (f x) (r, θ)) :=
  (smoothDirections_angularStateSlice
    (n04PositiveGeometry_radialTrace_joint J hU hΩ hf r hr a) b θ).congr
      (fun x hx => iteratedDeriv_radialBoundaryJet_eq_mixedDerivative
        hΩ (hf x hx) r hr a b θ)

end RadialRestriction

local instance n04PositivePacketDirectionsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε r : ℝ}

/-- The coordinate projection of the original absorbed root packet. -/
def n04PositiveGeometry_rootPacketCoordinate_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1) (i : Fin 6) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ annularOpen D)
      (fun z : (AnnularState S × ℝ) × PolarPoint =>
        n06ActualRootAbsorbedCoordinates D S z.1 z.2 i) :=
  (smoothDirections_postcompCLM
    (n04Realization_rootAbsorbedCoordinates_joint hD hT hS hε)
    (ContinuousLinearMap.proj i)).congr (fun _ _ => rfl)

private theorem rootPacketCoordinate_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) (i : Fin 6) :
    ContDiff ℝ ∞ (fun p => n06ActualRootAbsorbedCoordinates D S z p i) :=
  (contDiff_apply ℝ ℝ i).comp
    (n06_actualRootAbsorbedCoordinates_contDiff hD hT hS z)

/-- Original radial packet coordinate traces, with no chosen chart. -/
def n04PositiveGeometry_rootPacketTrace_joint
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a : ℕ) :
    SmoothDirections (stateNeighborhood S C base ε ×ˢ (univ : Set ℝ))
      (fun z => radialBoundaryJet
        (fun p => n06ActualRootAbsorbedCoordinates D S z.1 p i) r a z.2) :=
  n04PositiveGeometry_radialTrace_joint
    (n04PositiveGeometry_rootPacketCoordinate_joint hD hT hS hε i)
    (isOpen_stateNeighborhood S C base ε) (isOpen_Ioo.prod isOpen_univ)
    (fun z _ => (rootPacketCoordinate_contDiff hD hT hS z i).contDiffOn)
    r (fun _ => ⟨hr, mem_univ _⟩) a

/-- The parameter tower of each actual packet mixed jet. -/
def n04PositiveGeometry_rootPacketMixed_parameter
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (i : Fin 6) (a b : ℕ) (θ : ℝ) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => mixedDerivative a b
        (fun p => n06ActualRootAbsorbedCoordinates D S z p i) (r, θ)) :=
  n04PositiveGeometry_radialTrace_parameter
    (n04PositiveGeometry_rootPacketCoordinate_joint hD hT hS hε i)
    (isOpen_stateNeighborhood S C base ε) (isOpen_Ioo.prod isOpen_univ)
    (fun z _ => (rootPacketCoordinate_contDiff hD hT hS z i).contDiffOn)
    r (fun _ => ⟨hr, mem_univ _⟩) a b θ

/-- The four state-dependent coordinates occupy the unchanged slots one
through four of the six-coordinate absorbed packet. -/
def n04PositiveGeometry_rootPacketHeightIndex (i : Fin 4) : Fin 6 :=
  ⟨i.val + 1, by omega⟩

theorem n04PositiveGeometry_rootPacket_mixed_height
    (z : AnnularState S × ℝ) (i : Fin 4) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => n06ActualRootAbsorbedCoordinates D S z q
      (n04PositiveGeometry_rootPacketHeightIndex i)) p =
      z.2 * mixedDerivative a b (n06RootNormalizedHeightFields D S z.1.1 i) p := by
  have he : (fun q => n06ActualRootAbsorbedCoordinates D S z q
      (n04PositiveGeometry_rootPacketHeightIndex i)) =
      (fun q => z.2 * n06RootNormalizedHeightFields D S z.1.1 i q) := by
    funext q
    rw [n06_actualRootAbsorbedCoordinates_eq_packet]
    fin_cases i <;> rfl
  rw [he, mixedDerivative_const_mul]

end ContinuousFlexibility.Analysis
