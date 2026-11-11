import ContinuousFlexibility.Analysis.N08CircleResidual
import ContinuousFlexibility.Analysis.N08Neighborhoods
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-!
# The actual state derivative of the projected return residual

The smooth directional tower is the one already supplied by N02 on the
sector.  Its first jet is pulled back by the actual mean/odd projection.
This gives a continuous linear derivative on every ambient state direction,
including control directions whose decoded functions are not constant.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base : ℕ} {ε : ℝ}

private theorem n08_return_smoothTame
    (hR : N02Properties D T S C R base ε) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hR
  exact h

/-- The genuine N02 jet, with no assumed derivative formula. -/
def n08CircleSectorJet (hR : N02Properties D T S C R base ε) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) :=
  (n08_return_smoothTame hR).choose

def n08CircleSectorPoint (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) : StateDirections S × ℝ :=
  (n08_sectorProjection hS (z.1 - C.referenceState), z.2)

theorem n08CircleSectorPoint_lift (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (z : AnnularState S × ℝ) :
    liftSectorParameter S C (n08CircleSectorPoint hS C z) =
      (n08_stateProjection hS z.1, z.2) := by
  apply Prod.ext
  · change C.referenceState +
      (n08_sectorProjection hS (z.1 - C.referenceState)).val = _
    rw [n08_sectorProjection_val, map_sub, n08_stateProjection_reference hS href]
    abel
  · rfl

theorem n08CircleSectorPoint_mem (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε) :
    n08CircleSectorPoint hS C z ∈ sectorNeighborhood S base ε ε := by
  constructor
  · change stateGrading S base
      (n08_sectorProjection hS (z.1 - C.referenceState)).val < ε
    rw [n08_sectorProjection_val, map_sub, n08_stateProjection_reference hS href]
    exact hz.1
  · exact hz.2

/-- The actual differential in all state directions, with the external
parameter held fixed. -/
def n08CircleStateDerivative (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    AnnularState S →L[ℝ] CircleSpace S :=
  (projectiveJetHeadLinear (n08CircleSectorJet hR).D 0
    (n08CircleSectorPoint hS C z) Fin.elim0).comp
      ((n08_sectorProjection hS).prod (0 : AnnularState S →L[ℝ] ℝ))

theorem n08CircleStateDerivative_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ)
    (v : AnnularState S) :
    n08CircleStateDerivative hS hR z v =
      (n08CircleSectorJet hR).D 1 (n08CircleSectorPoint hS C z)
        (Fin.cons (n08_sectorProjection hS v, 0) Fin.elim0) := by
  simp only [n08CircleStateDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
    projectiveJetHeadLinear_apply]

theorem n08CircleStateDerivative_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (v : AnnularState S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (n08CircleStateDerivative hS hR z v) z.1 v := by
  let J := n08CircleSectorJet hR
  have hj := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain
    (n08CircleSectorPoint_mem hS href hz) (n08_sectorProjection hS v, 0)
  have hpoint (t : ℝ) :
      n08CircleSectorPoint hS C (z.1 + t • v, z.2) =
        n08CircleSectorPoint hS C z + t • (n08_sectorProjection hS v, 0) := by
    apply Prod.ext
    · change n08_sectorProjection hS (z.1 + t • v - C.referenceState) =
        n08_sectorProjection hS (z.1 - C.referenceState) + t • n08_sectorProjection hS v
      rw [map_sub, map_add, map_smul, map_sub]
      abel
    · simp only [n08CircleSectorPoint, Prod.snd_add, Prod.snd_smul, smul_zero, add_zero]
  have hline : HasProjectiveLineDerivAt
      (fun x => R.residual (liftSectorParameter S C (n08CircleSectorPoint hS C (x, z.2))))
      (n08CircleStateDerivative hS hR z v) z.1 v := by
    rw [n08CircleStateDerivative_apply]
    simpa only [HasProjectiveLineDerivAt, hpoint, projectiveFirstJetValue, J] using hj
  apply hline.congr_germ
  have hc : Continuous (fun x : AnnularState S => (n08_stateProjection hS x, z.2)) :=
    (n08_stateProjection hS).continuous.prodMk continuous_const
  have hn := hc.continuousAt.preimage_mem_nhds
    ((n08_isOpen_stateNeighborhood S C base ε).mem_nhds hz)
  filter_upwards [hn] with x hx
  rw [n08CircleResidual_projected_coe hS hR hx, n08CircleSectorPoint_lift hS href]

/-- Injection of a circle control into the full ambient state. -/
def n08KappaDirection (S : PhysicalSpacesData) : CircleSpace S →L[ℝ] AnnularState S :=
  (0 : CircleSpace S →L[ℝ] HeightPair S).prod
    ((0 : CircleSpace S →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.id ℝ (CircleSpace S)).prod
        (0 : CircleSpace S →L[ℝ] CircleSpace S)))

theorem n08KappaDirection_apply (S : PhysicalSpacesData) (u : CircleSpace S) :
    n08KappaDirection S u = (0, (0, (u, 0))) := by
  simp only [n08KappaDirection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]

def n08CircleColumn (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    CircleSpace S →L[ℝ] CircleSpace S :=
  (n08CircleStateDerivative hS hR z).comp (n08KappaDirection S)

theorem n08CircleColumn_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (u : CircleSpace S) :
    n08CircleColumn hS hR z u = n08CircleStateDerivative hS hR z (0, (0, (u, 0))) := by
  rw [n08CircleColumn, ContinuousLinearMap.comp_apply, n08KappaDirection_apply]

theorem n08CircleColumn_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (u : CircleSpace S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (n08CircleColumn hS hR z u) z.1 (0, (0, (u, 0))) := by
  rw [n08CircleColumn_apply]
  apply n08CircleStateDerivative_hasLineDerivAt hS href hR
  simpa only [n08_stateProjection_eq_self hS z.1 hs, Prod.eta] using hz

end ContinuousFlexibility.Statements
