import ContinuousFlexibility.Analysis.N04RealizationPrimitiveClosure
import ContinuousFlexibility.Analysis.N04RealizationMaterialSampleEnvelopes
import ContinuousFlexibility.Analysis.N06Neighborhood

/-!
# The complete actual primitive material-jet certificate

One neighborhood supports every finite order. At each order all genuine
state, piece and material-point evaluations form one index set. The raw
chart and atom estimates construct the factor certificate there; the
fifteen fields are collected before the actual sample cost is converted
to the physical point. The records and their samples never change.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}

/-- The one-sided sample displacement is geometric input from the actual
atlas. All fifteen material-field estimates are derived, on one common
neighborhood, from the reference/current towers and the material model. -/
theorem n04Realization_materialJets_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hfloor : ∀ r : ℝ, 1 ≤ T.E0 r)
    (hshift : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          endpointX 1 (Statements.endpointDistance D (T.sample (K.cell m))) ≤
            endpointX 1 (Statements.endpointDistance D x.1) + B) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ N : ℕ, ∃ r d : ℕ, ∃ C₀ A : ℝ, 0 < C₀ ∧ 0 ≤ A ∧
        ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
          ∀ (m : ℕ) (y : PolarPoint), (T.radius y.1, y.2) ∈ physicalPieceOpen S K z m →
            ∀ i : CanonicalPrimitiveIndex, ∀ k : ℕ, k ≤ N →
              ‖iteratedFDeriv ℝ k
                (fun v : PolarPoint => canonicalPrimitiveField D T C K z m i
                  (T.radius v.1, v.2)) y‖ ≤
                C₀ * T.E0 (T.radius y.1) ^ A *
                  (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d := by
  classical
  obtain ⟨base', hb, η, hη, hηε, hrawAll⟩ :=
    n04Realization_chartAtom_envelopes hD hT hε hrefState hgeom href hcur
      (fun m => hfloor (T.sample (K.cell m)))
  have hgeom' : CanonicalGeometry D S C K base' η :=
    n06_CanonicalGeometry_mono hgeom hb hηε
  have hreference : (C.referenceState, 0) ∈ stateNeighborhood S C base' η :=
    reference_mem_stateNeighborhood S C base' hη
  obtain ⟨B, hB, hdisplacement⟩ := hshift
  refine ⟨base', hb, η, hη, hηε, fun N => ?_⟩
  obtain ⟨r, hraw⟩ := hrawAll (N + 2)
  let X : Type :=
    {v : ((AnnularState S × ℝ) × ℕ) × PolarPoint //
      v.1.1 ∈ stateNeighborhood S C base' η ∧ stateSector S v.1.1.1 ∧
        n07bMaterialRadiusChart T v.2 ∈ physicalPieceOpen S K v.1.1 v.1.2}
  let z : X → AnnularState S × ℝ := fun x => x.1.1.1
  let m : X → ℕ := fun x => x.1.1.2
  let p : X → PolarPoint := fun x => x.1.2
  have hz (x : X) : z x ∈ stateNeighborhood S C base' η := x.2.1
  have hs (x : X) : stateSector S (z x).1 := x.2.2.1
  have hp (x : X) : n07bMaterialRadiusChart T (p x) ∈
      physicalPieceOpen S K (z x) (m x) := x.2.2.2
  let sample : X → ℝ := fun x => T.E0 (T.sample (K.cell (m x)))
  let point : X → ℝ := fun x => T.E0 (T.radius (p x).1)
  let rho : X → ℝ := fun x =>
    1 + stateGrading S r ((z x).1 - C.referenceState) + |(z x).2|
  let W : X → ℝ := fun x => sample x * point x * rho x
  have hsample (x : X) : 1 ≤ sample x := hfloor _
  have hpoint (x : X) : 1 ≤ point x := hfloor _
  have hrho (x : X) : 1 ≤ rho x := by
    dsimp only [rho]
    linarith only [apply_nonneg (stateGrading S r) ((z x).1 - C.referenceState),
      abs_nonneg (z x).2]
  have hproduct (x : X) : 1 ≤ sample x * point x := by
    simpa only [one_mul] using
      mul_le_mul (hsample x) (hpoint x) zero_le_one (zero_le_one.trans (hsample x))
  have hproductW (x : X) : sample x * point x ≤ W x :=
    le_mul_of_one_le_right (zero_le_one.trans (hproduct x)) (hrho x)
  have hW (x : X) : 1 ≤ W x := (hproduct x).trans (hproductW x)
  have hpointW (x : X) : point x ≤ W x :=
    (le_mul_of_one_le_left (zero_le_one.trans (hpoint x)) (hsample x)).trans (hproductW x)
  have hsampleW (x : X) : sample x ≤ W x :=
    (le_mul_of_one_le_right (zero_le_one.trans (hsample x)) (hpoint x)).trans (hproductW x)
  have hcurrentW (x : X) : sample x * rho x ≤ W x :=
    mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (zero_le_one.trans (hsample x)) (hpoint x))
      (zero_le_one.trans (hrho x))
  have hvalues := n04Realization_material_sample_value_envelopes hT hD
    (fun x : X => T.radius (p x).1) (fun x : X => T.sample (K.cell (m x)))
    (fun x => (hT.2.2.2.2.2.2.2.1 (p x).1).1)
    (fun x => materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell (m x)))
    hpoint hB (fun x => hdisplacement (z x)
      (stateNeighborhood_mono S C hb hηε (hz x)) (hs x) (m x)
      (n07bMaterialRadiusChart T (p x)) (hp x))
  have hRatio : HasPositiveEnvelope W
      (fun x => T.H (T.radius (p x).1) / T.H (T.sample (K.cell (m x)))) :=
    hvalues.1.base_mono (fun x => zero_le_one.trans (hpoint x)) hpointW
  have H : N04RealizationPrimitiveFactorEnvelopes X T S C K W z m p N :=
    n04Realization_primitiveFactor_envelopes hD hT hgeom' hreference hrefState.stateSector
      hW z m p hz hs hp hpointW N (hraw X) hcurrentW hsampleW
  have hfield := n04Realization_primitive_envelopes_of_factors hD hT hgeom'
    hreference hrefState.stateSector hW z m p hz hs hp hpointW hRatio N H
  let I : Type := CanonicalPrimitiveIndex × Fin (N + 1)
  let F : I → X → ℝ := fun i x => ‖iteratedFDeriv ℝ i.2.val
    (canonicalPrimitiveField D T C K (z x) (m x) i.1 ∘ n07bMaterialRadiusChart T) (p x)‖
  have hsum : HasPositiveEnvelope W (fun x => ∑ i : I, F i x) :=
    hasPositiveEnvelope_finsetSum hW Finset.univ F
      (fun i _ => hfield i.1 i.2.val (Nat.le_of_lt_succ i.2.isLt))
  obtain ⟨d, C₀, A, hC₀, hA, hbound⟩ :=
    n04Realization_sample_point_polynomial_bound hsample hpoint hrho hvalues.2 hsum
  refine ⟨r, d, C₀, A, hC₀, hA, ?_⟩
  intro z' hz' hs' m' y hy i k hk
  let x : X := ⟨((z', m'), y), hz', hs', hy⟩
  let j : I := (i, ⟨k, Nat.lt_succ_of_le hk⟩)
  have hsingle : F j x ≤ ∑ i : I, F i x :=
    Finset.single_le_sum (fun i _ => (show 0 ≤ F i x from norm_nonneg _))
      (Finset.mem_univ j)
  exact hsingle.trans (hbound x)

end ContinuousFlexibility.Analysis
