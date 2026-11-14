module

public import ContinuousFlexibility.Analysis.N05RetainedReferenceAssembly
public import ContinuousFlexibility.Analysis.N04RealizationRetainedPositiveEndpoints
public import ContinuousFlexibility.Analysis.N05RetainedOpticalLowerAdapter
public import ContinuousFlexibility.Analysis.N05RetainedN01a
public import ContinuousFlexibility.Analysis.N04RealizationRetainedN01
public import ContinuousFlexibility.Analysis.N04RealizationOpticalFieldGateway
public import ContinuousFlexibility.Analysis.N01ResidualSmoothTame

/-!
# One retained seed through the actual physical field construction

The original retained pair, connected reference and coordinate certificate
survive the cumulative construction. The existing seed factory supplies
the material data, physical spaces, primitive geometry and global E0
floor. The same seed also supplies the interior simple-root certificate for
all positive endpoints. One flow installation completes N01; its fixed return equation
and one optical cutoff then give Through03 on a common neighborhood.

The retained source is `n05_exists_retained_radial_reference`. Its bridge
is `exists_n05_seedReferenceConstruction_of_retained`, followed by
`SeedReferenceConstruction.exists_n05RetainedN01a` and the fixed-record
`N01Properties.exists_returnEquation`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
  ContinuousFlexibility.Blueprint

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

/-- Keep the dependent cutoff/source tail opaque during the preceding
existential selections. This is exactly the public optical payload. -/
private def n04RealizationOpticalFieldStartAt
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base loss : ℕ) (ε : ℝ) : Prop :=
  ∃ Q : N04bOpticalCutoffData D S C base ε,
    ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
      NonlinearPropertiesThrough03 D T S C R (Q.field E) base loss ε ∧
      N04bFieldRegularity D S C (Q.field E) base ε ∧
      (Q.field E).coefficients = returnCorrectedCoefficients D S C Q.cutoff ∧
      (Q.field E).minusFlow = returnCorrectedMinusFlow S C Q.cutoff

private def n04RealizationRetainedFieldStart (D : ReferenceData) : Prop :=
  ∃ T : MaterialData, ∃ S : PhysicalSpacesData, ∃ C : NonlinearGeometryData S,
    ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      IsMaterialData D T ∧ IsPhysicalSpaces D T S ∧
      (∀ r : ℝ, 1 ≤ T.E0 r) ∧ N01PrimitiveGeometry D T S C ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) ∧
      4 ≤ base ∧ 0 < ε ∧ n04RealizationOpticalFieldStartAt D T S C R base loss ε

/-- Compose the two choices before specializing the geometry type or
the final dependent field predicate. Neither intermediate witness moves. -/
private theorem n04Realization_compose_fixed_start
    {Flow Geometry Return : Type*} (install : Flow → Geometry)
    (N : Geometry → ℕ → ℕ → ℝ → Prop) (Primitive Host : Geometry → Prop)
    (Final : Geometry → Return → ℕ → ℕ → ℝ → Prop)
    (hstart : ∃ f base loss ε, 4 ≤ base ∧ 0 < ε ∧
      N (install f) base loss ε ∧ Primitive (install f) ∧ Host (install f))
    (hnext : ∀ C base loss ε, N C base loss ε →
      ∃ R base' ε', base ≤ base' ∧ 0 < ε' ∧ Final C R base' loss ε') :
    ∃ f R base loss ε, 4 ≤ base ∧ 0 < ε ∧
      Primitive (install f) ∧ Host (install f) ∧ Final (install f) R base loss ε := by
  obtain ⟨f, base₀, loss, ε₀, hbase₀, _hε₀, hN, hPrimitive, hHost⟩ := hstart
  obtain ⟨R, base, ε, hbase, hε, hFinal⟩ := hnext (install f) base₀ loss ε₀ hN
  exact ⟨f, R, base, loss, ε, hbase₀.trans hbase, hε, hPrimitive, hHost, hFinal⟩

private theorem n04Realization_retainedN01_with_host
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hA : N01PartA D T S C) (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r : ℝ, 1 ≤ T.E0 r)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) :
    ∃ Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ,
      ∃ base loss : ℕ, ∃ ε : ℝ, 4 ≤ base ∧ 0 < ε ∧
        N01Properties D T S (circleFlowGeometry C Θ) base loss ε ∧
        N01PrimitiveGeometry D T S (circleFlowGeometry C Θ) ∧
        (∀ m, Ioo ((circleFlowGeometry C Θ).left m)
          ((circleFlowGeometry C Θ).right m) ⊆
            D.cells ((circleFlowGeometry C Θ).cell m)) := by
  obtain ⟨Θ, base, loss, ε, hbase, hε, hN, hG',
      _hcontrol, hcell, hleft, hright, _htravel, _hreference⟩ :=
    n04Realization_retainedN01 hS hT hA hG hE
  refine ⟨Θ, base, loss, ε, hbase, hε, hN, hG', fun m => ?_⟩
  simpa only [hleft, hright, hcell] using hhost m

/-- The fixed N02 factory is applied before the optical cutoff factory.
Only the three flow fields of the supplied Part A record are installed. -/
theorem n04Realization_partA_through03
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hA : N01PartA D T S C) (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r : ℝ, 1 ≤ T.E0 r)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) :
    ∃ Θ : (AnnularState S × ℝ) → ℕ → ℝ → ℝ → ℝ,
      ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
        4 ≤ base ∧ 0 < ε ∧
        N01PrimitiveGeometry D T S (circleFlowGeometry C Θ) ∧
        (∀ m, Ioo ((circleFlowGeometry C Θ).left m)
          ((circleFlowGeometry C Θ).right m) ⊆
            D.cells ((circleFlowGeometry C Θ).cell m)) ∧
        ∃ Q : N04bOpticalCutoffData D S (circleFlowGeometry C Θ) base ε,
        ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
          NonlinearPropertiesThrough03 D T S (circleFlowGeometry C Θ) R
            (Q.field E) base loss ε ∧
          N04bFieldRegularity D S (circleFlowGeometry C Θ) (Q.field E) base ε ∧
          (Q.field E).coefficients =
            returnCorrectedCoefficients D S (circleFlowGeometry C Θ) Q.cutoff ∧
          (Q.field E).minusFlow =
            returnCorrectedMinusFlow S (circleFlowGeometry C Θ) Q.cutoff := by
  exact n04Realization_compose_fixed_start (circleFlowGeometry C)
    (N01Properties D T S) (N01PrimitiveGeometry D T S)
    (fun C' => ∀ m, Ioo (C'.left m) (C'.right m) ⊆ D.cells (C'.cell m))
    (n04RealizationOpticalFieldStartAt D T S)
    (n04Realization_retainedN01_with_host hT hS hA hG hE hhost)
    (fun C' base loss ε hN => by
      obtain ⟨R, hR⟩ := hN.exists_returnEquation hS hT
      obtain ⟨base', ε', hb, hε', _hε'ε, hfield⟩ :=
        n04Realization_exists_opticalField_through03 hT hS hN hR
      exact ⟨R, base', ε', hb, hε', hfield⟩)

/-- Assemble on an abstract reference before the retained connected
reference is substituted. The optical tail stays unopened. -/
private theorem n04Realization_fieldStart_of_partA
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hA : N01PartA D T S C) (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r : ℝ, 1 ≤ T.E0 r)
    (hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) :
    n04RealizationRetainedFieldStart D := by
  obtain ⟨Θ, R, base, loss, ε, hbase, hε, hG', hhost', hfield⟩ :=
    n04Realization_partA_through03 hT hS hA hG hE hhost
  exact ⟨T, S, circleFlowGeometry C Θ, R, base, loss, ε,
    hT, hS, hE, hG', hhost', hbase, hε, hfield⟩

private theorem n04Realization_seedConstruction_fieldStart
    {q : ℝ} (Q : SeedReferenceConstruction q) (hq : 0 < q)
    (hD : IsRadialReference Q.reference)
    (hraw : (Q.selected.family Q.selected.sigma).cellIndex =
      morseTwoTailAt Q.selected.chain.index (fun _ k => Q.selected.chain.index + k)) :
    n04RealizationRetainedFieldStart Q.reference := by
  obtain ⟨T, S, C, hT, hS, hA, _henumeration, hhost, hE, hG⟩ :=
    Q.exists_n05RetainedN01a hq hD hraw
  exact n04Realization_fieldStart_of_partA hT hS hA hG hE hhost

/-- The caller's retained reference is unchanged. The returned field,
its primitive geometry and its global material floor belong to one
jointly constructed witness. -/
theorem n04Realization_retainedSeed_through03
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length)
    (hselected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2)
    (hq : 0 < q) {Γ : ConnectedReferenceGeometry}
    (hw : Γ.reference.w = P.pair.profile)
    (hphi : Γ.reference.phi = P.pair.height)
    (hD : IsRadialReference Γ.reference)
    (hconstruction : RadialConstructionGeometry Γ.reference)
    (hcoordinates : R11aRetainedCoordinates P Γ) :
    (∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
      ∀ side : Bool, n04PositiveEndpoint i side ∈ radialCore Γ.reference ∧
        deriv Γ.reference.w (n04PositiveEndpoint i side) = 0 ∧
        deriv (deriv Γ.reference.w) (n04PositiveEndpoint i side) ≠ 0) ∧
    ∃ T : MaterialData, ∃ S : PhysicalSpacesData, ∃ C : NonlinearGeometryData S,
      ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
        IsMaterialData Γ.reference T ∧ IsPhysicalSpaces Γ.reference T S ∧
        (∀ r : ℝ, 1 ≤ T.E0 r) ∧ N01PrimitiveGeometry Γ.reference T S C ∧
        (∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m)) ∧
        4 ≤ base ∧ 0 < ε ∧
        ∃ Q : N04bOpticalCutoffData Γ.reference S C base ε,
        ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
          NonlinearPropertiesThrough03 Γ.reference T S C R (Q.field E) base loss ε ∧
          N04bFieldRegularity Γ.reference S C (Q.field E) base ε ∧
          (Q.field E).coefficients = returnCorrectedCoefficients Γ.reference S C Q.cutoff ∧
          (Q.field E).minusFlow = returnCorrectedMinusFlow S C Q.cutoff := by
  change (∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
    ∀ side : Bool, n04PositiveEndpoint i side ∈ radialCore Γ.reference ∧
      deriv Γ.reference.w (n04PositiveEndpoint i side) = 0 ∧
      deriv (deriv Γ.reference.w) (n04PositiveEndpoint i side) ≠ 0) ∧
        n04RealizationRetainedFieldStart Γ.reference
  obtain ⟨Q₀, hreference, hselected_eq, _hretained, _hprofile, _hheight⟩ :=
    exists_n05_seedReferenceConstruction_of_retained P hselected hband
      hw hphi hD.1 hconstruction hcoordinates
  refine ⟨fun i side =>
    n04Realization_seed_positive_endpoints_sameReference Q₀ hreference i side, ?_⟩
  have hQ₀ : IsRadialReference Q₀.reference := by
    simpa only [hreference] using hD
  have hraw : (S₀.family S₀.sigma).cellIndex =
      morseTwoTailAt S₀.chain.index (fun _ k => S₀.chain.index + k) := by
    obtain ⟨_e, _N, _hN, hraw, _hrest⟩ := hcoordinates
    exact hraw
  have hrawQ₀ : (Q₀.selected.family Q₀.selected.sigma).cellIndex =
      morseTwoTailAt Q₀.selected.chain.index (fun _ k => Q₀.selected.chain.index + k) := by
    simpa only [hselected_eq] using hraw
  simpa only [hreference] using
    n04Realization_seedConstruction_fieldStart Q₀ hq hQ₀ hrawQ₀

/-- The closed R11a construction retains its actual pair, reference and
coordinate metadata all the way to the literal corrected physical field. -/
theorem n04Realization_exists_retained_fieldStart :
    ∃ S₀ : SelectedTailData, ∃ K₀ : SeedCentralCutoff,
      ∃ Cstar : ℝ, ∃ requested : ℕ, ∃ length : ℝ,
      ∃ metadata : R10aSelectedMetadata Cstar requested S₀,
      ∃ P : SeedRetainedPair S₀ K₀ 1 length, ∃ Γ : ConnectedReferenceGeometry,
        4096 ≤ S₀.chain.index ∧ Γ.Realizes ∧
        Γ.reference.w = P.pair.profile ∧ Γ.reference.phi = P.pair.height ∧
        RadialConstructionGeometry Γ.reference ∧
        R11aRetainedCoordinates P Γ ∧ IsRadialReference Γ.reference ∧
        (∀ i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w),
          ∀ side : Bool, n04PositiveEndpoint i side ∈ radialCore Γ.reference ∧
            deriv Γ.reference.w (n04PositiveEndpoint i side) = 0 ∧
            deriv (deriv Γ.reference.w) (n04PositiveEndpoint i side) ≠ 0) ∧
        ∃ T : MaterialData, ∃ S : PhysicalSpacesData, ∃ C : NonlinearGeometryData S,
          ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
            IsMaterialData Γ.reference T ∧ IsPhysicalSpaces Γ.reference T S ∧
            (∀ r : ℝ, 1 ≤ T.E0 r) ∧ N01PrimitiveGeometry Γ.reference T S C ∧
            (∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m)) ∧
            4 ≤ base ∧ 0 < ε ∧
            ∃ Q : N04bOpticalCutoffData Γ.reference S C base ε,
            ∃ E : AnnularState S × ℝ → CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source,
              NonlinearPropertiesThrough03 Γ.reference T S C R (Q.field E) base loss ε ∧
              N04bFieldRegularity Γ.reference S C (Q.field E) base ε ∧
              (Q.field E).coefficients =
                returnCorrectedCoefficients Γ.reference S C Q.cutoff ∧
              (Q.field E).minusFlow = returnCorrectedMinusFlow S C Q.cutoff := by
  obtain ⟨_B, _C₀, _K₀, _B₀, _T, _models,
      _hC₀, _hK₀, _hB₀, _hT, _hwindow, _hcap,
      _hfar, _hbuffers, _henergy, _hrem, _herror,
      _CM, _KM, Cstar, requested, S₀, metadata,
      _hCM, _hKM, _hCstar, hindex, _hmodels,
      _η, _Kfirst, _ε, H, K₀, P, Γ,
      _hη, _hη48, _hKfirst, _hε, _hsmall, _hH,
      _hselected, _hhead, hΓ, hw, hphi,
      _hleft, _hright, _hTL, _hTR, _hcolumn, _hcentral, _hcentralHeight,
      hconstruction, hcoordinates, hreference, _hfamily⟩ :=
    n05_exists_retained_radial_reference
  refine ⟨S₀, K₀, Cstar, requested, H + 1, metadata, P, Γ,
    hindex, hΓ, hw, hphi, hconstruction, hcoordinates, hreference, ?_⟩
  exact n04Realization_retainedSeed_through03 P metadata.selected metadata.first_two
    zero_lt_one hw hphi hreference hconstruction hcoordinates

end ContinuousFlexibility.Analysis
