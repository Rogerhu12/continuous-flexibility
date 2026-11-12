import ContinuousFlexibility.Analysis.N05RetainedReferenceAssembly
import ContinuousFlexibility.Analysis.N05RetainedOpticalLowerAdapter
import ContinuousFlexibility.Analysis.N05RetainedN01a
import ContinuousFlexibility.Analysis.N04RealizationRetainedN01
import ContinuousFlexibility.Analysis.N04RealizationOpticalFieldGateway
import ContinuousFlexibility.Analysis.N01ResidualSmoothTame

/-!
# One retained seed through the actual physical field construction

The original retained pair, connected reference and coordinate certificate
survive the cumulative construction. The existing seed factory supplies
the material data, physical spaces, primitive geometry and global E0
floor. One flow installation completes N01; its fixed return equation
and one optical cutoff then give Through03 on a common neighborhood.

The retained source is `n05_exists_retained_radial_reference`. Its bridge
is `exists_n05_seedReferenceConstruction_of_retained`, followed by
`SeedReferenceConstruction.exists_n05RetainedN01a` and the fixed-record
`N01Properties.exists_returnEquation`.
-/

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
  obtain ⟨Θ, base₀, loss, ε₀, hbase₀, hε₀, hN, hG',
      _hcontrol, hcell, hleft, hright, _htravel, _hreference⟩ :=
    n04Realization_retainedN01 hS hT hA hG hE
  obtain ⟨R, hR⟩ := hN.exists_returnEquation hS hT
  obtain ⟨base, ε, hbase, hε, _hεε₀, hfield⟩ :=
    n04Realization_exists_opticalField_through03 hT hS hN hR
  have hhost' (m : ℕ) : Ioo ((circleFlowGeometry C Θ).left m)
      ((circleFlowGeometry C Θ).right m) ⊆
        D.cells ((circleFlowGeometry C Θ).cell m) := by
    simpa only [hleft, hright, hcell] using hhost m
  exact ⟨Θ, R, base, loss, ε, hbase₀.trans hbase, hε, hG', hhost', hfield⟩

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
  obtain ⟨Q₀, hreference, hselected_eq, _hretained, _hprofile, _hheight⟩ :=
    exists_n05_seedReferenceConstruction_of_retained P hselected hband
      hw hphi hD.1 hconstruction hcoordinates
  have hQ₀ : IsRadialReference Q₀.reference := by
    simpa only [hreference] using hD
  have hraw : (S₀.family S₀.sigma).cellIndex =
      morseTwoTailAt S₀.chain.index (fun _ k => S₀.chain.index + k) := by
    obtain ⟨_e, _N, _hN, hraw, _hrest⟩ := hcoordinates
    exact hraw
  have hrawQ₀ : (Q₀.selected.family Q₀.selected.sigma).cellIndex =
      morseTwoTailAt Q₀.selected.chain.index (fun _ k => Q₀.selected.chain.index + k) := by
    simpa only [hselected_eq] using hraw
  obtain ⟨T, S, C, hT₀, hS₀, hA₀, _henumeration, hhost₀, hE, hG₀⟩ :=
    Q₀.exists_n05RetainedN01a hq hQ₀ hrawQ₀
  have hT : IsMaterialData Γ.reference T := by
    simpa only [hreference] using hT₀
  have hS : IsPhysicalSpaces Γ.reference T S := by
    simpa only [hreference] using hS₀
  have hA : N01PartA Γ.reference T S C := by
    simpa only [hreference] using hA₀
  have hG : N01PrimitiveGeometry Γ.reference T S C := by
    simpa only [hreference] using hG₀
  have hhost : ∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m) := by
    simpa only [hreference] using hhost₀
  obtain ⟨Θ, R, base, loss, ε, hbase, hε, hG', hhost', hfield⟩ :=
    n04Realization_partA_through03 hT hS hA hG hE hhost
  exact ⟨T, S, circleFlowGeometry C Θ, R, base, loss, ε,
    hT, hS, hE, hG', hhost', hbase, hε, hfield⟩

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
