import ContinuousFlexibility.Analysis.N04PositiveGeometryRootInverseLinear
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsCommonContext
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOddPowerIdentity
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsPlaneJets
import ContinuousFlexibility.Analysis.N06CharacteristicRootJets
import ContinuousFlexibility.Analysis.CanonicalClosedInverseJets
import ContinuousFlexibility.Analysis.CircleInverseExistence

/-!
# The original root chart and its inverse first derivative

The unit root model identifies the original physical chart. Its two
columns are expressed in the actual odd and even boundary traces. The
stored canonical inverse then has the triangular differential at the
inverse of the actual root label, with the same radial orientation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped ContDiff Topology

local instance n04RootInverseDifferentialStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- Removing the unit radial orientation from the first jet gives the
two physical columns. No regularity of a choice of model is needed. -/
theorem n04PositiveGeometry_root_firstColumns_of_unit
    {d c : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R τ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R τ G)
    {F : PolarPoint → PolarPoint} (r σ θ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hf : ContDiffAt ℝ ∞ (fun p => F (rootProfileShift r σ p)) (0, θ))
    (hj : iteratedFDeriv ℝ 1 (fun p => F (rootProfileShift r σ p)) (0, θ) =
      iteratedFDeriv ℝ 1 (extendedRootEvenOddChart G) (0, θ)) :
    fderiv ℝ F (r, θ) (1, 0) =
        (σ * n06RootBoundaryScale G θ, σ * radialPartial (extendedRootEven G) (0, θ)) ∧
      fderiv ℝ F (r, θ) (0, 1) = (0, deriv β θ) := by
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hσinv : σ⁻¹ = σ := by rcases hσ with rfl | rfl <;> norm_num
  have he (v : PolarPoint) : fderiv ℝ F (r, θ) v =
      fderiv ℝ (extendedRootEvenOddChart G) (0, θ) (rootProfileInverseLinear σ v) := by
    have h := congrArg (fun A : PolarPoint [×1]→L[ℝ] PolarPoint => A (fun _ => v))
      (n04PositiveGeometry_rootProfileJet_unscale r σ θ hσne F 1 hf)
    rw [hj] at h
    simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      iteratedFDeriv_one_apply] using h
  have hr : rootProfileInverseLinear σ (1, 0) = σ • ((1, 0) : PolarPoint) := by
    simp only [rootProfileInverseLinear, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, hσinv]
  have hθ : rootProfileInverseLinear σ (0, 1) = ((0, 1) : PolarPoint) := by
    simp only [rootProfileInverseLinear, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero]
  constructor
  · rw [he, hr, map_smul, P.n06_chart_radial_zero θ]
    simp only [Prod.smul_mk, smul_eq_mul]
  · rw [he, hθ]
    exact n06_fderiv_angular_of_boundary_value
      ((P.n06_chart_contDiffAt_zero θ).differentiableAt (by simp)) P.extended_chart_zero

private theorem root_firstColumns_of_scalar_traces
    {d c : PolarPoint → ℝ} {β : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {R τ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R τ G)
    (F : PolarPoint → PolarPoint) (r σ θ odd even : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hf : ContDiffAt ℝ ∞ (fun p => F (rootProfileShift r σ p)) (0, θ))
    (hj0 : iteratedFDeriv ℝ 0 (fun p => F (rootProfileShift r σ p)) (0, θ) =
      iteratedFDeriv ℝ 0 (extendedRootEvenOddChart G) (0, θ))
    (hj1 : iteratedFDeriv ℝ 1 (fun p => F (rootProfileShift r σ p)) (0, θ) =
      iteratedFDeriv ℝ 1 (extendedRootEvenOddChart G) (0, θ))
    (hodd : radialBoundaryJet (extendedRootOddCoefficient G) 0 0 θ = odd)
    (heven : radialBoundaryJet (extendedRootEven G) 0 1 θ = even) :
    F (r, θ) = (0, β θ) ∧
      fderiv ℝ F (r, θ) (1, 0) =
        (σ * (((3 / 2 : ℝ) * odd) ^ (2 / 3 : ℝ)), σ * even) ∧
      fderiv ℝ F (r, θ) (0, 1) = (0, deriv β θ) := by
  have ho : rootOddCoefficient G (0, θ) = odd := by
    simpa only [radialBoundaryJet, iteratedDeriv_zero,
      extendedRootOddCoefficient_of_nonneg G (p := (0, θ)) (le_refl (0 : ℝ))] using hodd
  have he : radialPartial (extendedRootEven G) (0, θ) = even := by
    have hreg : ContDiffAt ℝ ∞ (extendedRootEven G) (0, θ) :=
      (P.n06_chart_contDiffAt_zero θ).snd
    have hjet : radialBoundaryJet (extendedRootEven G) 0 1 θ =
        radialPartial (extendedRootEven G) (0, θ) := by
      simpa only [iteratedFDeriv_one_apply, radialPartial] using
        n06_radialBoundaryJet_eq_frechet 1 hreg
    exact hjet.symm.trans heven
  have hv : F (r, θ) = extendedRootEvenOddChart G (0, θ) := by
    have h := congrArg (fun A : PolarPoint [×0]→L[ℝ] PolarPoint => A Fin.elim0) hj0
    simpa only [iteratedFDeriv_zero_apply, rootProfileShift, mul_zero, add_zero] using h
  have hc := n04PositiveGeometry_root_firstColumns_of_unit P r σ θ hσ hf hj1
  refine ⟨hv.trans (P.extended_chart_zero θ), ?_, hc.2⟩
  simpa only [n06RootBoundaryScale, rootRadialFactor, ho, he] using hc.1

def n04PositiveGeometry_rootBoundaryScale
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  ((3 / 2 : ℝ) * n04PositiveGeometry_rootOddTrace D S C g m side 0 y) ^ (2 / 3 : ℝ)

/-- All coefficients are literal functions of the original state and
angle. The model flow is absent from this definition. -/
def n04PositiveGeometry_rootInverseDifferential
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (y : (StateDirections S × ℝ) × ℝ) :
    PolarPoint →L[ℝ] PolarPoint :=
  let β := n01RootLabel S C (liftSectorParameter S C y.1) m side
  let η := Function.invFun β y.2
  n04PositiveGeometry_rootInverseLinear (n01ComponentRootOrientation side)
    (n04PositiveGeometry_rootBoundaryScale D S C g m side (y.1, η))⁻¹
    (n04PositiveGeometry_rootBoundaryFormula D S C g m side 0 (y.1, η))
    (deriv (Function.invFun β) y.2)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- The root model determines the value and both first columns of the
original stored physical chart, using the actual scalar trace packet. -/
theorem n04PositiveGeometry_actual_root_firstColumns
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C x).1)
      (stateHeight D S C (liftSectorParameter S C x))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C x))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C x)) δ) Θ)
    (hmodel : N04PositiveGeometryRootUnitModel D S C K
      (liftSectorParameter S C x) m side g δ Θ) (θ : ℝ) :
    let z := liftSectorParameter S C x
    let r := n01ComponentRoot C m side
    let σ := n01ComponentRootOrientation side
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    K.chart z i (r, θ) = (0, n01RootLabel S C z m side θ) ∧
      fderiv ℝ (K.chart z i) (r, θ) (1, 0) =
        (σ * n04PositiveGeometry_rootBoundaryScale D S C g m side (x, θ),
          σ * n04PositiveGeometry_rootBoundaryFormula D S C g m side 0 (x, θ)) ∧
      fderiv ℝ (K.chart z i) (r, θ) (0, 1) =
        (0, deriv (n01RootLabel S C z m side) θ) := by
  let z := liftSectorParameter S C x
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  have hz := liftSectorParameter_mem_stateNeighborhood (C := C) hx le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector x
  have P := n04PositiveGeometry_actual_unitRootCoordinate_properties
    hT hS hN hflow hz hs m side g hg hR hstrip hδ Θ hΘ
  have H := hmodel θ
  exact root_firstColumns_of_scalar_traces P (K.chart z i) r σ θ
    (n04PositiveGeometry_rootOddTrace D S C g m side 0 (x, θ))
    (n04PositiveGeometry_rootBoundaryFormula D S C g m side 0 (x, θ))
    (n01ComponentRootOrientation_eq side) H.2.1 (H.2.2.2.2.1 0) (H.2.2.2.2.1 1)
    (congrFun (n04PositiveGeometry_actual_oddTrace_eq hT hS hN hflow hx
      m side g hg hR hstrip hδ Θ hΘ 0 (by omega)) θ)
    (congrFun (n04PositiveGeometry_actual_unitRootTrace_eq hT hS hN hflow hx
      m side g hg hR hstrip hδ Θ hΘ 0) θ)

/-- The first derivative belongs to the original inverse chart. Its
off-diagonal term has no remaining orientation factor. -/
theorem n04PositiveGeometry_actual_rootInverse_fderiv_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε)
    (hA : CanonicalGeometry D S C K base ε)
    {x : StateDirections S × ℝ} (hx : x ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (side : Bool) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g
      (stateProfile D S C (liftSectorParameter S C x).1)
      (stateHeight D S C (liftSectorParameter S C x))
      (n01ComponentRoot C m side) (n01ComponentRootOrientation side) R)
    {δ : ℝ} (hδ : δ ≠ 0) (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ)
    (hΘ : N04FlowEquations (rootRescaledField
      (localizedRootDrift D S C (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C x))
      (localizedRootSpeed D S C g (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) hR (liftSectorParameter S C x)) δ) Θ)
    (hmodel : N04PositiveGeometryRootUnitModel D S C K
      (liftSectorParameter S C x) m side g δ Θ) (θ : ℝ) :
    fderiv ℝ (K.inverseChart (liftSectorParameter S C x)
      (if side then (K.cutPair m).2 else (K.cutPair m).1)) (0, θ) =
        n04PositiveGeometry_rootInverseDifferential D S C g m side (x, θ) := by
  let z := liftSectorParameter S C x
  let r := n01ComponentRoot C m side
  let σ := n01ComponentRootOrientation side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let β := n01RootLabel S C z m side
  let η := Function.invFun β θ
  let A := n04PositiveGeometry_rootBoundaryScale D S C g m side (x, η)
  let e := n04PositiveGeometry_rootBoundaryFormula D S C g m side 0 (x, η)
  have hz := liftSectorParameter_mem_stateNeighborhood (C := C) hx le_rfl
  have hs := hN.2.2.1.liftSectorParameter_sector x
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hβlower (ν : ℝ) : (1 / 4 : ℝ) ≤ deriv β ν :=
    (n01RootLabel_deriv_mem_quarter_four hN hflow hz hs m side ν).1
  have hβinv : β η = θ := rightInverse_invFun_of_deriv_lower_bound hquarter hβlower θ
  have hβne : deriv β η ≠ 0 := (hquarter.trans_le (hβlower η)).ne'
  have hb : deriv (Function.invFun β) θ * deriv β η = 1 := by
    rw [(hasDerivAt_invFun_of_deriv_lower_bound hquarter hβlower θ).deriv]
    exact inv_mul_cancel₀ hβne
  have hodd := n04PositiveGeometry_rootOddTrace_zero_pos hT hS hN hflow
    g m side hR hx hstrip η
  have hApos : 0 < A := Real.rpow_pos_of_pos
    (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) hodd) (2 / 3 : ℝ)
  have hcols := n04PositiveGeometry_actual_root_firstColumns hT hS hN hflow hx
    m side g hg hR hstrip hδ Θ hΘ hmodel η
  have hv : K.chart z i (r, η) = (0, θ) := by
    have hv' : K.chart z i (r, η) = (0, β η) := hcols.1
    simpa only [hβinv] using hv'
  have hroot : (r, η) ∈ physicalPieceClosed S K z i := (hmodel η).1
  have hclosed := hA.boundary z hz hs i
  have hq : ((0, θ) : PolarPoint) ∈ canonicalClosed S K i := by
    rw [← hv]
    exact hclosed.1 hroot
  have hpoint : K.inverseChart z i (0, θ) = (r, η) := by
    rw [← hv]
    exact hclosed.2.2.1 _ hroot
  have hf : ContDiffAt ℝ ∞ (K.chart z i) (K.inverseChart z i (0, θ)) :=
    (hclosed.2.2.2.2.1 _ (hclosed.2.1 hq)).1
  have hg' := n04b_inverseChart_contDiffAt_closed hA hz hs i hq
  have hfg := (canonicalClosed_inverse_germs hA hz hs i hq).2
  have hr : fderiv ℝ (K.chart z i) (K.inverseChart z i (0, θ)) (1, 0) =
      (σ * A, σ * e) := by
    rw [hpoint]
    exact hcols.2.1
  have hθ : fderiv ℝ (K.chart z i) (K.inverseChart z i (0, θ)) (0, 1) =
      (0, deriv β η) := by
    rw [hpoint]
    exact hcols.2.2
  change fderiv ℝ (K.inverseChart z i) (0, θ) =
    n04PositiveGeometry_rootInverseLinear σ A⁻¹ e (deriv (Function.invFun β) θ)
  exact n04PositiveGeometry_rootInverse_fderiv_eq hf hg' hfg
    (n01ComponentRootOrientation_eq side) (inv_mul_cancel₀ hApos.ne') hb hr hθ

end ContinuousFlexibility.Analysis
