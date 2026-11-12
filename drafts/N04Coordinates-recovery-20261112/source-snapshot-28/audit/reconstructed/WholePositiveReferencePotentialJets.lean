import ContinuousFlexibility.Analysis.ActualPositiveReferencePotentialMaterialJets
import ContinuousFlexibility.Analysis.WholePositiveReferencePrincipal
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Actual whole-atlas potential and its scalar flux jets

The stored positive reference potential agrees with the flux expression
for the same reference coordinate and height. This is a neighborhood
equality on the actual canonical open piece, so it transports all mixed
derivatives. No smoothness of an unrelated total coefficient extension is
assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

private theorem radialReferencePotential_flux_formula
    {w Y H : ℝ → ℝ} {l r : ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
      (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1)
    (x : ℝ) :
    -(H (Function.invFun Y x) *
      deriv (fun t => w t * deriv H t) (Function.invFun Y x) /
        deriv Y (Function.invFun Y x)) =
      -(H (Function.invFun Y x) *
        deriv ((fun t => w t * deriv H t) ∘ Function.invFun Y) x) := by
  let χ : ℝ → ℝ := Function.invFun Y
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hgeometry.chart_smooth.fst.comp hline
  have hH : ContDiff ℝ ∞ H := by
    simpa only [Function.comp_def] using hgeometry.height_smooth.comp hline
  have hχ : ContDiff ℝ ∞ χ := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
      hgeometry.inverse_smooth.fst.comp hline
  have hYpos : 0 < deriv Y (χ x) := by
    simpa only [planeJacobian_positiveReferenceCylinderChart
      (hY.differentiable (by simp) (χ x))] using
      hgeometry.jacobian_positive (χ x, 0)
  have hright (t : ℝ) : Y (χ t) = t :=
    congrArg Prod.fst (hgeometry.right_inverse (t, 0))
  have hχderiv : deriv χ x = (deriv Y (χ x))⁻¹ :=
    (HasDerivAt.of_local_left_inverse hχ.continuous.continuousAt
      (hY.differentiable (by simp) (χ x)).hasDerivAt hYpos.ne'
      (Eventually.of_forall hright)).deriv
  have hflux : ContDiff ℝ ∞ (fun t => w t * deriv H t) :=
    hw.mul (contDiff_infty_iff_deriv.mp hH).2
  have hchain : deriv ((fun t => w t * deriv H t) ∘ χ) x =
      deriv (fun t => w t * deriv H t) (χ x) * (deriv Y (χ x))⁻¹ := by
    rw [deriv_comp x (hflux.differentiable (by simp) (χ x))
      (hχ.differentiable (by simp) x), hχderiv]
  change -(H (χ x) * deriv (fun t => w t * deriv H t) (χ x) / deriv Y (χ x)) =
    -(H (χ x) * deriv ((fun t => w t * deriv H t) ∘ χ) x)
  rw [hchain, div_eq_mul_inv]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e₀ : ℕ ≃ N04PieceIndex D) (e : ℕ ≃ N04WholePieceIndex D)
  (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
  (Y H : N04PositiveComponent D.a D.b (deriv D.w) → ℝ → ℝ)
  (τ σ : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
  (Q : (AnnularState S × ℝ) →
    N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
  (N : Set ℝ)

theorem n04WholeReferenceGaugeAtlasData_positive_reference_potential_flux_germ
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    {p : PolarPoint}
    (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j q => H j q.1) τ σ Q N) m) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j q => H j q.1) τ σ Q N
    V.potential (C.referenceState, 0) m =ᶠ[𝓝 p]
      (fun q : PolarPoint => -(H i (Function.invFun (Y i) q.1) *
        deriv ((fun r => D.w r * deriv (H i) r) ∘ Function.invFun (Y i)) q.1)) := by
  let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
    e cell (fun j => positiveReferenceCylinderChart (Y j))
    (fun j => positiveReferenceCylinderInverse (Y j))
    (fun j q => H j q.1) τ σ Q N
  have hopen : IsOpen (canonicalOpen S V m) := isOpen_Ioo.prod isOpen_univ
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hv := (n04WholeReferenceGaugeAtlasData_positive_reference_formulas
    hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi hgeometry href hq).2.2.2.1
  exact hv.trans (radialReferencePotential_flux_formula
    (n04b_profileGeometry_of_through03 hN).2.2.1.1 hgeometry q.1)

theorem n04WholeReferenceGaugeAtlasData_positive_reference_potential_mixed
    (m : ℕ) (i : N04PositiveComponent D.a D.b (deriv D.w)) (hi : e m = .inr i)
    (hgeometry : PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (href : τ (C.referenceState, 0) i = id ∧
      σ (C.referenceState, 0) i = id ∧ Q (C.referenceState, 0) i = (fun _ => 1))
    {p : PolarPoint}
    (hp : p ∈ canonicalOpen S
      (n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
        e cell (fun j => positiveReferenceCylinderChart (Y j))
        (fun j => positiveReferenceCylinderInverse (Y j))
        (fun j q => H j q.1) τ σ Q N) m) (a b : ℕ) :
    let V := n04WholeReferenceGaugeAtlasData C L (n04bActualTypedAtlas hT hS hN hfield e₀)
      e cell (fun j => positiveReferenceCylinderChart (Y j))
      (fun j => positiveReferenceCylinderInverse (Y j))
      (fun j q => H j q.1) τ σ Q N
    mixedDerivative a b (V.potential (C.referenceState, 0) m) p =
      if b = 0 then iteratedDeriv a
        (fun t => -(H i (Function.invFun (Y i) t) *
          deriv ((fun r => D.w r * deriv (H i) r) ∘ Function.invFun (Y i)) t)) p.1
      else 0 := by
  exact (mixedDerivative_eq_of_germ
    (n04WholeReferenceGaugeAtlasData_positive_reference_potential_flux_germ
      hT hS hN hfield e₀ e cell Y H τ σ Q N m i hi hgeometry href hp) a b).trans
    (n08_mixedDerivative_radial
      (fun t => -(H i (Function.invFun (Y i) t) *
        deriv ((fun r => D.w r * deriv (H i) r) ∘ Function.invFun (Y i)) t)) a b p)

end ContinuousFlexibility.Analysis
