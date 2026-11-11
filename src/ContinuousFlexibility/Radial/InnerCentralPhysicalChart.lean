import ContinuousFlexibility.Radial.InnerRadialActualPieces
import ContinuousFlexibility.Radial.InnerCentralPhysicalColumn
import ContinuousFlexibility.Radial.InnerCentralPhysicalPoisson

/-!
# The fixed central model as an actual finite-chain piece

The central chart is the original integral-defined radius and density.
Its scalar column is the original compact auxiliary column at mode two
and zero otherwise. Its physical coefficient, full conormal drift, and
Dirichlet bound all refer to the same localized model and radial measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (central : Fin (n + 1)) (q : ℕ) {X₀ height C K : ℝ}
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  (hh : 0 < height)
  (hcore : Ioo (centralRadius (-X₀)) (centralRadius X₀) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-X₀) X₀,
    D.w (centralRadius x) = height * centralDensityRoot x ^ 2 * deriv centralRadius x)
  (hleft : G.left central = centralRadius (-X₀))
  (hright : G.right central = centralRadius X₀)
  (hB : BufferHypotheses (innerCentralBufferData q X₀))
  (M : InnerBufferLocalizedData (innerCentralBufferData q X₀) C K)

/-- The only temporary scalar column occurs at the actual second mode. -/
def innerCentralActiveColumn : RadialModeL2 D :=
  if q = 1 then innerCentralPhysicalTemporaryColumn D hh hsupport hcore hw else 0

/-- The original central chart with its same compressed inverse. The
operator and scalar row use the same fixed auxiliary column. -/
def innerCentralPhysicalModelChart :
    InnerRadialModelChart D G (decide (q = 1)) (2 * q) central
      (innerCentralActiveColumn D q hsupport hh hcore hw) central where
  buffer := innerCentralBufferData q X₀
  buffer_hypotheses := hB
  C := C
  K := K
  localized := M
  radius := centralRadius
  scale := centralDensityRoot
  height := height
  height_pos := hh
  radius_smooth := contDiff_centralRadius
  scale_smooth := contDiff_centralDensityRoot
  chart_pos := innerCentralBuffer_chart_pos q X₀
  in_core := hcore
  weight_identity := hw
  U := centralRadiusWeightConstant * (1 + X₀)
  U_nonneg := innerCentralBuffer_velocity_nonneg hX
  log_deriv_bound := innerCentralBuffer_chart_velocity q X₀
  potential_identity := by
    intro x _
    simp only [innerCentralBufferData, centralPotential, centralRadius_liouvilleRho,
      centralDensityRoot_liouvilleV0]
    ring
  left_eq := hleft
  right_eq := hright
  bordered_eq := by simp only [innerCentralBufferData, eq_self_iff_true, ite_true]
  column_eq := by
    intro _
    by_cases hq : q = 1
    · simp only [innerCentralBufferData, innerCentralActiveColumn, if_pos hq,
        innerCentralPhysicalTemporaryColumn]
    · simp only [innerCentralBufferData, innerCentralActiveColumn, if_neg hq, map_zero]

def innerCentralDirichletConstant (X₀ C : ℝ) : ℝ :=
  (sqrt 2 * (sqrt 12 + 1) ^ 2 * (1 + 2 * C)) * innerCentralBufferCoefficient X₀ C ^ 4

theorem innerCentralDirichletConstant_nonneg {X₀ C : ℝ} (hC : 0 ≤ C) :
    0 ≤ innerCentralDirichletConstant X₀ C := by
  unfold innerCentralDirichletConstant
  positivity

/-- With the central cut fixed, its actual Dirichlet cost is independent
of the frequency and of every later number of retained Morse cells. -/
theorem innerCentralPhysicalModelChart_dirichlet_cost (hq : 1 ≤ q) (hC : 0 ≤ C) :
    ‖(innerCentralPhysicalModelChart D G central q hX hsupport hh hcore hw
      hleft hright hB M).dirichlet‖ ≤ innerCentralDirichletConstant X₀ C := by
  have hc := innerCentralBufferCoefficient_bounds hq hX hC
  dsimp only [innerCentralPhysicalModelChart, InnerRadialModelChart.dirichlet,
    innerCentralDirichletConstant]
  exact innerLiouvilleHilbertDirichlet_coefficient_cost D hB.1.le hh
    contDiff_centralRadius contDiff_centralDensityRoot (innerCentralBuffer_chart_pos q X₀)
    hcore hw (centralRadiusWeightConstant * (1 + X₀))
    (innerCentralBuffer_velocity_nonneg hX) (innerCentralBuffer_chart_velocity q X₀)
    M hB hC hc.1 hc.2.1 hc.2.2.2.1 hc.2.2.2.2.2

/-- The same physical column in the dictionary is the actual weighted
Poisson column already estimated in the original radial measure. -/
theorem innerCentralPhysicalModelChart_column (i : Fin 2) :
    (innerCentralPhysicalModelChart D G central q hX hsupport hh hcore hw
      hleft hright hB M).column i =
      innerCentralPhysicalPoissonColumn D hX hB M hh hcore hw i := by
  simp only [innerCentralPhysicalModelChart, InnerRadialModelChart.column,
    innerCentralPhysicalPoissonColumn]

/-- The central leading cut energy retains the exact signed density
drift in the physical finite-chain dictionary. -/
theorem innerCentralPhysicalModelChart_kappa (i : Fin 2) :
    (innerCentralPhysicalModelChart D G central q hX hsupport hh hcore hw
      hleft hright hB M).kappa i =
      innerPhysicalCutKappa height
        (fun k => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) k))
        (innerCentralModelCutEnergy M) i := by
  simp only [innerCentralPhysicalModelChart, InnerRadialModelChart.kappa]
  exact (innerCentralModelPhysicalKappa_eq M height i).symm

end ContinuousFlexibility.Radial
