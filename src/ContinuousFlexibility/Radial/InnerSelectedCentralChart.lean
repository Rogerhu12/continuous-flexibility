import ContinuousFlexibility.Radial.InnerSelectedPhysicalGeometry
import ContinuousFlexibility.Radial.InnerCentralPhysicalChart
import ContinuousFlexibility.Radial.InnerPhysicalModelSelection

/-!
# The same selected central model in the actual physical geometry

The raw central profile supplies its positive interval and its single
temporary mode-two column. The chart uses the already selected central
compression witness. Its physical cut energies, conormal error, inverse
cost and weighted Poisson columns are properties of this same chart.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace Matrix.Norms.L2Operator

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)

/-- The full physical central interval is inside the original radial
core, as follows from its two actual endpoints. -/
include P in
theorem central_interval_core :
    Ioo (centralRadius (-X₀)) (centralRadius X₀) ⊆ radialCore D := by
  have horder : -X₀ ≤ X₀ := by linarith only [P.cut_pos]
  have hl := P.central_core (left_mem_Icc.mpr horder)
  have hr := P.central_core (right_mem_Icc.mpr horder)
  intro r hmem
  exact ⟨hl.1.trans hmem.1, hmem.2.trans hr.2⟩

/-- The same compact central border at mode two, and zero at every
other even mode. No final reference column is substituted. -/
def centralColumn (q : ℕ) (hsupport : innerCentralModelBorderRadius < X₀) :
    RadialModeL2 D :=
  innerCentralActiveColumn D q hsupport P.centralHeight_pos
    P.central_interval_core P.central_profile

section CentralModel

variable {C K η : ℝ} (hfamily : InnerCentralPhysicalFamily C K X₀ η)
  (hX : 8 ≤ X₀) (hsupport : innerCentralModelBorderRadius < X₀)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (central : Fin (n + 1))
  (q : ℕ) (hq : 1 ≤ q)
  (hleft : G.left central = centralRadius (-X₀))
  (hright : G.right central = centralRadius X₀)

/-- The actual chart of the one central model selected from the
ordered R09 family. Its input contains no inverse or norm conclusion. -/
def centralModel :
    InnerRadialModelChart D G (decide (q = 1)) ((2 : ℝ) * q) central
      (P.centralColumn q hsupport) central :=
  innerCentralPhysicalModelChart D G central q hX hsupport P.centralHeight_pos
    P.central_interval_core P.central_profile hleft hright
    (innerSelectedCentralModel_hypotheses hfamily q hq)
    (innerSelectedCentralModel hfamily q hq)

/-- The physical cut coefficient includes the exact signed density
drift already present in the central model energy. -/
theorem centralModel_kappa :
    (P.centralModel hfamily hX hsupport G central q hq hleft hright).kappa =
      innerPhysicalCutKappa P.centralHeight
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i))
        (innerCentralModelCutEnergy (innerSelectedCentralModel hfamily q hq)) := by
  funext i
  simpa only [centralModel] using
    innerCentralPhysicalModelChart_kappa D G central q hX hsupport
      P.centralHeight_pos P.central_interval_core P.central_profile hleft hright
      (innerSelectedCentralModel_hypotheses hfamily q hq)
      (innerSelectedCentralModel hfamily q hq) i

theorem centralModel_kappa_pos (i : Fin 2) :
    0 < (P.centralModel hfamily hX hsupport G central q hq hleft hright).kappa i := by
  rw [P.centralModel_kappa hfamily hX hsupport G central q hq hleft hright,
    innerPhysicalCutKappa]
  exact mul_pos
    (mul_pos P.centralHeight_pos
      (sq_pos_of_pos (centralDensityRoot_pos (bufferCut (innerCentralBufferData q X₀) i))))
    (innerSelectedCentralModel_cutEnergy_pos hfamily q hq i)

/-- The error is exactly the conormal error of that same selected
model, with its actual physical height and density. -/
theorem centralModel_errorMatrix :
    (P.centralModel hfamily hX hsupport G central q hq hleft hright).errorMatrix =
      (innerSelectedCentralModel hfamily q hq).physicalFluxError P.centralHeight
        (fun i => centralDensityRoot (bufferCut (innerCentralBufferData q X₀) i)) := by
  simp only [centralModel, InnerRadialModelChart.errorMatrix, innerCentralPhysicalModelChart]

/-- Both signs retain the same physical matrix and the central cut
weight one. The estimate comes from the selected R09 witness. -/
theorem centralModel_error_lt (sign : Bool) :
    ‖innerTwoCutWeightedError
      (P.centralModel hfamily hX hsupport G central q hq hleft hright).kappa
      (fun _ => 1)
      (P.centralModel hfamily hX hsupport G central q hq hleft hright).errorMatrix sign‖ < η := by
  rw [P.centralModel_kappa hfamily hX hsupport G central q hq hleft hright,
    P.centralModel_errorMatrix hfamily hX hsupport G central q hq hleft hright]
  exact innerSelectedCentralModel_error hfamily q hq P.centralHeight_pos sign

theorem centralModel_error_le (sign : Bool) :
    ‖innerTwoCutWeightedError
      (P.centralModel hfamily hX hsupport G central q hq hleft hright).kappa
      (fun _ => 1)
      (P.centralModel hfamily hX hsupport G central q hq hleft hright).errorMatrix sign‖ ≤ η :=
  (P.centralModel_error_lt hfamily hX hsupport G central q hq hleft hright sign).le

/-- The actual Hilbert Dirichlet operator stored in the chart has the
fixed central cost, independent of every later number of cells. -/
theorem centralModel_dirichlet_norm_le (hC : 0 ≤ C) :
    ‖(P.centralModel hfamily hX hsupport G central q hq hleft hright).dirichlet‖ ≤
      innerCentralDirichletConstant X₀ C := by
  simpa only [centralModel] using
    innerCentralPhysicalModelChart_dirichlet_cost D G central q hX hsupport
      P.centralHeight_pos P.central_interval_core P.central_profile hleft hright
      (innerSelectedCentralModel_hypotheses hfamily q hq)
      (innerSelectedCentralModel hfamily q hq) hq hC

/-- The column in the physical dictionary is the same column covered
by the original selected central estimate. -/
theorem centralModel_column (i : Fin 2) :
    (P.centralModel hfamily hX hsupport G central q hq hleft hright).column i =
      innerCentralPhysicalPoissonColumn D hX
        (innerSelectedCentralModel_hypotheses hfamily q hq)
        (innerSelectedCentralModel hfamily q hq) P.centralHeight_pos
        P.central_interval_core P.central_profile i := by
  simpa only [centralModel] using
    innerCentralPhysicalModelChart_column D G central q hX hsupport
      P.centralHeight_pos P.central_interval_core P.central_profile hleft hright
      (innerSelectedCentralModel_hypotheses hfamily q hq)
      (innerSelectedCentralModel hfamily q hq) i

/-- Every bounded physical weight equal to one on the central model
has the same normalized column bound. In particular both reciprocal
global signs satisfy this estimate without changing the model. -/
theorem centralModel_column_norm_le
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hmiddle : ∀ x ∈ Icc (-X₀) X₀, W (centralRadius x) = 1)
    (i : Fin 2) :
    ‖(Real.sqrt
        ((P.centralModel hfamily hX hsupport G central q hq hleft hright).kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
        ((P.centralModel hfamily hX hsupport G central q hq hleft hright).column i)‖ ≤
      innerCentralPoissonConstant / ((2 : ℝ) * q) := by
  rw [P.centralModel_kappa hfamily hX hsupport G central q hq hleft hright,
    P.centralModel_column hfamily hX hsupport G central q hq hleft hright]
  exact innerSelectedCentralModel_poisson_bound hfamily q hq hX
    (innerSelectedCentralModel_hypotheses hfamily q hq)
    D P.centralHeight P.centralHeight_pos P.central_interval_core P.central_profile
    W hW CW hWC hmiddle i

end CentralModel

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
