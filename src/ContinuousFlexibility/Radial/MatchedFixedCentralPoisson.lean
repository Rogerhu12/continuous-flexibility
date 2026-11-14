module

public import ContinuousFlexibility.Radial.FixedCentralModelColumnCost
public import ContinuousFlexibility.Radial.InnerCentralPhysicalPoisson

/-!
# The actual fixed central chart has a uniform weighted Poisson cost

The chart is the original fixedCentralPhysicalModelChart. The stronger
remainder chosen before the geometry removes the polynomial frequency
cost, for both signs of any actual weight equal to one in the center.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

section Chart

variable (B : FixedCentralBorder) (D : ReferenceData)
  (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
  {n : ℕ} (G : InnerRadialChainGeometry D n) (central : Fin (n + 1))
  (q : ℕ) {T B₀ C K : ℝ} (hT : 8 ≤ T)
  (hcap : sqrt centralOscillatorA + 2 ≤ T)
  (hcolumn : referenceColumn D = fixedCentralColumn B.chi)
  (hcore : Ioo (centralRadius (-T)) (centralRadius T) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc (-T) T,
    D.w (centralRadius x) = 1 * centralDensityRoot x ^ 2 * deriv centralRadius x)
  (hleft : G.left central = centralRadius (-T))
  (hright : G.right central = centralRadius T)
  (hB : BufferHypotheses (B.modelBuffer q T B₀))
  (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)

local notation "A" => fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
  hcolumn hcore hw hleft hright hB M

theorem matchedFixedCentralModelChart_weighted_column_bound (hq : 1 ≤ q)
    (henergy : ∀ i, 0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i)
    (hrem : ∀ i, (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
      (innerBufferRemainderEnvelope (B.modelBuffer q T B₀) C K i /
        sqrt (fixedCentralModelCutEnergy M i)) ≤ 1 / (2 * (q : ℝ)))
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hmiddle : ∀ x ∈ Icc (-T) T, W (centralRadius x) = 1) (i : Fin 2) :
    ‖(sqrt ((A).kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) ((A).column i)‖ ≤
      innerCentralPoissonConstant / (2 * (q : ℝ)) := by
  have hj := innerCentralBuffer_frequency hq
  have hjpos : (0 : ℝ) < 2 * (q : ℝ) := (by norm_num : (0 : ℝ) < 2).trans_le hj
  have hU := innerCentralBuffer_velocity_nonneg hT
  have hbuffer : ∀ x ∈ uIcc (bufferCut (B.modelBuffer q T B₀) i)
      (bufferInnerWall (B.modelBuffer q T B₀) i),
      |deriv centralRadius x / centralRadius x| ≤ centralRadiusWeightConstant * (1 + T) :=
    fun _ hx => innerCentralBuffer_velocity (innerBuffer_closedSpan_subset hB i hx)
  have hconstant : ∀ x ∈ uIcc (bufferCut (B.modelBuffer q T B₀) i)
      (bufferInnerWall (B.modelBuffer q T B₀) i), W (centralRadius x) = 1 :=
    fun x hx => hmiddle x (innerBuffer_closedSpan_subset hB i hx)
  have hcell : ∀ x ∈ Ioo (B.modelBuffer q T B₀).l (B.modelBuffer q T B₀).h,
      |W (centralRadius x)| ≤ (1 : ℝ) * 1 := by
    intro x hx
    rw [hmiddle x (Ioo_subset_Icc_self hx)]
    norm_num
  have hvelocity : (centralRadiusWeightConstant * (1 + T)) /
      (B.modelBuffer q T B₀).mass i ≤
      (8 * centralRadiusWeightConstant) / (2 * (q : ℝ)) := by
    simpa only [FixedCentralBorder.modelBuffer, centralModelBuffer, centralBufferMass,
      innerCentralCapMass] using innerCentralBuffer_velocity_over_mass hq hT
  have hnorm := innerModelPhysicalPoissonColumn_frequency_bound D hB M
    (by norm_num : (0 : ℝ) < 1) contDiff_centralRadius contDiff_centralDensityRoot
    (fixedCentralModel_chart_positive T) hcore hw
    (centralRadiusWeightConstant * (1 + T)) hU
    (fun _ hx => innerCentralBuffer_velocity hx) W hW CW hWC i
    (ratio := 1) (w := 1) (Ucap := centralRadiusWeightConstant * (1 + T))
    (k := fixedCentralModelCutEnergy M i) (j := 2 * (q : ℝ))
    (Kcap := 8 * centralRadiusWeightConstant)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) hU
    (henergy i).1 hjpos (mul_nonneg (by norm_num) centralRadiusWeightConstant_pos.le)
    (fun _ => rfl) hconstant hbuffer hcell (henergy i).2 hvelocity
    (by simpa only [mul_one] using hrem i)
  rw [fixedCentralPhysicalModelChart_kappa]
  simpa only [fixedCentralModelPhysicalKappa, InnerRadialModelChart.column,
    fixedCentralPhysicalModelChart, innerPhysicalCutKappa, innerCentralPoissonConstant,
    one_mul] using hnorm

end Chart

end ContinuousFlexibility.Radial
