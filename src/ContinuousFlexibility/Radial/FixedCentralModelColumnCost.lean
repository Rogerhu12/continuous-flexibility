import ContinuousFlexibility.Radial.FixedCentralModelSmallError
import ContinuousFlexibility.Radial.InnerModelPoissonNormalization
import ContinuousFlexibility.Radial.InnerLiouvilleConormal

/-!
# Actual fixed-central Poisson column costs

The finite constant below uses only the already constructed model
columns and the fixed model radius.  It is independent of every later
radial gluing parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

def fixedCentralModelColumnEnvelope {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (i : Fin 2) : ℝ :=
  sqrt 12 * ((centralRadiusWeightConstant * (1 + T)) /
      (B.modelBuffer q T B₀).mass i) *
      (sqrt (M.column i).inwardEnergy / sqrt (fixedCentralModelCutEnergy M i)) +
    (sqrt 12 * (centralRadiusWeightConstant * (1 + T)) + 1) *
      (innerBufferRemainderEnvelope (B.modelBuffer q T B₀) C K i /
        sqrt (fixedCentralModelCutEnergy M i))

def fixedCentralModelColumnCost {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (j : ℝ) : ℝ :=
  |j| * max 0 (max (fixedCentralModelColumnEnvelope M 0)
    (fixedCentralModelColumnEnvelope M 1))

theorem fixedCentralModelColumnCost_nonneg {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (j : ℝ) : 0 ≤ fixedCentralModelColumnCost M j :=
  mul_nonneg (abs_nonneg j) (le_max_left _ _)

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

theorem fixedCentralPhysicalModelChart_kappa (i : Fin 2) :
    (fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap hcolumn hcore hw
      hleft hright hB M).kappa i = fixedCentralModelPhysicalKappa M i := by
  change 1 * centralDensityRoot _ ^ 2 *
      ((M.column i).inwardEnergy + innerLiouvilleBoundaryDrift
        centralDensityRoot (bufferCut (B.modelBuffer q T B₀)) i) = _
  unfold fixedCentralModelPhysicalKappa innerPhysicalCutKappa fixedCentralModelCutEnergy
    innerLiouvilleBoundaryDrift
  rw [deriv_centralDensityRoot]
  field_simp [(centralDensityRoot_pos (bufferCut (B.modelBuffer q T B₀) i)).ne']
  <;> ring

theorem fixedCentralPhysicalModelChart_errorMatrix :
    (fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap hcolumn hcore hw
      hleft hright hB M).errorMatrix =
      M.physicalFluxError 1
        (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i)) := rfl

include hT in
theorem fixedCentralPhysicalModelChart_column_bound
    (hk : ∀ i, 0 < fixedCentralModelCutEnergy M i) {j : ℝ} (hj : 0 < j)
    (i : Fin 2) :
    ‖(sqrt ((fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
        hcolumn hcore hw hleft hright hB M).kappa i))⁻¹ •
      (fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap
        hcolumn hcore hw hleft hright hB M).column i‖ ≤
      fixedCentralModelColumnCost M j / j := by
  let A := fixedCentralPhysicalModelChart B D hD hborder G central q hT hcap hcolumn
    hcore hw hleft hright hB M
  have hqpos : 0 < 2 * (q : ℝ) := by
    have hm := buffer_mass_pos hB 0
    change 0 < 2 * (q : ℝ) * T / 4 at hm
    have hTp : 0 < T := by linarith only [hT]
    by_contra hq
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hq) hTp.le
    nlinarith only [hm, hmul]
  have hbuf (x : ℝ)
      (hx : x ∈ uIcc (bufferCut (B.modelBuffer q T B₀) i)
        (bufferInnerWall (B.modelBuffer q T B₀) i)) :
      x ∈ Icc (-T) T := by
    have hc : bufferCut (B.modelBuffer q T B₀) i ∈ Icc (-T) T := by
      change (if i = 0 then -T else T) ∈ Icc (-T) T
      split_ifs <;> constructor <;> linarith only [hT]
    have hb : bufferInnerWall (B.modelBuffer q T B₀) i ∈ Icc (-T) T := by
      change bufferInnerWall (centralModelBuffer (2 * (q : ℝ)) T B₀
        (centralModelBordered q) B.modelColumn
        (centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi))) i ∈ Icc (-T) T
      rw [centralModelBuffer_innerWall (centralModelBordered q) B.modelColumn
        (centralModelPhysicalColumnFunction 1 (fixedCentralColumn B.chi))
        hqpos (by linarith only [hT])]
      split_ifs <;> constructor <;> linarith only [hT]
    exact ⟨(le_min hc.1 hb.1).trans hx.1, hx.2.trans (max_le hc.2 hb.2)⟩
  have h := innerModelPhysicalPoissonColumn_normalized_bound D hB M A.height_pos
    A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
    A.U A.U_nonneg A.log_deriv_bound
    (fun _ => 1) measurable_const 1 (by simp) i (by norm_num : (0 : ℝ) ≤ 1)
    zero_lt_one A.U_nonneg (hk i) (fun _ => rfl) (fun _ _ => rfl)
    (fun x hx => A.log_deriv_bound x (hbuf x hx)) (by simp)
  have hnorm : ‖(sqrt (A.kappa i))⁻¹ • A.column i‖ ≤
      fixedCentralModelColumnEnvelope M i := by
    simpa only [A, fixedCentralPhysicalModelChart_kappa, fixedCentralModelPhysicalKappa,
      innerPhysicalCutKappa, one_mul, mul_one, innerBorderFieldMap_weight_one,
      ContinuousLinearMap.id_apply, InnerRadialModelChart.column,
      fixedCentralPhysicalModelChart, fixedCentralModelColumnEnvelope] using h
  have hi : fixedCentralModelColumnEnvelope M i ≤
      max 0 (max (fixedCentralModelColumnEnvelope M 0)
        (fixedCentralModelColumnEnvelope M 1)) := by
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  apply (hnorm.trans hi).trans_eq
  unfold fixedCentralModelColumnCost
  rw [abs_of_pos hj]
  field_simp [hj.ne']

end Chart

end ContinuousFlexibility.Radial
