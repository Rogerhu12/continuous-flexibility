import ContinuousFlexibility.Radial.InnerLiouvilleWeights
import ContinuousFlexibility.Radial.InnerBufferWeightedColumn
import ContinuousFlexibility.Radial.InnerBorderWeights

/-!
# Weighted physical columns of the same compressed model

The leading field uses the velocity on its own buffer. The remainder
uses the same Dirichlet inverse as the original Poisson column. The
single scalar is included, and its cut weight is one in the central
model; in every other model it vanishes by the original scalar equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

def innerBufferRemainderEnvelope (B : BufferData) (C K : ℝ) (i : Fin 2) : ℝ :=
  (B.B₀ + C * ∑ k, (B.mass k)⁻¹ ^ 2) *
    (K * (1 + B.layerBound) * B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i))

theorem InnerBufferLocalizedData.remainder_envelope_nonneg
    {B : BufferData} {C K : ℝ} (M : InnerBufferLocalizedData B C K) (i : Fin 2) :
    0 ≤ innerBufferRemainderEnvelope B C K i :=
  (norm_nonneg _).trans (M.remainder_norm_bound i)

theorem InnerBufferLocalizedData.scalar_weight_bound
    {B : BufferData} {C K : ℝ} (M : InnerBufferLocalizedData B C K) (i : Fin 2)
    {w : ℝ} (hw : 0 < w) (hcentral : B.bordered = true → w = 1) :
    |(M.column i).scalar| ≤ w * innerBufferRemainderEnvelope B C K i := by
  cases hb : B.bordered with
  | false =>
    have hs : (M.column i).scalar = 0 := by
      simpa only [hb, Bool.false_eq_true, ite_false] using (M.column i).scalar_row
    rw [hs, abs_zero]
    exact mul_nonneg hw.le (M.remainder_envelope_nonneg i)
  | true =>
    rw [hcentral hb, one_mul]
    exact M.scalar_bound i

theorem innerBorderL2_norm_le_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ 2 μ) (c : ℝ) :
    ‖(WithLp.toLp 2 (f, c) : InnerBorderL2 μ)‖ ≤ ‖f‖ + |c| := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg f) (abs_nonneg c))).mp
  rw [innerBorderL2_norm_sq]
  nlinarith only [sq_abs c, mul_nonneg (norm_nonneg f) (abs_nonneg c)]

section PhysicalModel

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {height : ℝ}
  (hh : 0 < height) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = height * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)

/-- The actual physical Poisson column, with its genuine unit radial
boundary value and the same temporary scalar as its model column. -/
def innerModelPhysicalPoissonColumn (i : Fin 2) :
    InnerBorderL2 (radialHilbertMeasure D) :=
  WithLp.toLp 2 (innerLiouvilleUnitPoissonPair D hB.1.le hh hR hs hp hcore hw U hU hv
    (bufferCut B i) (M.column i).field (M.column i).scalar)

theorem innerModelPhysicalPoissonColumn_weighted_bound
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (i : Fin 2) {ratio w Ucap : ℝ}
    (hratio : 0 ≤ ratio) (hwpos : 0 < w) (hcap : 0 ≤ Ucap)
    (hcentral : B.bordered = true → w = 1)
    (hconstant : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i), W (R x) = w)
    (hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      |deriv R x / R x| ≤ Ucap)
    (hcell : ∀ x ∈ Ioo B.l B.h, |W (R x)| ≤ ratio * w) :
    ‖innerBorderFieldMap (radialHilbertMeasure D)
      (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
      (innerModelPhysicalPoissonColumn D hB M hh hR hs hp hcore hw U hU hv i)‖ ≤
      (sqrt height * s (bufferCut B i)) * w *
        (sqrt 12 * Ucap * (sqrt (M.column i).inwardEnergy / B.mass i) +
          (sqrt 12 * U * ratio + 1) * innerBufferRemainderEnvelope B C K i) := by
  let A := innerLiouvilleFieldLift D hB.1.le hh hR hs hp hcore hw U hU hv
  let MW := innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC
  have hlead := innerLiouvilleFieldLift_weighted_buffer_bound
    D hB.1.le hh hR hs hp hcore hw U hU hv W hW CW hWC (M.column i).leading
    (uIcc (bufferCut B i) (bufferInnerWall B i))
    (innerBufferLeading_point_support hB i (M.column i).pin (M.column i).leading
      (M.column i).leading_ae).2 w hconstant hcap hbuffer
  rw [abs_of_pos hwpos] at hlead
  have hlead' : ‖MW (A (M.column i).leading)‖ ≤
      w * (sqrt 12 * Ucap * (sqrt (M.column i).inwardEnergy / B.mass i)) :=
    hlead.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (M.column i).leading_bound
        (mul_nonneg (sqrt_nonneg 12) hcap)) hwpos.le)
  have hrem := innerLiouvilleFieldLift_weighted_cell_bound
    D hB.1.le hh hR hs hp hcore hw U hU hv W hW CW hWC
    (M.remainder i).1 (M.remainder_supported i) hcell
  have hremfield : ‖(M.remainder i).1‖ ≤ innerBufferRemainderEnvelope B C K i := by
    apply le_trans _ (M.remainder_norm_bound i)
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hrem' : ‖MW (A (M.remainder i).1)‖ ≤
      (sqrt 12 * U) * (ratio * w) * innerBufferRemainderEnvelope B C K i :=
    hrem.trans (mul_le_mul_of_nonneg_left hremfield
      (mul_nonneg (mul_nonneg (sqrt_nonneg 12) hU) (mul_nonneg hratio hwpos.le)))
  have hfield : ‖MW (A (M.column i).field)‖ ≤
      w * (sqrt 12 * Ucap * (sqrt (M.column i).inwardEnergy / B.mass i)) +
        (sqrt 12 * U) * (ratio * w) * innerBufferRemainderEnvelope B C K i := by
    rw [(M.column_decomposition i).1, map_sub, map_sub]
    exact (norm_sub_le _ _).trans (add_le_add hlead' hrem')
  have hpair : ‖(WithLp.toLp 2 (MW (A (M.column i).field), (M.column i).scalar) :
      InnerBorderL2 (radialHilbertMeasure D))‖ ≤
      w * (sqrt 12 * Ucap * (sqrt (M.column i).inwardEnergy / B.mass i) +
        (sqrt 12 * U * ratio + 1) * innerBufferRemainderEnvelope B C K i) := by
    apply (innerBorderL2_norm_le_sum _ _ _).trans
    calc
      _ ≤ _ := add_le_add hfield (M.scalar_weight_bound i hwpos hcentral)
      _ = _ := by ring
  have hcut : bufferCut B i ∈ Icc B.l B.h := by
    unfold bufferCut
    split_ifs
    · exact left_mem_Icc.mpr hB.1.le
    · exact right_mem_Icc.mpr hB.1.le
  have hscale : 0 < sqrt height * s (bufferCut B i) :=
    mul_pos (sqrt_pos.mpr hh) (hp _ hcut).2.2
  have heq : innerBorderFieldMap (radialHilbertMeasure D) MW
      (innerModelPhysicalPoissonColumn D hB M hh hR hs hp hcore hw U hU hv i) =
      (sqrt height * s (bufferCut B i)) •
        (WithLp.toLp 2 (MW (A (M.column i).field), (M.column i).scalar) :
          InnerBorderL2 (radialHilbertMeasure D)) := by
    simp only [innerModelPhysicalPoissonColumn, innerLiouvilleUnitPoissonPair_apply,
      innerBorderFieldMap_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_smul]
    rfl
  change ‖innerBorderFieldMap (radialHilbertMeasure D) MW
    (innerModelPhysicalPoissonColumn D hB M hh hR hs hp hcore hw U hU hv i)‖ ≤ _
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]
  exact (mul_le_mul_of_nonneg_left hpair hscale.le).trans_eq (by ring)

end PhysicalModel

end ContinuousFlexibility.Radial
