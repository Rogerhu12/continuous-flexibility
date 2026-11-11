import ContinuousFlexibility.Radial.InnerBufferFullInverse
import ContinuousFlexibility.Radial.CentralRadialClosedGraph
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A compact temporary border for the central Schrödinger model

The source is a normalized smooth bump divided by the actual positive
ground state. Its ground pairing is exactly one. The already proved
reduced Schrödinger inverse then gives the full bordered inverse for
arbitrary L² sources and arbitrary scalar rows. The graph remains the
frozen weak Schrödinger graph; the physical radial inverse is not used
as a substitute for this model inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

def innerCentralModelBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem innerCentralModelGround_pos (x : ℝ) :
    0 < normalizedOscillatorHermite 2 0 x := by
  rw [normalizedOscillatorHermite, oscillatorHermiteMode_eq,
    hermitePolynomial_zero, Polynomial.eval_one, one_mul]
  exact div_pos (exp_pos _) (oscillatorHermiteNorm_pos (by norm_num) 0)

def innerCentralModelBorderFunction (x : ℝ) : ℝ :=
  innerCentralModelBump.normed volume x / normalizedOscillatorHermite 2 0 x

theorem contDiff_innerCentralModelBorderFunction :
    ContDiff ℝ ∞ innerCentralModelBorderFunction :=
  innerCentralModelBump.contDiff_normed.div
    (contDiff_normalizedOscillatorHermite 2 0) (fun x => (innerCentralModelGround_pos x).ne')

theorem innerCentralModelBorderFunction_tsupport :
    tsupport innerCentralModelBorderFunction ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := by
  have hs : tsupport innerCentralModelBorderFunction ⊆
      tsupport (innerCentralModelBump.normed volume) := by
    apply closure_mono
    intro x hx
    change innerCentralModelBump.normed volume x ≠ 0
    intro hz
    exact hx (by rw [innerCentralModelBorderFunction, hz, zero_div])
  apply hs.trans
  rw [innerCentralModelBump.tsupport_normed_eq, Real.closedBall_eq_Icc]
  simpa only [innerCentralModelBump, zero_sub, zero_add, neg_div] using
    (Subset.rfl : Icc (-1 / 2 : ℝ) (1 / 2) ⊆ Icc (-1 / 2 : ℝ) (1 / 2))

theorem innerCentralModelBorderFunction_hasCompactSupport :
    HasCompactSupport innerCentralModelBorderFunction :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    innerCentralModelBorderFunction_tsupport

theorem innerCentralModelBorderFunction_memLp :
    MemLp innerCentralModelBorderFunction 2 volume :=
  contDiff_innerCentralModelBorderFunction.continuous.memLp_of_hasCompactSupport
    innerCentralModelBorderFunction_hasCompactSupport

def innerCentralModelBorder : HermiteL2 :=
  innerCentralModelBorderFunction_memLp.toLp innerCentralModelBorderFunction

theorem innerCentralModelBorder_ae :
    (innerCentralModelBorder : ℝ → ℝ) =ᵐ[volume] innerCentralModelBorderFunction :=
  innerCentralModelBorderFunction_memLp.coeFn_toLp

theorem innerCentralModelBorder_coefficient :
    hermiteCoefficient 2 innerCentralModelBorder 0 = 1 := by
  unfold hermiteCoefficient
  calc
    (∫ x : ℝ, innerCentralModelBorder x * normalizedOscillatorHermite 2 0 x) =
        ∫ x : ℝ, innerCentralModelBump.normed volume x := by
      apply integral_congr_ae
      filter_upwards [innerCentralModelBorder_ae] with x hx
      rw [hx, innerCentralModelBorderFunction,
        div_mul_cancel₀ _ (innerCentralModelGround_pos x).ne']
    _ = 1 := innerCentralModelBump.integral_normed

theorem innerCentralModelBorder_ground_pairing :
    ⟪innerCentralModelBorder, centralRadialGroundVector⟫_ℝ = 1 := by
  rw [centralRadialGroundVector, inner_hermiteL2Vector_right,
    innerCentralModelBorder_coefficient]

theorem innerCentralModelGround_border_pairing :
    ⟪centralRadialGroundVector, innerCentralModelBorder⟫_ℝ = 1 := by
  rw [real_inner_comm, innerCentralModelBorder_ground_pairing]

theorem innerCentralModelGround_graph :
    (centralRadialGroundVector, 0) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  simpa only [centralRadialGroundVector, centralSpectralLevel_two,
    Nat.cast_zero, mul_zero, zero_smul] using
    centralClosedGraph_eigenpair (by norm_num : (0 : ℝ) < 2) 0

def innerCentralModelCorrectedSource : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.id ℝ HermiteL2 -
    (innerSL ℝ centralRadialGroundVector).smulRight innerCentralModelBorder

theorem innerCentralModelCorrectedSource_apply (F : HermiteL2) :
    innerCentralModelCorrectedSource F =
      F - ⟪centralRadialGroundVector, F⟫_ℝ • innerCentralModelBorder := by
  simp only [innerCentralModelCorrectedSource, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem innerCentralModelCorrectedSource_compatible (F : HermiteL2) :
    hermiteCoefficient 2 (innerCentralModelCorrectedSource F) 0 = 0 := by
  rw [← inner_hermiteL2Vector_left (by norm_num : (0 : ℝ) < 2)]
  have h : hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 = centralRadialGroundVector := rfl
  rw [h, innerCentralModelCorrectedSource_apply, inner_sub_right,
    real_inner_smul_right, innerCentralModelGround_border_pairing, mul_one, sub_self]

def innerCentralModelOutput : (HermiteL2 × ℝ) →L[ℝ] HermiteL2 :=
  let A := centralReducedHilbertInverse ∘L innerCentralModelCorrectedSource ∘L
    ContinuousLinearMap.fst ℝ HermiteL2 ℝ
  A + (ContinuousLinearMap.snd ℝ HermiteL2 ℝ -
    (innerSL ℝ innerCentralModelBorder) ∘L A).smulRight centralRadialGroundVector

def innerCentralModelScalar : (HermiteL2 × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ centralRadialGroundVector) ∘L ContinuousLinearMap.fst ℝ HermiteL2 ℝ

def innerCentralModelInverse : (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ) :=
  innerCentralModelOutput.prod innerCentralModelScalar

theorem innerCentralModelOutput_apply (F : HermiteL2) (t : ℝ) :
    innerCentralModelOutput (F, t) =
      centralReducedHilbertInverse (innerCentralModelCorrectedSource F) +
        (t - ⟪innerCentralModelBorder,
          centralReducedHilbertInverse (innerCentralModelCorrectedSource F)⟫_ℝ) •
            centralRadialGroundVector := by
  simp only [innerCentralModelOutput, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', innerSL_apply_apply]

theorem innerCentralModelInverse_apply (F : HermiteL2) (t : ℝ) :
    innerCentralModelInverse (F, t) =
      (innerCentralModelOutput (F, t), ⟪centralRadialGroundVector, F⟫_ℝ) := by
  simp only [innerCentralModelInverse, innerCentralModelScalar,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', innerSL_apply_apply]

theorem innerCentralModelInverse_equations (F : HermiteL2) (t : ℝ) :
    (innerCentralModelOutput (F, t),
      F - ⟪centralRadialGroundVector, F⟫_ℝ • innerCentralModelBorder) ∈
        centralClosedGraph (by norm_num : (0 : ℝ) < 2) ∧
      ⟪innerCentralModelBorder, innerCentralModelOutput (F, t)⟫_ℝ = t := by
  have hb := centralReducedHilbertInverse_graph
    (innerCentralModelCorrectedSource F) (innerCentralModelCorrectedSource_compatible F)
  have hs := (centralClosedGraph (by norm_num : (0 : ℝ) < 2)).add_mem hb
    ((centralClosedGraph (by norm_num : (0 : ℝ) < 2)).smul_mem
      (t - ⟪innerCentralModelBorder,
        centralReducedHilbertInverse (innerCentralModelCorrectedSource F)⟫_ℝ)
      innerCentralModelGround_graph)
  constructor
  · simpa only [innerCentralModelOutput_apply, innerCentralModelCorrectedSource_apply,
      Prod.add_def, Prod.smul_mk, smul_zero, add_zero] using hs
  · rw [innerCentralModelOutput_apply, inner_add_right, real_inner_smul_right,
      innerCentralModelBorder_ground_pairing, mul_one]
    ring

/-- The sign is exactly the frozen block `(H,+g; row,0)`: the source
in the Schrödinger graph is F minus the output scalar times g. -/
theorem innerCentralModelInverse_solves (F : RadialL2 × ℝ) :
    BorderedFullGraph (centralPotential 2) innerCentralModelBorder true
      (innerCentralModelInverse F) F := by
  rcases F with ⟨F, t⟩
  rw [innerCentralModelInverse_apply]
  have h := innerCentralModelInverse_equations F t
  exact ⟨(centralWeakSchrodingerGraph_iff (by norm_num) _ _).mpr h.1, h.2⟩

/-- Uniqueness is in the same weak differential graph for arbitrary
L² forcing, not in a domain defined as the range of the inverse. -/
theorem innerCentralModelInverse_unique (U F : RadialL2 × ℝ)
    (hu : BorderedFullGraph (centralPotential 2) innerCentralModelBorder true U F) :
    innerCentralModelInverse F = U := by
  rcases U with ⟨u, c⟩
  rcases F with ⟨F, t⟩
  have hu' : (u, F - c • innerCentralModelBorder) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) ∧
        ⟪innerCentralModelBorder, u⟫_ℝ = t :=
    ⟨(centralWeakSchrodingerGraph_iff (by norm_num) _ _).mp hu.1, hu.2⟩
  have hcompat := centralClosedGraph_two_source_compatible _ _ hu'.1
  have hk : ⟪centralRadialGroundVector, F - c • innerCentralModelBorder⟫_ℝ = 0 := by
    simpa only [centralRadialGroundVector, inner_hermiteL2Vector_left] using hcompat
  rw [inner_sub_right, real_inner_smul_right,
    innerCentralModelGround_border_pairing, mul_one] at hk
  have hc : c = ⟪centralRadialGroundVector, F⟫_ℝ := by linarith only [hk]
  have hs := innerCentralModelInverse_equations F t
  have hsame : (innerCentralModelOutput (F, t), F - c • innerCentralModelBorder) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
    rw [hc]
    exact hs.1
  have hd := (centralClosedGraph (by norm_num : (0 : ℝ) < 2)).sub_mem hu'.1 hsame
  have hz : (u - innerCentralModelOutput (F, t), 0) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
    simpa only [Prod.sub_def, sub_self] using hd
  obtain ⟨a, ha⟩ := (centralClosedGraph_two_kernel_iff _).mp hz
  have hrow : ⟪innerCentralModelBorder, u - innerCentralModelOutput (F, t)⟫_ℝ = 0 := by
    rw [inner_sub_right, hu'.2, hs.2, sub_self]
  have hground : hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0 = centralRadialGroundVector := rfl
  rw [hground] at ha
  rw [ha, real_inner_smul_right, innerCentralModelBorder_ground_pairing, mul_one] at hrow
  rw [hrow, zero_smul] at ha
  rw [innerCentralModelInverse_apply]
  exact Prod.ext (sub_eq_zero.mp ha).symm hc.symm

/-- One finite constant controls the actual compact second-mode border
and every unbordered even central mode. It is independent of the cut. -/
def innerCentralModelInverseConstant : ℝ :=
  max (2 / centralGapDelta) (‖innerCentralModelInverse‖ + 1)

theorem innerCentralModelInverseConstant_pos : 0 < innerCentralModelInverseConstant :=
  (div_pos (by norm_num) centralGapDelta_pos).trans_le (le_max_left _ _)

theorem innerCentralModelInverse_norm_le :
    ‖innerCentralModelInverse‖ ≤ innerCentralModelInverseConstant :=
  (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_right _ _)

end ContinuousFlexibility.Radial
