import ContinuousFlexibility.Radial.InnerBufferFullInverse
import ContinuousFlexibility.Radial.CentralAuxiliaryBorder
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A compact temporary border for the central Schrödinger model

The source is the exact Liouville pullback R'/s*g₀(R) of the compact
physical auxiliary column already constructed for R03. Its pairing
with the actual unnormalized Gaussian is one. The already proved
reduced Schrödinger inverse then gives the full bordered inverse for
arbitrary L² sources and arbitrary scalar rows. The graph remains the
frozen weak Schrödinger graph; the physical radial inverse is not used
as a substitute for this model inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

def innerCentralModelBorderFunction (x : ℝ) : ℝ :=
  sqrt 12 * centralRadiusLogDerivative x * centralAuxiliarySourceFunction x

/-- This is the fixed physical R03 source, pulled back with the exact
inverse-adjoint density. No new auxiliary column is chosen. -/
theorem innerCentralModelBorderFunction_apply (x : ℝ) :
    innerCentralModelBorderFunction x =
      deriv centralRadius x / centralDensityRoot x * centralAuxiliaryFunction (centralRadius x) := by
  rw [innerCentralModelBorderFunction, centralAuxiliarySourceFunction_apply]
  unfold centralRadiusLogDerivative
  field_simp [(centralRadius_pos x).ne', (centralDensityRoot_pos x).ne',
    (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne']
  <;> ring

/-- Under the inverse-adjoint Liouville lift this is exactly the
already fixed positive Riesz column of R03, with its prescribed height
scaling. The physical sign convention is then a scalar sign change. -/
theorem innerCentralModelBorderFunction_physical {scale : ℝ} (hscale : 0 < scale) (x : ℝ) :
    innerCentralModelBorderFunction x /
      (12 * sqrt scale * centralDensityRoot x * (deriv centralRadius x / centralRadius x) ^ 2) =
        centralAuxiliaryColumnFunction scale (centralRadius x) := by
  rw [innerCentralModelBorderFunction_apply, centralAuxiliaryColumnFunction,
    centralRadialVarpi, centralRadialProfile_pullback]
  let z : ℝ := sqrt scale
  have hz : 0 < z := sqrt_pos.mpr hscale
  have he : scale = z ^ 2 := (sq_sqrt hscale.le).symm
  rw [he, sqrt_sq hz.le]
  field_simp [hz.ne', (centralRadius_pos x).ne', (centralDensityRoot_pos x).ne',
    (deriv_centralRadius_pos x).ne']
  <;> ring

theorem contDiff_innerCentralModelBorderFunction :
    ContDiff ℝ ∞ innerCentralModelBorderFunction :=
  (contDiff_const.mul contDiff_centralRadiusLogDerivative).mul
    contDiff_centralAuxiliarySourceFunction

theorem innerCentralModelBorderFunction_hasCompactSupport :
    HasCompactSupport innerCentralModelBorderFunction :=
  centralAuxiliarySourceFunction_hasCompactSupport.mul_left

theorem exists_innerCentralModelBorderRadius :
    ∃ R : ℝ, 1 ≤ R ∧ tsupport innerCentralModelBorderFunction ⊆ Icc (-R) R := by
  obtain ⟨C, hC⟩ := innerCentralModelBorderFunction_hasCompactSupport.isBounded.exists_norm_le
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x hx
  have h : |x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
  exact abs_le.mp (h.trans (le_max_right _ _))

def innerCentralModelBorderRadius : ℝ := Classical.choose exists_innerCentralModelBorderRadius

theorem innerCentralModelBorderRadius_ge_one : 1 ≤ innerCentralModelBorderRadius :=
  (Classical.choose_spec exists_innerCentralModelBorderRadius).1

theorem innerCentralModelBorderFunction_tsupport :
    tsupport innerCentralModelBorderFunction ⊆
      Icc (-innerCentralModelBorderRadius) innerCentralModelBorderRadius :=
  (Classical.choose_spec exists_innerCentralModelBorderRadius).2

theorem innerCentralModelBorderFunction_memLp :
    MemLp innerCentralModelBorderFunction 2 volume :=
  contDiff_innerCentralModelBorderFunction.continuous.memLp_of_hasCompactSupport
    innerCentralModelBorderFunction_hasCompactSupport

def innerCentralModelBorder : HermiteL2 :=
  innerCentralModelBorderFunction_memLp.toLp innerCentralModelBorderFunction

theorem innerCentralModelBorder_ae :
    (innerCentralModelBorder : ℝ → ℝ) =ᵐ[volume] innerCentralModelBorderFunction :=
  innerCentralModelBorderFunction_memLp.coeFn_toLp

def innerCentralModelKernel : HermiteL2 :=
  oscillatorHermiteNorm 2 0 • centralRadialGroundVector

theorem innerCentralModelKernel_inner (F : HermiteL2) :
    ⟪innerCentralModelKernel, F⟫_ℝ = oscillatorHermiteNorm 2 0 * hermiteCoefficient 2 F 0 := by
  rw [innerCentralModelKernel, real_inner_smul_left, centralRadialGroundVector,
    inner_hermiteL2Vector_left]

theorem innerCentralModelBorder_ground_pairing :
    ⟪innerCentralModelBorder, innerCentralModelKernel⟫_ℝ = 1 := by
  calc
    ⟪innerCentralModelBorder, innerCentralModelKernel⟫_ℝ =
        ⟪centralAuxiliarySourceVector, centralAuxiliaryKernelVector⟫_ℝ := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [innerCentralModelBorder_ae,
        Lp.coeFn_smul (oscillatorHermiteNorm 2 0) centralRadialGroundVector,
        Lp.coeFn_smul centralAuxiliaryKernelScale centralRadialKernelVector,
        centralRadialKernelVector_hasWeight, centralAuxiliarySourceVector_ae]
        with x hg hk ha hw hs
      have hk' : innerCentralModelKernel x =
          oscillatorHermiteNorm 2 0 * centralRadialGroundVector x := by
        simpa only [innerCentralModelKernel, Pi.smul_apply, smul_eq_mul] using hk
      have ha' : centralAuxiliaryKernelVector x =
          centralAuxiliaryKernelScale * centralRadialKernelVector x := by
        simpa only [centralAuxiliaryKernelVector, Pi.smul_apply, smul_eq_mul] using ha
      have hw' : centralRadialKernelVector x =
          centralRadiusLogDerivative x * centralRadialGroundVector x := hw
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hg, hk', ha', hw', hs]
      dsimp only [innerCentralModelBorderFunction, centralAuxiliaryKernelScale]
      ring
    _ = 1 := centralAuxiliarySource_kernel_pairing

theorem innerCentralModelGround_border_pairing :
    ⟪innerCentralModelKernel, innerCentralModelBorder⟫_ℝ = 1 := by
  rw [real_inner_comm, innerCentralModelBorder_ground_pairing]

theorem innerCentralModelGround_graph :
    (innerCentralModelKernel, 0) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  have hground : (centralRadialGroundVector, 0) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
    simpa only [centralRadialGroundVector, centralSpectralLevel_two,
      Nat.cast_zero, mul_zero, zero_smul] using
      centralClosedGraph_eigenpair (by norm_num : (0 : ℝ) < 2) 0
  simpa only [innerCentralModelKernel, Prod.smul_mk, smul_zero] using
    (centralClosedGraph (by norm_num : (0 : ℝ) < 2)).smul_mem
      (oscillatorHermiteNorm 2 0) hground

theorem innerCentralModelKernel_of_graph {u : HermiteL2}
    (hu : (u, 0) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    ∃ a : ℝ, u = a • innerCentralModelKernel := by
  obtain ⟨a, ha⟩ := (centralClosedGraph_two_kernel_iff u).mp hu
  refine ⟨a / oscillatorHermiteNorm 2 0, ?_⟩
  rw [innerCentralModelKernel, smul_smul,
    div_mul_cancel₀ _ (oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne',
    centralRadialGroundVector]
  exact ha

def innerCentralModelCorrectedSource : HermiteL2 →L[ℝ] HermiteL2 :=
  ContinuousLinearMap.id ℝ HermiteL2 -
    (innerSL ℝ innerCentralModelKernel).smulRight innerCentralModelBorder

theorem innerCentralModelCorrectedSource_apply (F : HermiteL2) :
    innerCentralModelCorrectedSource F =
      F - ⟪innerCentralModelKernel, F⟫_ℝ • innerCentralModelBorder := by
  simp only [innerCentralModelCorrectedSource, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem innerCentralModelCorrectedSource_compatible (F : HermiteL2) :
    hermiteCoefficient 2 (innerCentralModelCorrectedSource F) 0 = 0 := by
  have h : ⟪innerCentralModelKernel, innerCentralModelCorrectedSource F⟫_ℝ = 0 := by
    rw [innerCentralModelCorrectedSource_apply, inner_sub_right,
      real_inner_smul_right, innerCentralModelGround_border_pairing, mul_one, sub_self]
  rw [innerCentralModelKernel_inner] at h
  exact (mul_eq_zero.mp h).resolve_left (oscillatorHermiteNorm_pos (by norm_num : (0 : ℝ) < 2) 0).ne'

def innerCentralModelOutput : (HermiteL2 × ℝ) →L[ℝ] HermiteL2 :=
  let A := centralReducedHilbertInverse ∘L innerCentralModelCorrectedSource ∘L
    ContinuousLinearMap.fst ℝ HermiteL2 ℝ
  A + (ContinuousLinearMap.snd ℝ HermiteL2 ℝ -
    (innerSL ℝ innerCentralModelBorder) ∘L A).smulRight innerCentralModelKernel

def innerCentralModelScalar : (HermiteL2 × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ innerCentralModelKernel) ∘L ContinuousLinearMap.fst ℝ HermiteL2 ℝ

def innerCentralModelInverse : (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ) :=
  innerCentralModelOutput.prod innerCentralModelScalar

theorem innerCentralModelOutput_apply (F : HermiteL2) (t : ℝ) :
    innerCentralModelOutput (F, t) =
      centralReducedHilbertInverse (innerCentralModelCorrectedSource F) +
        (t - ⟪innerCentralModelBorder,
          centralReducedHilbertInverse (innerCentralModelCorrectedSource F)⟫_ℝ) •
            innerCentralModelKernel := by
  simp only [innerCentralModelOutput, add_apply,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', innerSL_apply_apply]

theorem innerCentralModelInverse_apply (F : HermiteL2) (t : ℝ) :
    innerCentralModelInverse (F, t) =
      (innerCentralModelOutput (F, t), ⟪innerCentralModelKernel, F⟫_ℝ) := by
  simp only [innerCentralModelInverse, innerCentralModelScalar,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', innerSL_apply_apply]

theorem innerCentralModelInverse_equations (F : HermiteL2) (t : ℝ) :
    (innerCentralModelOutput (F, t),
      F - ⟪innerCentralModelKernel, F⟫_ℝ • innerCentralModelBorder) ∈
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
  have hk : ⟪innerCentralModelKernel, F - c • innerCentralModelBorder⟫_ℝ = 0 := by
    rw [innerCentralModelKernel_inner, hcompat, mul_zero]
  rw [inner_sub_right, real_inner_smul_right,
    innerCentralModelGround_border_pairing, mul_one] at hk
  have hc : c = ⟪innerCentralModelKernel, F⟫_ℝ := by linarith only [hk]
  have hs := innerCentralModelInverse_equations F t
  have hsame : (innerCentralModelOutput (F, t), F - c • innerCentralModelBorder) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
    rw [hc]
    exact hs.1
  have hd := (centralClosedGraph (by norm_num : (0 : ℝ) < 2)).sub_mem hu'.1 hsame
  have hz : (u - innerCentralModelOutput (F, t), 0) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
    simpa only [Prod.sub_def, sub_self] using hd
  obtain ⟨a, ha⟩ := innerCentralModelKernel_of_graph hz
  have hrow : ⟪innerCentralModelBorder, u - innerCentralModelOutput (F, t)⟫_ℝ = 0 := by
    rw [inner_sub_right, hu'.2, hs.2, sub_self]
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

theorem exists_innerCentralModelFullInverse (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
      ‖H‖ ≤ innerCentralModelInverseConstant ∧
      (∀ F, (decide (n = 1) = false → F.2 = 0) →
        BorderedFullGraph (centralPotential (2 * n))
          (if n = 1 then innerCentralModelBorder else 0) (decide (n = 1)) (H F) F) ∧
      (∀ U F, BorderedFullGraph (centralPotential (2 * n))
        (if n = 1 then innerCentralModelBorder else 0) (decide (n = 1)) U F → H F = U) := by
  by_cases hn1 : n = 1
  · subst n
    refine ⟨innerCentralModelInverse, innerCentralModelInverse_norm_le, ?_, ?_⟩
    · intro F _
      simpa only [eq_self_iff_true, decide_true, ite_true, Nat.cast_one, mul_one] using
        innerCentralModelInverse_solves F
    · intro U F hUF
      apply innerCentralModelInverse_unique U F
      simpa only [eq_self_iff_true, decide_true, ite_true, Nat.cast_one, mul_one] using hUF
  · obtain ⟨H, hH, hforward, hbackward⟩ := exists_innerCentralFullInverse n (by omega)
    refine ⟨H, hH.trans (le_max_left _ _), ?_, ?_⟩
    · simpa only [hn1, ite_false, decide_false] using hforward
    · simpa only [hn1, ite_false, decide_false] using hbackward

end ContinuousFlexibility.Radial
