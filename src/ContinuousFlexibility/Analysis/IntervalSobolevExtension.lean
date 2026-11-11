import ContinuousFlexibility.Analysis.SeeleySobolevExtension
import ContinuousFlexibility.Analysis.IntervalSobolevCutoffNorm
import ContinuousFlexibility.Analysis.SobolevAffineExtension
import ContinuousFlexibility.Analysis.SobolevJetRestriction

/-!
# A fixed extension from an interval

A smooth partition splits the function into two pieces supported away from
the opposite endpoint. Each piece is extended by the same half-line Seeley
operator, in the corresponding affine orientation. Their sum retains the
original function on the whole closed interval. The construction is linear
and independent of the Sobolev order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal

variable {ι F : Type*} [Countable ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem interval_reflection_preimage (L : ℝ) :
    Icc (0 : ℝ) L = (fun x : ℝ => L + (-1) * x) ⁻¹' Icc 0 L := by
  ext x
  simp only [mem_preimage, mem_Icc, neg_one_mul]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

def intervalSobolevReflect (L : ℝ) (hL : 0 < L) :
    IntervalSobolevCore F L hL →ₗ[ℝ] IntervalSobolevCore F L hL :=
  smoothSobolevAffinePullback measurableSet_Icc measurableSet_Icc
    (uniqueDiffOn_Icc hL) (uniqueDiffOn_Icc hL) L (-1) (Or.inr rfl)
    (interval_reflection_preimage L)

def lineSobolevReflect (L : ℝ) : LineSobolevCore F →ₗ[ℝ] LineSobolevCore F :=
  smoothSobolevAffinePullback MeasurableSet.univ MeasurableSet.univ
    uniqueDiffOn_univ uniqueDiffOn_univ L (-1) (Or.inr rfl) (by simp)

@[simp] theorem intervalSobolevReflect_apply (L : ℝ) (hL : 0 < L)
    (f : IntervalSobolevCore F L hL) (x : ℝ) :
    intervalSobolevReflect L hL f x = f (L - x) := by
  simp only [intervalSobolevReflect, smoothSobolevAffinePullback_apply,
    neg_one_mul, sub_eq_add_neg]

@[simp] theorem lineSobolevReflect_apply (L : ℝ) (f : LineSobolevCore F) (x : ℝ) :
    lineSobolevReflect L f x = f (L - x) := by
  simp only [lineSobolevReflect, smoothSobolevAffinePullback_apply,
    neg_one_mul, sub_eq_add_neg]

theorem norm_intervalSobolevReflect_jet (L : ℝ) (hL : 0 < L)
    (k : ℕ) (f : IntervalSobolevCore F L hL) :
    ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k
        (intervalSobolevReflect L hL f)‖ =
      ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ :=
  norm_sobolevCoreJet_affine measurableSet_Icc measurableSet_Icc
    (uniqueDiffOn_Icc hL) (uniqueDiffOn_Icc hL) L (-1) (Or.inr rfl)
    (interval_reflection_preimage L) k f

theorem norm_lineSobolevReflect_jet (L : ℝ) (k : ℕ) (f : LineSobolevCore F) :
    ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (lineSobolevReflect L f)‖ =
      ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k f‖ :=
  norm_sobolevCoreJet_affine MeasurableSet.univ MeasurableSet.univ
    uniqueDiffOn_univ uniqueDiffOn_univ L (-1) (Or.inr rfl) (by simp) k f

def intervalLeftCutoffCore (L : ℝ) (hL : 0 < L) :
    IntervalSobolevCore F L hL →ₗ[ℝ] HalfLineSobolevCore F :=
  cutoffHalfLineCoreLinear hL (show 2 * L / 3 < L by linarith)
    (contDiff_intervalSobolevCutoff L hL)
    (fun y hy => intervalSobolevCutoff_zero L hL hy)
    (intervalSobolevCutoff_deriv_bounded L hL)

def intervalRightCutoffCore (L : ℝ) (hL : 0 < L) :
    IntervalSobolevCore F L hL →ₗ[ℝ] HalfLineSobolevCore F :=
  cutoffHalfLineCoreLinear hL (show 2 * L / 3 < L by linarith)
    (contDiff_intervalSobolevRightCutoff L hL)
    (fun y hy => intervalSobolevRightCutoff_zero L hL hy)
    (intervalSobolevRightCutoff_deriv_bounded L hL)

@[simp] theorem intervalLeftCutoffCore_apply (L : ℝ) (hL : 0 < L)
    (f : IntervalSobolevCore F L hL) (x : ℝ) :
    intervalLeftCutoffCore L hL f x = intervalSobolevCutoff L hL x • f x :=
  cutoffHalfLineCoreLinear_apply _ _ _ _ _ f x

@[simp] theorem intervalRightCutoffCore_apply (L : ℝ) (hL : 0 < L)
    (f : IntervalSobolevCore F L hL) (x : ℝ) :
    intervalRightCutoffCore L hL f x = intervalSobolevRightCutoff L hL x • f x :=
  cutoffHalfLineCoreLinear_apply _ _ _ _ _ f x

/-- A single interval extension, assembled from the same half-line
operator in the two orientations. -/
def intervalSeeleyCoreExtension (S : SeeleyData ι) (L : ℝ) (hL : 0 < L) :
    IntervalSobolevCore F L hL →ₗ[ℝ] LineSobolevCore F :=
  (seeleySobolevCoreExtension S).comp (intervalLeftCutoffCore L hL) +
    (lineSobolevReflect L).comp ((seeleySobolevCoreExtension S).comp
      ((intervalRightCutoffCore L hL).comp (intervalSobolevReflect L hL)))

theorem intervalSeeleyCoreExtension_rightInverse (S : SeeleyData ι)
    (L : ℝ) (hL : 0 < L) (f : IntervalSobolevCore F L hL) {x : ℝ}
    (hx : x ∈ Icc 0 L) : intervalSeeleyCoreExtension S L hL f x = f x := by
  have hright : 0 ≤ L - x := sub_nonneg.mpr hx.2
  simp only [intervalSeeleyCoreExtension, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.coe_add, Pi.add_apply, lineSobolevReflect_apply]
  rw [seeleySobolevCoreExtension_rightInverse S _ hx.1,
    seeleySobolevCoreExtension_rightInverse S _ hright,
    intervalLeftCutoffCore_apply, intervalRightCutoffCore_apply,
    intervalSobolevReflect_apply, sub_sub_cancel, ← add_smul,
    intervalSobolevCutoff_partition, one_smul]

def intervalSeeleySobolevBound (S : SeeleyData ι) (L : ℝ) (hL : 0 < L) (k : ℕ) : ℝ :=
  seeleySobolevBound S k *
    (cutoffSobolevBound (intervalSobolevCutoff_deriv_bounded L hL) k +
      cutoffSobolevBound (intervalSobolevRightCutoff_deriv_bounded L hL) k)

theorem intervalSeeleySobolevBound_nonneg (S : SeeleyData ι) (L : ℝ)
    (hL : 0 < L) (k : ℕ) : 0 ≤ intervalSeeleySobolevBound S L hL k :=
  mul_nonneg (seeleySobolevBound_nonneg S k)
    (add_nonneg (cutoffSobolevBound_nonneg _ _) (cutoffSobolevBound_nonneg _ _))

theorem intervalSeeleyCoreExtension_bound (S : SeeleyData ι)
    (L : ℝ) (hL : 0 < L) (k : ℕ) (f : IntervalSobolevCore F L hL) :
    ‖sobolevCoreJet F univ MeasurableSet.univ uniqueDiffOn_univ k
        (intervalSeeleyCoreExtension S L hL f)‖ ≤
      intervalSeeleySobolevBound S L hL k *
        ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ := by
  have hleft :
      ‖sobolevCoreJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k
          (intervalLeftCutoffCore L hL f)‖ ≤
        cutoffSobolevBound (intervalSobolevCutoff_deriv_bounded L hL) k *
          ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ :=
    cutoffHalfLineCoreLinear_bound hL _ _ _ _ k f
  have hright :
      ‖sobolevCoreJet F (Ici 0) measurableSet_Ici (uniqueDiffOn_Ici 0) k
          (intervalRightCutoffCore L hL (intervalSobolevReflect L hL f))‖ ≤
        cutoffSobolevBound (intervalSobolevRightCutoff_deriv_bounded L hL) k *
          ‖sobolevCoreJet F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k f‖ := by
    exact (cutoffHalfLineCoreLinear_bound hL _ _ _ _ k (intervalSobolevReflect L hL f)).trans_eq
      (congrArg (fun r => cutoffSobolevBound
        (intervalSobolevRightCutoff_deriv_bounded L hL) k * r)
        (norm_intervalSobolevReflect_jet L hL k f))
  simp only [intervalSeeleyCoreExtension, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  refine (norm_add_le _ _).trans ?_
  rw [norm_lineSobolevReflect_jet]
  have h₁ := (seeleySobolevCoreExtension_bound S k (intervalLeftCutoffCore L hL f)).trans
    (mul_le_mul_of_nonneg_left hleft (seeleySobolevBound_nonneg S k))
  have h₂ := (seeleySobolevCoreExtension_bound S k
      (intervalRightCutoffCore L hL (intervalSobolevReflect L hL f))).trans
    (mul_le_mul_of_nonneg_left hright (seeleySobolevBound_nonneg S k))
  exact (add_le_add h₁ h₂).trans_eq (by simp only [intervalSeeleySobolevBound]; ring)

/-- Bounded interval extension on every actual completed Sobolev space. -/
def intervalSeeleySobolevExtension (S : SeeleyData ι) (L : ℝ) (hL : 0 < L) (k : ℕ) :
    SobolevJetCompletion F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k →L[ℝ]
      SobolevJetCompletion F univ MeasurableSet.univ uniqueDiffOn_univ k :=
  sobolevJetExtension F (intervalSeeleyCoreExtension S L hL) k

theorem norm_intervalSeeleySobolevExtension_le (S : SeeleyData ι)
    (L : ℝ) (hL : 0 < L) (k : ℕ) :
    ‖intervalSeeleySobolevExtension (F := F) S L hL k‖ ≤ intervalSeeleySobolevBound S L hL k :=
  norm_sobolevJetExtension_le F _ k (intervalSeeleySobolevBound_nonneg S L hL k)
    (intervalSeeleyCoreExtension_bound S L hL k)

theorem intervalSeeleySobolevExtension_rightInverse (S : SeeleyData ι)
    (L : ℝ) (hL : 0 < L) (k : ℕ) :
    (sobolevRestriction F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k).comp
        (intervalSeeleySobolevExtension S L hL k) =
      ContinuousLinearMap.id ℝ
        (SobolevJetCompletion F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) k) :=
  sobolevRestriction_comp_extension F _ _ _ _ k
    (intervalSeeleyCoreExtension_bound S L hL k)
    (fun f _ hx => intervalSeeleyCoreExtension_rightInverse S L hL f hx)

theorem intervalSeeleySobolevExtension_compatible (S : SeeleyData ι)
    (L : ℝ) (hL : 0 < L) {k m : ℕ} (hkm : k ≤ m) :
    (sobolevJetBonding F univ MeasurableSet.univ uniqueDiffOn_univ hkm).comp
        (intervalSeeleySobolevExtension S L hL m) =
      (intervalSeeleySobolevExtension S L hL k).comp
        (sobolevJetBonding F (Icc 0 L) measurableSet_Icc (uniqueDiffOn_Icc hL) hkm) :=
  sobolevJetExtension_compatible F (intervalSeeleyCoreExtension S L hL) hkm
    (intervalSeeleyCoreExtension_bound S L hL k) (intervalSeeleyCoreExtension_bound S L hL m)

end ContinuousFlexibility.Analysis
