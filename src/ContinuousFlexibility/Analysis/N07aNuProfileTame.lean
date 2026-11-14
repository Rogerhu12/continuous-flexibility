module

public import ContinuousFlexibility.Analysis.N07aProfileNu
public import ContinuousFlexibility.Scalar.WeightedCompositionGerm

/-!
# The genuine border-profile map as a uniform tame germ

The fixed compact border function belongs to every positive height
weight. Composing its scalar multiples with exp minus one is the existing
weighted composition map, identified with the literal profile by its
injective decoder.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n07aChiHeight
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (γ : ℝ) : (S.height γ).Space :=
  SobolevModelData.liftHeight (hS.1 γ) (fun p => D.chi p.1)
    (heightMember_radial_of_compact_support hT hb.1
      ⟨tsupport D.chi, hb.2.1, fun r hr => (hb.2.2.1 hr).1,
        fun r hr _ => notMem_tsupport_iff_eventuallyEq.mp hr |>.eq_of_nhds⟩)

theorem n07aChiHeight_decode
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (γ : ℝ) :
    (S.height γ).decode (n07aChiHeight hT hS hb γ) = fun p => D.chi p.1 :=
  SobolevModelData.decode_liftHeight (hS.1 γ) _ _

def n07aRealHeightCLM (γ : ℝ) (a : (S.height γ).Space) :
    ℝ →L[ℝ] (S.height γ).Space :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight a

theorem n07aRealHeightCLM_apply (γ : ℝ) (a : (S.height γ).Space) (ν : ℝ) :
    n07aRealHeightCLM γ a ν = ν • a := by
  simp only [n07aRealHeightCLM, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]

theorem n07aRealHeightCLM_isTame (γ : ℝ) (a : (S.height γ).Space) :
    IsTameLinear realGrading (S.height γ).grading
      (n07aRealHeightCLM γ a).toLinearMap 0 0 := by
  intro s _
  refine ⟨⟨(S.height γ).grading s a, apply_nonneg _ _⟩, ?_⟩
  intro ν
  change (S.height γ).grading s (n07aRealHeightCLM γ a ν) ≤
    (S.height γ).grading s a * ‖ν‖
  rw [n07aRealHeightCLM_apply, map_smul_eq_mul]
  exact le_of_eq (mul_comm _ _)

theorem n07aNuProfileHeight_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) (γ : ℝ) :
    n07aNuProfileHeight hT hS hb γ 0 = 0 := by
  apply (hS.1 γ).2.2.2.2.2.1
  rw [n07aNuProfileHeight_decode, map_zero]
  funext p
  simp only [n07aNuProfileMean, zero_mul, Real.exp_zero, sub_self, Pi.zero_apply]

theorem n07aNuProfileHeight_uniformTameGerm
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hb : RadialTrueBorder D) {γ : ℝ} (hγ : 0 < γ) :
    UniformTameGerm realGrading (S.height γ).grading 0
      (n07aNuProfileHeight hT hS hb γ) := by
  have hlin := uniformTameGerm_continuousLinear weighted_realGrading_withSeminorms (0 : ℝ)
    (n07aRealHeightCLM γ (n07aChiHeight hT hS hb γ))
    (n07aRealHeightCLM_isTame γ (n07aChiHeight hT hS hb γ))
  have hf : ContDiff ℝ ∞ (fun t : ℝ => Real.exp t - 1) := Real.contDiff_exp.sub contDiff_const
  have hf₀ : (fun t : ℝ => Real.exp t - 1) 0 = 0 := by simp
  have hcomp := hlin.weightedComposition
    (by exact map_zero (n07aRealHeightCLM γ (n07aChiHeight hT hS hb γ)))
    hT hS hγ hf hf₀ weighted_realGrading_monotone weighted_realGrading_withSeminorms
  apply hcomp.congr
  intro ν
  apply (hS.1 γ).2.2.2.2.2.1
  rw [SobolevModelData.decode_weightedCompositionMap, n07aNuProfileHeight_decode]
  funext p
  rw [n07aRealHeightCLM_apply, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, n07aChiHeight_decode, n07aNuProfileMean]

end ContinuousFlexibility.Analysis
