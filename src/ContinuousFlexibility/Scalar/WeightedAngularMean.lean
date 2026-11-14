module

public import ContinuousFlexibility.Scalar.WeightedAngularMeanL2
public import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# The normalized angular mean as an actual weighted projection

Each radial weighted jet is averaged by an L² contraction, and every
positive angular jet vanishes. Hence every physical norm contracts at
its original order. The lifted map is an idempotent continuous linear
projection with base zero and loss zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}

theorem weightedPhysicalJet_scalarAngularMeanField_memLp
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (scalarAngularMeanField f))
      2 materialCylinderMeasure := by
  cases b with
  | zero =>
    rw [weightedPhysicalJet_scalarAngularMeanField_zero hT hf.1]
    exact (scalarAngularMeanField_memLp_and_norm_le
      (contDiff_weightedPhysicalJet hT hf.1 a 0 c) (hf.2.2.2.2 a 0 c)).1
  | succ b =>
    rw [weightedPhysicalJet_scalarAngularMeanField_succ]
    exact MemLp.zero

theorem eLpNorm_weightedPhysicalJet_scalarAngularMeanField_le
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) (a b c : ℕ) :
    eLpNorm (weightedPhysicalJet T γ a b c (scalarAngularMeanField f))
      2 materialCylinderMeasure ≤
      eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure := by
  cases b with
  | zero =>
    rw [weightedPhysicalJet_scalarAngularMeanField_zero hT hf.1]
    have hb := scalarAngularMeanField_memLp_and_norm_le
      (contDiff_weightedPhysicalJet hT hf.1 a 0 c) (hf.2.2.2.2 a 0 c)
    exact (ENNReal.toReal_le_toReal hb.1.eLpNorm_ne_top
      (hf.2.2.2.2 a 0 c).eLpNorm_ne_top).mp hb.2
  | succ b =>
    rw [weightedPhysicalJet_scalarAngularMeanField_succ, eLpNorm_zero]
    exact zero_le

theorem heightMember_scalarAngularMeanField
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) :
    HeightMember D T γ (scalarAngularMeanField f) := by
  refine ⟨scalarAngularMeanField_contDiffOn hf.1, ?_, ?_,
    scalarAngularMeanField_eq_zero_outside hf.2.2.2.1, ?_⟩
  · intro r θ
    rfl
  · intro p
    simp only [scalarAngularMeanField, Prod.fst_add, add_zero]
  · exact weightedPhysicalJet_scalarAngularMeanField_memLp hT hf

theorem physicalNorm_scalarAngularMeanField_le
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) (s : ℕ) :
    physicalNorm T γ s (scalarAngularMeanField f) ≤ physicalNorm T γ s f := by
  classical
  unfold physicalNorm
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono
  · exact ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.pow_ne_top
      (hf.2.2.2.2 (j.val 0).val (j.val 1).val (j.val 2).val).eLpNorm_ne_top)
  · apply Finset.sum_le_sum
    intro j _
    exact pow_le_pow_left₀ zero_le
      (eLpNorm_weightedPhysicalJet_scalarAngularMeanField_le hT hf
        (j.val 0).val (j.val 1).val (j.val 2).val) 2

namespace SobolevModelData

variable {A : SobolevModelData}

def angularMeanFieldLinear (hA : IsSobolevModel D T γ A) :
    A.Space →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := fun u => scalarAngularMeanField (A.decode u)
  map_add' := by
    intro u v
    simp only [map_add]
    exact scalarAngularMeanField_add
      (heightMember_continuous_angularSlice (hA.2.2.2.1 u))
      (heightMember_continuous_angularSlice (hA.2.2.2.1 v))
  map_smul' := by
    intro c u
    have he : A.decode (c • u) = fun p => c * A.decode u p := by
      funext p
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [he, scalarAngularMeanField_const_mul]
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem angularMeanFieldLinear_apply (hA : IsSobolevModel D T γ A) (u : A.Space) :
    angularMeanFieldLinear hA u = scalarAngularMeanField (A.decode u) := rfl

private theorem angularMean_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    HeightMember D T γ (angularMeanFieldLinear hA u) :=
  heightMember_scalarAngularMeanField hT (hA.2.2.2.1 u)

private theorem angularMean_physicalBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ s (angularMeanFieldLinear hA u) ≤ C * A.grading (s + 0) u := by
  intro s _
  refine ⟨1, zero_le_one, fun u => ?_⟩
  simpa only [angularMeanFieldLinear_apply, Nat.add_zero, one_mul,
    sobolevGrading_eq_physicalNorm hA] using
    physicalNorm_scalarAngularMeanField_le hT (hA.2.2.2.1 u) s

def angularMeanCLM (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    A.Space →L[ℝ] A.Space :=
  liftCLM hA (angularMeanFieldLinear hA) (angularMean_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularMean_physicalBound hT hA)

theorem decode_angularMeanCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    A.decode (angularMeanCLM hT hA u) = scalarAngularMeanField (A.decode u) :=
  decode_liftCLM hA (angularMeanFieldLinear hA) (angularMean_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularMean_physicalBound hT hA) u

theorem angularMeanCLM_idempotent
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) :
    angularMeanCLM hT hA (angularMeanCLM hT hA u) = angularMeanCLM hT hA u := by
  apply hA.2.2.2.2.2.1
  simp only [decode_angularMeanCLM, scalarAngularMeanField_idempotent]

theorem grading_angularMeanCLM_le
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (u : A.Space) (s : ℕ) :
    A.grading s (angularMeanCLM hT hA u) ≤ A.grading s u := by
  simpa only [sobolevGrading_eq_physicalNorm hA, decode_angularMeanCLM] using
    physicalNorm_scalarAngularMeanField_le hT (hA.2.2.2.1 u) s

theorem angularMeanCLM_isTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) :
    IsTameLinear A.grading A.grading (angularMeanCLM hT hA).toLinearMap 0 0 :=
  liftLinear_isTame hA (angularMeanFieldLinear hA) (angularMean_heightMember hT hA)
    (angularMean_physicalBound hT hA)

theorem angularMeanCLM_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    {U : Set A.Space} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame A.grading A.grading U 0 0 (angularMeanCLM hT hA) :=
  liftCLM_fixedNeighborhoodSmoothTame hA (angularMeanFieldLinear hA)
    (angularMean_heightMember hT hA)
    (withSeminorms_graded (fun n => A.level n) A.bond) (angularMean_physicalBound hT hA) hU

end SobolevModelData

end ContinuousFlexibility.Statements
