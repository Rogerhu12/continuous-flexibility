import ContinuousFlexibility.Scalar.WeightedRadialMultiplier
import ContinuousFlexibility.Scalar.WeightedJetNormOperator
import ContinuousFlexibility.Scalar.WeightedCoefficientAlgebra

/-!
# Actual physical radial multiplication on the weighted spaces

A physical coefficient need only be smooth on the open annulus. Its
material-coordinate derivatives are controlled by the actual subpower
envelope. Multiplication preserves the original zero extension and has
loss one and base zero in every weighted height model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {k : ℝ → ℝ}

theorem materialPullback_radialMultiplier
    (T : MaterialData) (γ : ℝ) (k : ℝ → ℝ) (f : PolarPoint → ℝ) :
    materialPullback T γ (fun p => k p.1 * f p) =
      fun p => k (T.radius p.1) * materialPullback T γ f p := by
  funext p
  unfold materialPullback
  ring

theorem weightedPhysicalJet_radialMultiplier_bound
    (hT : IsMaterialData D T)
    (hk : MaterialSubpower T (fun x => k (T.radius x))) (a b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      MemLp (weightedPhysicalJet T γ a b c (fun p => k p.1 * f p))
        2 materialCylinderMeasure ∧
      (eLpNorm (weightedPhysicalJet T γ a b c (fun p => k p.1 * f p))
        2 materialCylinderMeasure).toReal ≤ C * physicalNorm T γ (a + b + c + 1) f := by
  have hbound : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv j (fun t => k (T.radius t)) x| ≤ C * T.M (T.radius x) ^ (1 : ℕ) := by
    intro j
    simpa only [pow_one] using hk.le_materialM j
  obtain ⟨C, hC, hCf⟩ :=
    weightedRadialMultiplier_jet_bound (γ := γ) hT hk.1 1 hbound a b c
  refine ⟨C, hC, fun f hf => ?_⟩
  have he : weightedPhysicalJet T γ a b c (fun p => k p.1 * f p) =
      fun p => T.M (T.radius p.1) ^ c *
        mixedDerivative a b (fun q => k (T.radius q.1) * materialPullback T γ f q) p := by
    unfold weightedPhysicalJet
    rw [materialPullback_radialMultiplier T γ k f]
  rw [he]
  exact hCf f hf

theorem heightMember_radialMultiplier
    (hT : IsMaterialData D T)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x)))
    {f : PolarPoint → ℝ} (hf : HeightMember D T γ f) :
    HeightMember D T γ (fun p => k p.1 * f p) := by
  have hkr : ContDiffOn ℝ ∞ (fun p : PolarPoint => k p.1) (annularOpen D) :=
    hks.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  refine ⟨hkr.mul hf.1, ?_, ?_, ?_, ?_⟩
  · intro r θ
    dsimp only
    rw [hf.2.1 r θ]
  · intro p
    simp only [Prod.fst_add, add_zero, hf.2.2.1 p]
  · intro p hp
    dsimp only
    rw [hf.2.2.2.1 p hp, mul_zero]
  · intro a b c
    obtain ⟨_, _, hb⟩ := weightedPhysicalJet_radialMultiplier_bound (γ := γ) hT hk a b c
    exact (hb f hf).1

theorem physicalNorm_radialMultiplier_bound
    (hT : IsMaterialData D T)
    (hk : MaterialSubpower T (fun x => k (T.radius x))) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ, HeightMember D T γ f →
      physicalNorm T γ s (fun p => k p.1 * f p) ≤ C * physicalNorm T γ (s + 1) f :=
  physicalNorm_bound_of_operator_jet_bounds
    (fun a b c => weightedPhysicalJet_radialMultiplier_bound (γ := γ) hT hk a b c) s

namespace SobolevModelData

variable {A : SobolevModelData}

def radialMultiplierFieldLinear (A : SobolevModelData) (k : ℝ → ℝ) :
    A.Space →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := fun u p => k p.1 * A.decode u p
  map_add' := by
    intro u v
    funext p
    simp only [map_add, Pi.add_apply, mul_add]
  map_smul' := by
    intro c u
    funext p
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem radialMultiplierFieldLinear_apply (A : SobolevModelData) (k : ℝ → ℝ) (u : A.Space) :
    radialMultiplierFieldLinear A k u = (fun p => k p.1 * A.decode u p) := rfl

private theorem radialMultiplier_heightMember
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x))) (u : A.Space) :
    HeightMember D T γ (radialMultiplierFieldLinear A k u) :=
  heightMember_radialMultiplier hT hks hk (hA.2.2.2.1 u)

private theorem radialMultiplier_physicalBound
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hk : MaterialSubpower T (fun x => k (T.radius x))) :
    ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ s (radialMultiplierFieldLinear A k u) ≤ C * A.grading (s + 1) u := by
  intro s _
  obtain ⟨C, hC, hCf⟩ := physicalNorm_radialMultiplier_bound (γ := γ) hT hk s
  refine ⟨C, hC, fun u => ?_⟩
  simpa only [radialMultiplierFieldLinear_apply, sobolevGrading_eq_physicalNorm hA] using
    hCf (A.decode u) (hA.2.2.2.1 u)

def radialMultiplierCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x))) : A.Space →L[ℝ] A.Space :=
  liftCLM hA (radialMultiplierFieldLinear A k) (radialMultiplier_heightMember hT hA hks hk)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radialMultiplier_physicalBound hT hA hk)

theorem decode_radialMultiplierCLM
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x))) (u : A.Space) :
    A.decode (radialMultiplierCLM hT hA hks hk u) = (fun p => k p.1 * A.decode u p) :=
  decode_liftCLM hA (radialMultiplierFieldLinear A k) (radialMultiplier_heightMember hT hA hks hk)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radialMultiplier_physicalBound hT hA hk) u

theorem radialMultiplierCLM_isTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x))) :
    IsTameLinear A.grading A.grading (radialMultiplierCLM hT hA hks hk).toLinearMap 1 0 :=
  liftLinear_isTame hA (radialMultiplierFieldLinear A k) (radialMultiplier_heightMember hT hA hks hk)
    (radialMultiplier_physicalBound hT hA hk)

theorem radialMultiplierCLM_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hks : ContDiffOn ℝ ∞ k (Ioo D.a D.b))
    (hk : MaterialSubpower T (fun x => k (T.radius x)))
    {U : Set A.Space} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame A.grading A.grading U 0 1 (radialMultiplierCLM hT hA hks hk) :=
  liftCLM_fixedNeighborhoodSmoothTame hA (radialMultiplierFieldLinear A k)
    (radialMultiplier_heightMember hT hA hks hk)
    (withSeminorms_graded (fun n => A.level n) A.bond) (radialMultiplier_physicalBound hT hA hk) hU

end SobolevModelData

end ContinuousFlexibility.Statements
