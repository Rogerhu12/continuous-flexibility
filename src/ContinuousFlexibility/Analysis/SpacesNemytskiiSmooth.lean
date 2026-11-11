import ContinuousFlexibility.Analysis.SpacesNemytskiiCurveDerivative
import ContinuousFlexibility.Analysis.SpacesNemytskiiMultilinear
import ContinuousFlexibility.Analysis.SpacesMultilinearContinuity
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Smooth tame scalar composition on the actual physical space

The kernels form a tower of genuine projective directional derivatives.
Their continuity and fixed-loss estimates give smooth tameness. Clipping
the scalar function then gives the exact composition requested on one
fixed low-seminorm neighborhood of zero for every positive height weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
  (hI : HasInterpolation (spacesPhysicalGrading hT))
  {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
  (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)

theorem spacesNemytskiiKernel_continuous (k : ℕ) :
    Continuous (fun z : PhysicalJetProjectiveLimit hT × (Fin k → PhysicalJetProjectiveLimit hT) =>
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k z.1 z.2) := by
  obtain ⟨base, hb⟩ := spaces_nemytskii_kernel_coarse hT hI
  apply spaces_projective_parameter_multilinear_continuous
    (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT) base
    (spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k)
    (spacesNemytskiiKernel hT hI hγ hF hF0 hFb (k + 1))
  · intro u v w
    exact spacesNemytskiiKernel_hasProjectiveLineDerivAt hT hI hγ hF hF0 hFb k u w v
  · exact hb γ hγ F hF hF0 hFb k
  · exact hb γ hγ F hF hF0 hFb (k + 1)

def spacesNemytskiiContinuousMultilinear (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    (PhysicalJetProjectiveLimit hT) [×k]→L[ℝ] (PhysicalJetProjectiveLimit hT) where
  toMultilinearMap := spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k u
  cont := (spacesNemytskiiKernel_continuous hT hI hγ hF hF0 hFb k).comp
    (continuous_const.prodMk continuous_id)

theorem spacesNemytskiiContinuousMultilinear_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesNemytskiiContinuousMultilinear hT hI hγ hF hF0 hFb k u v =
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v := rfl

def spacesNemytskiiSmoothDirections :
    SmoothDirections univ (fun u => spacesNemytskiiKernel hT hI hγ hF hF0 hFb 0 u Fin.elim0) where
  open_domain := isOpen_univ
  D := spacesNemytskiiContinuousMultilinear hT hI hγ hF hF0 hFb
  zero := fun _ _ => rfl
  continuous := fun k => (spacesNemytskiiKernel_continuous hT hI hγ hF hF0 hFb k).continuousOn
  derivative := fun k u _ v w =>
    spacesNemytskiiKernel_hasProjectiveLineDerivAt hT hI hγ hF hF0 hFb k u w v

theorem spacesNemytskiiSmoothDirections_D_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) :
    (spacesNemytskiiSmoothDirections hT hI hγ hF hF0 hFb).D k u v =
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v := rfl

theorem spaces_nemytskii_bounded_smoothTame :
    SmoothTameOn (spacesPhysicalGrading hT) (spacesPhysicalGrading hT) univ
      (fun u => spacesNemytskiiKernel hT hI hγ hF hF0 hFb 0 u Fin.elim0) := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_kernel_tame hT hI
  refine ⟨spacesNemytskiiSmoothDirections hT hI hγ hF hF0 hFb, fun k u₀ _ => ?_⟩
  refine ⟨loss, base, 1, zero_lt_one, fun s _ => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hF0 hFb k s
    (1 + spacesPhysicalGrading hT base u₀) (by have h := apply_nonneg (spacesPhysicalGrading hT base) u₀; linarith)
  refine ⟨C, hC, fun u _ hu v => ?_⟩
  have hub : spacesPhysicalGrading hT base u ≤ 1 + spacesPhysicalGrading hT base u₀ := by
    calc
      spacesPhysicalGrading hT base u = spacesPhysicalGrading hT base ((u - u₀) + u₀) := by rw [sub_add_cancel]
      _ ≤ spacesPhysicalGrading hT base (u - u₀) + spacesPhysicalGrading hT base u₀ := map_add_le_add _ _ _
      _ ≤ 1 + spacesPhysicalGrading hT base u₀ := add_le_add hu.le le_rfl
  exact hbound u hub v

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The full scalar composition clause, with its genuine smooth directional
tower on one fixed low-seminorm neighborhood. -/
theorem spaces_nemytskii_composition {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ : ℝ) (hγ : 0 < γ) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ comp : PhysicalJetProjectiveLimit hT → PhysicalJetProjectiveLimit hT,
        (∀ u, spacesPhysicalGrading hT base u < ε → ∀ p,
          spacesPhysicalDecoded hT γ (comp u) p = F (spacesPhysicalDecoded hT γ u p)) ∧
        SmoothTameOn (spacesPhysicalGrading hT) (spacesPhysicalGrading hT)
          {u | spacesPhysicalGrading hT base u < ε} comp := by
  let φ := spacesScalarClipped F
  have hφ : ContDiff ℝ ∞ φ := spacesScalarClipped_contDiff hF
  have hφ0 : φ 0 = 0 := spacesScalarClipped_zero hF0
  have hφb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n φ x| ≤ C :=
    spacesScalarClipped_derivative_bound hF
  obtain ⟨ε, hε, hagree⟩ := spacesScalarClipped_model_neighborhood hT hγ
    (isSobolevModel_canonicalSobolevModelData hT γ) F
  let comp := fun u => spacesNemytskiiKernel hT hI hγ hφ hφ0 hφb 0 u Fin.elim0
  refine ⟨2, ε, hε, comp, ?_, ?_⟩
  · intro u hu p
    have hdecode := congrFun (spacesNemytskiiKernel_decode hT hI hγ hφ hφ0 hφb 0 u Fin.elim0) p
    have he := spacesNemytskiiPhysical_apply hT γ hφ0 0 u Fin.elim0 p
    simp only [iteratedDeriv_zero, Fin.prod_univ_zero, mul_one] at he
    exact hdecode.trans (he.trans (hagree u hu p))
  · apply smoothTameOn_mono (spaces_nemytskii_bounded_smoothTame hT hI hγ hφ hφ0 hφb)
    · exact isOpen_lt (continuous_gradedSeminorm _ _ 2) continuous_const
    · exact subset_univ _

end ContinuousFlexibility.Statements
