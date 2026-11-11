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

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem spaces_continuous_fixed_first {E V F : Type*}
    [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace F]
    (f : E → V → F) (hf : Continuous (fun z : E × V => f z.1 z.2)) (x : E) :
    Continuous (f x) := by
  have hp : Continuous (fun v : V => (x, v)) := continuous_const.prodMk continuous_id
  exact hf.comp hp

/-- Bundle continuity before specializing the source to a concrete weak-jet
subspace, keeping the multilinear map opaque during elaboration. -/
def spacesContinuousMultilinearMapOfContinuous {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] {k : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin k => E) F) (hB : Continuous B) : E [×k]→L[ℝ] F where
  toMultilinearMap := B
  cont := hB

theorem spacesContinuousMultilinearMapOfContinuous_apply {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] {k : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin k => E) F) (hB : Continuous B) (v : Fin k → E) :
    spacesContinuousMultilinearMapOfContinuous B hB v = B v := rfl

/-- A fixed low-seminorm bound on the base gives the local estimates in
the smooth-tame definition without changing the directional tower. -/
theorem spaces_smoothTameOn_univ_of_bounded_base {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) {f : E → F}
    (J : Statements.SmoothDirections Set.univ f) (base loss : ℕ)
    (hb : ∀ k s : ℕ, ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v : Fin k → E,
        q s (J.D k x v) ≤ C *
          ((1 + p (s + loss) x) * ∏ i, p base (v i) +
            ∑ i, p (s + loss) (v i) * ∏ j ∈ Finset.univ.erase i, p base (v j))) :
    Statements.SmoothTameOn p q Set.univ f := by
  refine ⟨J, fun k x₀ _ => ⟨loss, base, 1, zero_lt_one, fun s _ => ?_⟩⟩
  have hR : 1 ≤ 1 + p base x₀ := by have h := apply_nonneg (p base) x₀; linarith
  obtain ⟨C, hC, hbound⟩ := hb k s (1 + p base x₀) hR
  refine ⟨C, hC, fun x _ hx v => hbound x ?_ v⟩
  calc
    p base x = p base ((x - x₀) + x₀) := by rw [sub_add_cancel]
    _ ≤ p base (x - x₀) + p base x₀ := map_add_le_add (p base) _ _
    _ ≤ 1 + p base x₀ := add_le_add hx.le le_rfl

end ContinuousFlexibility.Analysis

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

theorem spacesNemytskiiMultilinear_continuous (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    Continuous (spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k u) := by
  have he : (spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k u :
      (Fin k → PhysicalJetProjectiveLimit hT) → PhysicalJetProjectiveLimit hT) =
        spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u :=
    funext (fun v => spacesNemytskiiMultilinear_apply hT hI hγ hF hF0 hFb k u v)
  rw [he]
  exact spaces_continuous_fixed_first (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k)
    (spacesNemytskiiKernel_continuous hT hI hγ hF hF0 hFb k) u

def spacesNemytskiiContinuousMultilinear (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    (PhysicalJetProjectiveLimit hT) [×k]→L[ℝ] (PhysicalJetProjectiveLimit hT) :=
  spacesContinuousMultilinearMapOfContinuous
    (spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k u)
    (spacesNemytskiiMultilinear_continuous hT hI hγ hF hF0 hFb k u)

theorem spacesNemytskiiContinuousMultilinear_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesNemytskiiContinuousMultilinear hT hI hγ hF hF0 hFb k u v =
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v := rfl

def spacesNemytskiiSmoothDirections :
    SmoothDirections univ (fun u => spacesNemytskiiKernel hT hI hγ hF hF0 hFb 0 u Fin.elim0) where
  open_domain := isOpen_univ
  D := spacesNemytskiiContinuousMultilinear hT hI hγ hF hF0 hFb
  zero := fun _ _ => rfl
  continuous := by
    intro k
    simp only [spacesNemytskiiContinuousMultilinear_apply]
    exact (spacesNemytskiiKernel_continuous hT hI hγ hF hF0 hFb k).continuousOn
  derivative := by
    intro k u _ v w
    simp only [spacesNemytskiiContinuousMultilinear_apply]
    exact spacesNemytskiiKernel_hasProjectiveLineDerivAt hT hI hγ hF hF0 hFb k u w v

theorem spacesNemytskiiSmoothDirections_D_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT)
    (v : Fin k → PhysicalJetProjectiveLimit hT) :
    (spacesNemytskiiSmoothDirections hT hI hγ hF hF0 hFb).D k u v =
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v := rfl

theorem spaces_nemytskii_bounded_smoothTame :
    SmoothTameOn (spacesPhysicalGrading hT) (spacesPhysicalGrading hT) univ
      (fun u => spacesNemytskiiKernel hT hI hγ hF hF0 hFb 0 u Fin.elim0) := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_kernel_tame hT hI
  apply spaces_smoothTameOn_univ_of_bounded_base (spacesPhysicalGrading hT) (spacesPhysicalGrading hT)
    (spacesNemytskiiSmoothDirections hT hI hγ hF hF0 hFb) base loss
  intro k s R hR
  obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hF0 hFb k s R hR
  refine ⟨C, hC, fun u hu v => ?_⟩
  rw [spacesNemytskiiSmoothDirections_D_apply]
  exact hbound u hu v

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
