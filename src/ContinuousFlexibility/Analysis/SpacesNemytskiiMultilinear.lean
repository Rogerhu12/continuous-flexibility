import ContinuousFlexibility.Analysis.SpacesNemytskiiKernels

/-!
# Multilinearity and coarse bounds for composition kernels

The encoded kernels are multilinear in their directions because their
actual decoded functions are products of linear evaluations. Their tame
bound also supplies the seminorm product bounds used for continuity.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

def spacesNemytskiiPhysicalMultilinear (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) :
    MultilinearMap ℝ (fun _ : Fin k => PhysicalJetProjectiveLimit hT) (PolarPoint → ℝ) :=
  MultilinearMap.pi (fun p =>
    iteratedDeriv k F (spacesPhysicalDecoded hT γ u p) •
      (MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap
        (fun _ => (LinearMap.proj p).comp (spacesPhysicalDecodeLinear hT γ)))

theorem spacesNemytskiiPhysicalMultilinear_apply (γ : ℝ) (F : ℝ → ℝ) (k : ℕ)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) (p : PolarPoint) :
    spacesNemytskiiPhysicalMultilinear hT γ F k u v p =
      iteratedDeriv k F (spacesPhysicalDecoded hT γ u p) * ∏ i, spacesPhysicalDecoded hT γ (v i) p := rfl

theorem spacesNemytskiiKernel_decodeLinear (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesPhysicalDecodeLinear hT γ (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v) =
      spacesNemytskiiPhysicalMultilinear hT γ F k u v := by
  funext p
  exact (congrFun (spacesNemytskiiKernel_decode hT hI hγ hF hF0 hFb k u v) p).trans
    (spacesNemytskiiPhysical_apply hT γ hF0 k u v p)

def spacesNemytskiiMultilinear (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    MultilinearMap ℝ (fun _ : Fin k => PhysicalJetProjectiveLimit hT) (PhysicalJetProjectiveLimit hT) where
  toFun := spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u
  map_update_add' := by
    intro _ v i x y
    apply spacesPhysicalDecoded_injective hT γ
    change spacesPhysicalDecodeLinear hT γ _ = spacesPhysicalDecodeLinear hT γ (_ + _)
    rw [map_add]
    simp only [spacesNemytskiiKernel_decodeLinear]
    exact (spacesNemytskiiPhysicalMultilinear hT γ F k u).map_update_add v i x y
  map_update_smul' := by
    intro _ v i a x
    apply spacesPhysicalDecoded_injective hT γ
    change spacesPhysicalDecodeLinear hT γ _ = spacesPhysicalDecodeLinear hT γ (a • _)
    rw [map_smul]
    simp only [spacesNemytskiiKernel_decodeLinear]
    exact (spacesNemytskiiPhysicalMultilinear hT γ F k u).map_update_smul v i a x

theorem spacesNemytskiiMultilinear_apply (hI : HasInterpolation (spacesPhysicalGrading hT))
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C)
    (k : ℕ) (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesNemytskiiMultilinear hT hI hγ hF hF0 hFb k u v =
      spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v := rfl

theorem spacesNemytskiiMajorant_le_coarse {base high N k : ℕ} (hb : base ≤ N) (hh : high ≤ N)
    (u : PhysicalJetProjectiveLimit hT) (v : Fin k → PhysicalJetProjectiveLimit hT) :
    spacesNemytskiiMajorant hT base high u v ≤
      ((k : ℝ) + 1) * (1 + spacesPhysicalGrading hT N u) * ∏ i, spacesPhysicalGrading hT N (v i) := by
  classical
  let P := ∏ i, spacesPhysicalGrading hT N (v i)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => apply_nonneg _ _)
  have hv : (∏ i, spacesPhysicalGrading hT base (v i)) ≤ P := by
    apply Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
    intro i _
    exact gradedSeminorm_monotone _ _ hb (v i)
  have hterm (i : Fin k) : spacesPhysicalGrading hT high (v i) *
      (∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (v j)) ≤ P := by
    calc
      _ ≤ spacesPhysicalGrading hT N (v i) *
          ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT N (v j) := by
        apply mul_le_mul (gradedSeminorm_monotone _ _ hh (v i)) _
          (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (apply_nonneg _ _)
        exact Finset.prod_le_prod₀ (fun j _ => apply_nonneg _ _)
          (fun j _ => gradedSeminorm_monotone _ _ hb (v j))
      _ = P := Finset.mul_prod_erase Finset.univ
        (fun j => spacesPhysicalGrading hT N (v j)) (Finset.mem_univ i)
  have hsum : (∑ i, spacesPhysicalGrading hT high (v i) *
      ∏ j ∈ Finset.univ.erase i, spacesPhysicalGrading hT base (v j)) ≤ (k : ℝ) * P := by
    calc
      _ ≤ ∑ _i : Fin k, P := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp
  unfold spacesNemytskiiMajorant
  calc
    _ ≤ (1 + spacesPhysicalGrading hT N u) * P + (k : ℝ) * P :=
      add_le_add (mul_le_mul (add_le_add le_rfl (gradedSeminorm_monotone _ _ hh u)) hv
        (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)) (by positivity)) hsum
    _ = (1 + spacesPhysicalGrading hT N u + (k : ℝ)) * P := by ring
    _ ≤ (((k : ℝ) + 1) * (1 + spacesPhysicalGrading hT N u)) * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have hp : 0 ≤ spacesPhysicalGrading hT N u := apply_nonneg _ _
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hp]
    _ = _ := rfl

theorem spaces_nemytskii_kernel_coarse (hI : HasInterpolation (spacesPhysicalGrading hT)) :
    ∃ base : ℕ, ∀ (γ : ℝ) (hγ : 0 < γ) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
      (hFb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv n F x| ≤ C),
      ∀ k s : ℕ, ∀ R : ℝ, 1 ≤ R → ∃ N : ℕ, base ≤ N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalJetProjectiveLimit hT), spacesPhysicalGrading hT base u ≤ R →
      ∀ v : Fin k → PhysicalJetProjectiveLimit hT,
        spacesPhysicalGrading hT s (spacesNemytskiiKernel hT hI hγ hF hF0 hFb k u v) ≤
          C * (1 + spacesPhysicalGrading hT N u) * ∏ i, spacesPhysicalGrading hT N (v i) := by
  obtain ⟨base, loss, hb⟩ := spaces_nemytskii_kernel_tame hT hI
  refine ⟨base, fun γ hγ F hF hF0 hFb k s R hR => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hb γ hγ F hF hF0 hFb k s R hR
  refine ⟨max base (s + loss), le_max_left _ _, C * ((k : ℝ) + 1), by positivity, fun u hu v => ?_⟩
  apply (hbound u hu v).trans
  calc
    C * spacesNemytskiiMajorant hT base (s + loss) u v ≤
        C * (((k : ℝ) + 1) * (1 + spacesPhysicalGrading hT (max base (s + loss)) u) *
          ∏ i, spacesPhysicalGrading hT (max base (s + loss)) (v i)) :=
      mul_le_mul_of_nonneg_left
        (spacesNemytskiiMajorant_le_coarse hT (le_max_left _ _) (le_max_right _ _) u v) hC
    _ = _ := by ring

end ContinuousFlexibility.Statements
