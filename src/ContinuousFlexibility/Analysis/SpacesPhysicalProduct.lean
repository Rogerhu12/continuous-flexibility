module

public import ContinuousFlexibility.Analysis.SpacesHeightProductBounds
public import ContinuousFlexibility.Analysis.SpacesBilinearContinuity

/-!
# Smooth tame multiplication of physical heights

The map is the actual pointwise product, encoded into the prescribed weak
jet graph. Its one-high-factor estimate supplies the bilinear clause of
the assumed projective tame calculus.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

theorem spacesPhysicalDecoded_map_add (γ : ℝ) (u v : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalDecoded hT γ (u + v) = spacesPhysicalDecoded hT γ u + spacesPhysicalDecoded hT γ v :=
  (spacesPhysicalDecodeLinear hT γ).map_add u v

theorem spacesPhysicalDecoded_map_smul (γ c : ℝ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalDecoded hT γ (c • u) = c • spacesPhysicalDecoded hT γ u :=
  (spacesPhysicalDecodeLinear hT γ).map_smul c u

def spacesPhysicalMultiply (γ δ : ℝ) (u v : PhysicalJetProjectiveLimit hT) :
    PhysicalJetProjectiveLimit hT :=
  spacesPhysicalHeightEncode hT (spaces_heightMember_mul hT
    (spacesPhysicalDecoded_heightMember hT γ u) (spacesPhysicalDecoded_heightMember hT δ v))

theorem spacesPhysicalMultiply_decode (γ δ : ℝ) (u v : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalDecoded hT (γ + δ) (spacesPhysicalMultiply hT γ δ u v) =
      fun p => spacesPhysicalDecoded hT γ u p * spacesPhysicalDecoded hT δ v p :=
  spacesPhysicalDecoded_encode hT _

def spacesPhysicalMultiplyBilinear (γ δ : ℝ) : PhysicalJetProjectiveLimit hT →ₗ[ℝ]
    PhysicalJetProjectiveLimit hT →ₗ[ℝ] PhysicalJetProjectiveLimit hT :=
  LinearMap.mk₂ ℝ (spacesPhysicalMultiply hT γ δ)
    (by
      intro u v w
      apply spacesPhysicalDecoded_injective hT (γ + δ)
      funext p
      simp only [spacesPhysicalMultiply_decode, spacesPhysicalDecoded_map_add, Pi.add_apply]
      ring)
    (by
      intro c u v
      apply spacesPhysicalDecoded_injective hT (γ + δ)
      funext p
      simp only [spacesPhysicalMultiply_decode, spacesPhysicalDecoded_map_smul,
        Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro u v w
      apply spacesPhysicalDecoded_injective hT (γ + δ)
      funext p
      simp only [spacesPhysicalMultiply_decode, spacesPhysicalDecoded_map_add, Pi.add_apply]
      ring)
    (by
      intro c u v
      apply spacesPhysicalDecoded_injective hT (γ + δ)
      funext p
      simp only [spacesPhysicalMultiply_decode, spacesPhysicalDecoded_map_smul,
        Pi.smul_apply, smul_eq_mul]
      ring)

theorem spacesPhysicalMultiplyBilinear_apply (γ δ : ℝ) (u v : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalMultiplyBilinear hT γ δ u v = spacesPhysicalMultiply hT γ δ u v :=
  LinearMap.mk₂_apply ..

theorem spacesPhysicalMultiply_one_high (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ δ : ℝ) : ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : PhysicalJetProjectiveLimit hT,
        spacesPhysicalGrading hT s (spacesPhysicalMultiply hT γ δ u v) ≤ C *
          (spacesPhysicalGrading hT (s + loss) u * spacesPhysicalGrading hT base v +
            spacesPhysicalGrading hT base u * spacesPhysicalGrading hT (s + loss) v) := by
  obtain ⟨base, loss, hb⟩ := spaces_physical_product_one_high hT hI γ δ
  refine ⟨base, loss, fun s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb s
  refine ⟨C, hC, fun u v => ?_⟩
  rw [spacesPhysicalGrading_eq_physicalNorm hT (γ + δ), spacesPhysicalMultiply_decode]
  exact hb u v

private theorem spacesPhysicalMultiply_product_bound (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ δ : ℝ) : ∀ s : ℕ, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : PhysicalJetProjectiveLimit hT,
        spacesPhysicalGrading hT s (spacesPhysicalMultiplyBilinear hT γ δ u v) ≤
          C * spacesPhysicalGrading hT N u * spacesPhysicalGrading hT N v := by
  obtain ⟨base, loss, hb⟩ := spacesPhysicalMultiply_one_high hT hI γ δ
  intro s
  obtain ⟨C, hC, hb⟩ := hb s
  let N := max base (s + loss)
  have hmono (u : PhysicalJetProjectiveLimit hT) {i : ℕ} (hi : i ≤ N) :
      spacesPhysicalGrading hT i u ≤ spacesPhysicalGrading hT N u :=
    Analysis.gradedSeminorm_monotone _ _ hi u
  refine ⟨N, 2 * C, by positivity, fun u v => ?_⟩
  rw [spacesPhysicalMultiplyBilinear_apply]
  apply (hb u v).trans
  calc
    _ ≤ C * (spacesPhysicalGrading hT N u * spacesPhysicalGrading hT N v +
        spacesPhysicalGrading hT N u * spacesPhysicalGrading hT N v) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add
        (mul_le_mul (hmono u (le_max_right _ _)) (hmono v (le_max_left _ _))
          (apply_nonneg _ _) (apply_nonneg _ _))
        (mul_le_mul (hmono u (le_max_left _ _)) (hmono v (le_max_right _ _))
          (apply_nonneg _ _) (apply_nonneg _ _))
    _ = _ := by ring

theorem spacesPhysicalMultiply_continuous (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ δ : ℝ) :
    Continuous (fun z : PhysicalJetProjectiveLimit hT × PhysicalJetProjectiveLimit hT =>
      spacesPhysicalMultiply hT γ δ z.1 z.2) := by
  have h := Analysis.spaces_projective_bilinear_continuous
    (fun s => physicalJetClosedSubmodule hT s) (physicalJetBond hT)
    (spacesPhysicalMultiplyBilinear hT γ δ) (spacesPhysicalMultiply_product_bound hT hI γ δ)
  simpa only [spacesPhysicalMultiplyBilinear_apply] using h

def spacesPhysicalMultiplyCLM (hI : HasInterpolation (spacesPhysicalGrading hT)) (γ δ : ℝ) :
    PhysicalJetProjectiveLimit hT →L[ℝ] PhysicalJetProjectiveLimit hT →L[ℝ] PhysicalJetProjectiveLimit hT :=
  Analysis.spaces_projective_bilinear_clm
    (fun s => physicalJetClosedSubmodule hT s) (physicalJetBond hT)
    (spacesPhysicalMultiplyBilinear hT γ δ) (spacesPhysicalMultiply_continuous hT hI γ δ)

theorem spacesPhysicalMultiplyCLM_apply (hI : HasInterpolation (spacesPhysicalGrading hT))
    (γ δ : ℝ) (u v : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalMultiplyCLM hT hI γ δ u v = spacesPhysicalMultiply hT γ δ u v :=
  spacesPhysicalMultiplyBilinear_apply hT γ δ u v

theorem spacesPhysicalMultiply_smoothTame (hH01 : H01Statement)
    (hI : HasInterpolation (spacesPhysicalGrading hT)) (γ δ : ℝ) :
    SmoothTameOn (pairGrading (spacesPhysicalGrading hT) (spacesPhysicalGrading hT))
      (spacesPhysicalGrading hT) univ
      (fun z : PhysicalJetProjectiveLimit hT × PhysicalJetProjectiveLimit hT =>
        spacesPhysicalMultiply hT γ δ z.1 z.2) := by
  exact Analysis.spaces_projective_bilinear_smoothTame_of_eq
    (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT) hH01
    (spacesPhysicalMultiplyCLM hT hI γ δ) (spacesPhysicalMultiply hT γ δ)
    (spacesPhysicalMultiplyCLM_apply hT hI γ δ) (spacesPhysicalMultiply_one_high hT hI γ δ)

end ContinuousFlexibility.Statements
