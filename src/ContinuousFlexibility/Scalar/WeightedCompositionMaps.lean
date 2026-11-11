import ContinuousFlexibility.Scalar.WeightedUniformComposition
import ContinuousFlexibility.Scalar.WeightedCompositionMoser

/-!
# Actual scalar composition maps with uniform derivative towers

The value estimates and membership are now supplied by the physical cylinder
proofs. The original physical-spaces composition map supplies the genuine
derivatives. Restricting its domain once yields the fixed common ball required
by the weighted scalar interfaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Every genuine tower for the literal scalar composition has one common
base and loss on a domain bounded in that low seminorm. -/
theorem weightedComposition_uniformTowers
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ) :
    ∃ base loss : ℕ, ∀ {U : Set A.Space} {f : A.Space → A.Space},
      ∀ J : SmoothDirections U f, ∀ F : ℝ → ℝ,
        ContDiff ℝ ∞ F → F 0 = 0 →
        (∀ x ∈ U, ∀ p, A.decode (f x) p = F (A.decode x p)) →
        ∀ R : ℝ, 0 ≤ R → (∀ x ∈ U, A.grading base x ≤ R) →
          UniformScalarTowerEstimate A.grading A.grading U base loss f J := by
  obtain ⟨valueBase, valueLoss, _, hvalue⟩ :=
    weightedComposition_physicalNorm_bound hT hA hinterp hγ
  exact uniformSobolevComposition_of_valueBounds hT hA hinterp hγ.le valueBase valueLoss
    (fun _ hF hF0 u => weightedComposition_heightMember hT hA hinterp hγ hF hF0 u) hvalue

/-- A globally smooth scalar function vanishing at zero has an actual
composition map on one small height ball, with one base and loss for its
entire derivative tower. -/
theorem exists_fixedNeighborhood_weightedComposition
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ f : (S.height γ).Space → (S.height γ).Space,
        (∀ u, (S.height γ).grading base u < ε → ∀ p,
          (S.height γ).decode (f u) p = F ((S.height γ).decode u p)) ∧
        FixedNeighborhoodSmoothTame (S.height γ).grading (S.height γ).grading
          {u | (S.height γ).grading base u < ε} base loss f := by
  rcases hS with ⟨hHeight, hCircle, hCutoff, hHeightTame, hCircleTame, hMult, hTrace,
    hSource, hPsi, hPsiOne, hQ, hProjection, hInverse, hComposition, hParity⟩
  obtain ⟨bF, εF, hεF, f, hfDecode, hfTame⟩ := hComposition γ hγ F hF hF0
  obtain ⟨J, _⟩ := hfTame
  obtain ⟨b, loss, hUniform⟩ :=
    weightedComposition_uniformTowers hT (hHeight γ) (hHeightTame γ).2.2 hγ
  let base : ℕ := max bF b
  let ε : ℝ := min εF 1
  let U : Set (S.height γ).Space := {u | (S.height γ).grading base u < ε}
  have hp : Monotone (S.height γ).grading :=
    gradedSeminorm_monotone (fun n => (S.height γ).level n) (S.height γ).bond
  have hε : 0 < ε := lt_min hεF zero_lt_one
  have hU : IsOpen U := isOpen_lt
    (continuous_gradedSeminorm (fun n => (S.height γ).level n) (S.height γ).bond base)
    continuous_const
  have hsub : U ⊆ {u | (S.height γ).grading bF u < εF} := by
    intro u hu
    exact lt_of_le_of_lt (hp (le_max_left _ _) u)
      (lt_of_lt_of_le hu (min_le_left _ _))
  let J' : SmoothDirections U f := smoothDirectionsRestrict J hU hsub
  have hbound : ∀ u ∈ U, (S.height γ).grading b u ≤ 1 := by
    intro u hu
    exact (hp (le_max_right _ _) u).trans (hu.le.trans (min_le_right _ _))
  have hdecode : ∀ u ∈ U, ∀ p,
      (S.height γ).decode (f u) p = F ((S.height γ).decode u p) :=
    fun u hu p => hfDecode u (hsub hu) p
  have hJ := hUniform J' F hF hF0 hdecode 1 zero_le_one hbound
  refine ⟨base, loss, ε, hε, f, ?_, ?_⟩
  · exact hdecode
  · exact fixedNeighborhoodSmoothTame_of_uniform J'
      (hJ.weaken hp (le_max_right _ _) (le_refl loss))

end ContinuousFlexibility.Statements
