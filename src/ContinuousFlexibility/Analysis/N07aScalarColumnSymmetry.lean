module

public import ContinuousFlexibility.Analysis.N07aCoefficientSymmetry
public import ContinuousFlexibility.Scalar.Normalization

/-!
# Reflection of the actual scalar columns

Signed coordinate derivatives preserve the genuine reflection identities,
including at points where the derivatives are totalized.  Thus the ν
derivative and the corrected cutoff divergence are even functions before
they are sent through the actual canonical coordinate map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

private theorem n07a_even_height_jets {f : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) :
    (∀ r θ, heightRadial f (r, -θ) = heightRadial f (r, θ)) ∧
    (∀ r θ, heightAngular f (r, -θ) = -heightAngular f (r, θ)) ∧
    (∀ r θ, radialPartial (heightRadial f) (r, -θ) =
      radialPartial (heightRadial f) (r, θ)) ∧
    (∀ r θ, radialPartial (heightAngular f) (r, -θ) =
      -radialPartial (heightAngular f) (r, θ)) ∧
    (∀ r θ, angularPartial (heightAngular f) (r, -θ) =
      angularPartial (heightAngular f) (r, θ)) := by
  have h : ∀ r θ, f (r, -θ) = (1 : ℝ) * f (r, θ) := by simpa only [one_mul]
  have hk : ∀ r θ, heightRadial f (r, -θ) = heightRadial f (r, θ) := by
    intro r θ
    simpa only [one_mul, heightRadial] using (n07a_coordinatePartials_reflection h r θ).1
  have hp : ∀ r θ, heightAngular f (r, -θ) = -heightAngular f (r, θ) := by
    intro r θ
    simp only [heightAngular, (n07a_coordinatePartials_reflection h r θ).2,
      neg_one_mul, neg_div]
  refine ⟨hk, hp, ?_, ?_, ?_⟩
  · intro r θ
    simpa only [one_mul] using (n07a_coordinatePartials_reflection
      (σ := 1) (by simpa only [one_mul] using hk) r θ).1
  · intro r θ
    simpa only [neg_one_mul] using (n07a_coordinatePartials_reflection
      (σ := -1) (by simpa only [neg_one_mul] using hp) r θ).1
  · intro r θ
    simpa only [neg_neg, one_mul, neg_one_mul] using (n07a_coordinatePartials_reflection
      (σ := -1) (by simpa only [neg_one_mul] using hp) r θ).2

theorem n07a_polarCoordinateResidual_even (w : ℝ → ℝ) {f : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (r θ : ℝ) :
    polarCoordinateResidual w f (r, -θ) = polarCoordinateResidual w f (r, θ) := by
  obtain ⟨hk, hp, hkr, hpr, hpt⟩ := n07a_even_height_jets hf
  have hEr : radialPartial (profileEnergy w) (r, -θ) =
      radialPartial (profileEnergy w) (r, θ) := by
    simpa only [one_mul] using (n07a_coordinatePartials_reflection (σ := 1)
      (fun r θ => by simp only [profileEnergy, one_mul]) r θ).1
  simp only [polarCoordinateResidual, polarCurvatureNumerator, polarDiscriminant,
    profileEnergy, hk, hp, hkr, hpr, hpt, hEr, heightDiscriminant,
    darbouxNumerator, neg_sq]

theorem n07a_polarResidualVariation_even (w : ℝ → ℝ) {f g : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ))
    (hg : ∀ r θ, g (r, -θ) = g (r, θ)) (r θ : ℝ) :
    polarResidualVariation w f g (r, -θ) = polarResidualVariation w f g (r, θ) := by
  obtain ⟨hk, hp, hkr, hpr, hpt⟩ := n07a_even_height_jets hf
  obtain ⟨gk, gp, gkr, gpr, gpt⟩ := n07a_even_height_jets hg
  have hEr : radialPartial (profileEnergy w) (r, -θ) =
      radialPartial (profileEnergy w) (r, θ) := by
    simpa only [one_mul] using (n07a_coordinatePartials_reflection (σ := 1)
      (fun r θ => by simp only [profileEnergy, one_mul]) r θ).1
  simp only [polarResidualVariation, polarCurvatureNumeratorVariation,
    polarDiscriminantVariation, polarCurvatureNumerator, polarDiscriminant,
    profileEnergy, hk, hp, hkr, hpr, hpt, gk, gp, gkr, gpr, gpt, hEr,
    heightDiscriminant, darbouxNumerator, darbouxNumeratorVariation,
    neg_sq, mul_neg, neg_mul, neg_neg]

theorem n07a_normalizedHeightResidual_even (w : ℝ → ℝ) {f g : PolarPoint → ℝ}
    (hf : ∀ r θ, f (r, -θ) = f (r, θ))
    (hg : ∀ r θ, g (r, -θ) = g (r, θ)) (q r θ : ℝ) :
    normalizedHeightResidual w f g q (r, -θ) =
      normalizedHeightResidual w f g q (r, θ) := by
  by_cases hq : q = 0
  · subst q
    rw [normalizedHeightResidual_zero, normalizedHeightResidual_zero,
      n07a_polarResidualVariation_even w hf hg]
  · rw [normalizedHeightResidual_of_ne_zero w f g _ hq,
      normalizedHeightResidual_of_ne_zero w f g _ hq,
      n07a_polarCoordinateResidual_even w (fun r θ => by simp only [heightFamily, hf, hg])]

theorem n07a_scalarResidualField_even
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    scalarResidualField D S C z (r, -θ) = scalarResidualField D S C z (r, θ) := by
  apply n07a_normalizedHeightResidual_even
  · intro r θ
    rfl
  · intro r θ
    simp only [stateU, heightPairField,
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.1 r θ]

theorem n07a_nuColumnField_even
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    nuColumnField D S C z (r, -θ) = nuColumnField D S C z (r, θ) := by
  apply congrArg (fun f : ℝ → ℝ => deriv f z.1.2.1)
  funext ν
  exact n07a_scalarResidualField_even hS ((z.1.1, (ν, z.1.2.2)), z.2) r θ

theorem n07a_divergenceOperator_even (A : SymmetricCoefficients) {f : PolarPoint → ℝ}
    (ha : ∀ r θ, A.a (r, -θ) = A.a (r, θ))
    (hb : ∀ r θ, A.b (r, -θ) = -A.b (r, θ))
    (hc : ∀ r θ, A.c (r, -θ) = A.c (r, θ))
    (hf : ∀ r θ, f (r, -θ) = f (r, θ)) (r θ : ℝ) :
    divergenceOperator A f (r, -θ) = divergenceOperator A f (r, θ) := by
  have h : ∀ r θ, f (r, -θ) = (1 : ℝ) * f (r, θ) := by simpa only [one_mul]
  have hrad : ∀ r θ,
      (A.a (r, -θ) * radialPartial f (r, -θ) + A.b (r, -θ) * angularPartial f (r, -θ)) =
      (1 : ℝ) * (A.a (r, θ) * radialPartial f (r, θ) + A.b (r, θ) * angularPartial f (r, θ)) := by
    intro r θ
    simp only [ha, hb, (n07a_coordinatePartials_reflection h r θ).1,
      (n07a_coordinatePartials_reflection h r θ).2, one_mul, neg_one_mul, neg_mul_neg]
  have hang : ∀ r θ,
      (A.b (r, -θ) * radialPartial f (r, -θ) + A.c (r, -θ) * angularPartial f (r, -θ)) =
      (-1 : ℝ) * (A.b (r, θ) * radialPartial f (r, θ) + A.c (r, θ) * angularPartial f (r, θ)) := by
    intro r θ
    simp only [hb, hc, (n07a_coordinatePartials_reflection h r θ).1,
      (n07a_coordinatePartials_reflection h r θ).2, one_mul, neg_one_mul]
    ring
  simp only [divergenceOperator,
    (n07a_coordinatePartials_reflection
      (f := fun y => A.a y * radialPartial f y + A.b y * angularPartial f y)
      (σ := 1) hrad r θ).1,
    (n07a_coordinatePartials_reflection
      (f := fun y => A.b y * radialPartial f y + A.c y * angularPartial f y)
      (σ := -1) hang r θ).2, neg_neg, one_mul]

end ContinuousFlexibility.Analysis
