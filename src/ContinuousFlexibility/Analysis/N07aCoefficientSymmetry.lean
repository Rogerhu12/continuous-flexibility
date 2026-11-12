import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.GreenIdentity
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Angular symmetry of the actual original coefficients

Reflection is a continuous linear equivalence of polar coordinate space.
The totalized derivative therefore has the expected signed symmetry even
at points where it is not differentiable. The three original coefficients
inherit even, odd, even symmetry directly from their defining formulas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

private def n07aPolarReflection : PolarPoint ≃L[ℝ] PolarPoint :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

private theorem n07aPolarReflection_apply (p : PolarPoint) :
    n07aPolarReflection p = (p.1, -p.2) := by
  simp only [n07aPolarReflection, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.neg_apply]

/-- Signed reflection commutes with the radial partial and changes sign
under the angular partial. No differentiability premise is necessary. -/
theorem n07a_coordinatePartials_reflection {f : PolarPoint → ℝ} {σ : ℝ}
    (hf : ∀ r θ, f (r, -θ) = σ * f (r, θ)) (r θ : ℝ) :
    radialPartial f (r, -θ) = σ * radialPartial f (r, θ) ∧
      angularPartial f (r, -θ) = -σ * angularPartial f (r, θ) := by
  have he : f ∘ n07aPolarReflection = σ • f := by
    funext p
    simpa only [Function.comp_apply, n07aPolarReflection_apply, Pi.smul_apply,
      smul_eq_mul] using hf p.1 p.2
  have hd := n07aPolarReflection.comp_right_fderiv (f := f) (x := (r, θ))
  rw [he, congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) σ) (r, θ)] at hd
  have hr := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hd
  have ht := congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hd
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, n07aPolarReflection_apply, neg_zero] at hr
  have heθ : ((0, -(1 : ℝ)) : PolarPoint) = -(0, (1 : ℝ)) := by simp
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, n07aPolarReflection_apply, heθ, map_neg] at ht
  exact ⟨hr.symm, by dsimp only [angularPartial]; linarith only [ht]⟩

/-- The actual coefficient formulas preserve angular symmetry, including
their totalized quotients and square roots. -/
theorem n07a_heightCorrectedCoefficients_reflection
    (w : ℝ → ℝ) {z : PolarPoint → ℝ}
    (hz : ∀ r θ, z (r, -θ) = z (r, θ)) :
    (∀ r θ, polarLinearA w z (r, -θ) = polarLinearA w z (r, θ)) ∧
      (∀ r θ, polarLinearB w z (r, -θ) = -polarLinearB w z (r, θ)) ∧
      (∀ r θ, polarCorrectedC w z (r, -θ) = polarCorrectedC w z (r, θ)) := by
  have hz' : ∀ r θ, z (r, -θ) = (1 : ℝ) * z (r, θ) := by simpa only [one_mul]
  have hk : ∀ r θ, heightRadial z (r, -θ) = heightRadial z (r, θ) :=
    fun r θ => by simpa only [one_mul, heightRadial] using (n07a_coordinatePartials_reflection hz' r θ).1
  have hp : ∀ r θ, heightAngular z (r, -θ) = -heightAngular z (r, θ) := by
    intro r θ
    simp only [heightAngular,
      (n07a_coordinatePartials_reflection hz' r θ).2, neg_one_mul, neg_div]
  have hkr : ∀ r θ, radialPartial (heightRadial z) (r, -θ) =
      radialPartial (heightRadial z) (r, θ) := by
    intro r θ
    simpa only [one_mul] using
      (n07a_coordinatePartials_reflection (f := heightRadial z) (σ := 1)
        (by simpa only [one_mul] using hk) r θ).1
  have hpr : ∀ r θ, radialPartial (heightAngular z) (r, -θ) =
      -radialPartial (heightAngular z) (r, θ) := by
    intro r θ
    simpa only [neg_one_mul] using
      (n07a_coordinatePartials_reflection (σ := -1)
        (by simpa only [neg_one_mul] using hp) r θ).1
  have hpt : ∀ r θ, angularPartial (heightAngular z) (r, -θ) =
      angularPartial (heightAngular z) (r, θ) := by
    intro r θ
    simpa only [neg_neg, one_mul, neg_one_mul] using
      (n07a_coordinatePartials_reflection (σ := -1)
        (by simpa only [neg_one_mul] using hp) r θ).2
  have hEr : ∀ r θ, radialPartial (profileEnergy w) (r, -θ) =
      radialPartial (profileEnergy w) (r, θ) := by
    intro r θ
    simpa only [one_mul] using
      (n07a_coordinatePartials_reflection (σ := 1)
        (fun r θ => by simp only [profileEnergy, one_mul]) r θ).1
  have hscale : ∀ r θ, polarScale w z (r, -θ) = polarScale w z (r, θ) := by
    intro r θ
    simp only [polarScale, polarDiscriminant, heightDiscriminant,
      profileEnergy, hk, hp, neg_sq]
  refine ⟨?_, ?_, ?_⟩ <;> intro r θ
  · simp only [polarLinearA, profileEnergy, hk, hpt, hscale]
  · simp only [polarLinearB, profileEnergy, hpr, hscale, linearMixed]
    ring
  · simp only [polarCorrectedC, profileEnergy, hEr, hk, hp, hkr, hpr, hpt, hscale,
      correctedAngular, linearAngular, scaledCoordinateResidual, darbouxNumerator, neg_sq]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem n07a_stateHeight_even (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (r θ : ℝ) :
    stateHeight D S C z (r, -θ) = stateHeight D S C z (r, θ) := by
  simp only [stateHeight, stateU, heightPairField,
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.1 r θ]

theorem n07a_stateHeight_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) : Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  intro p
  simp only [stateHeight, stateU, heightPairField, Prod.fst_add, add_zero,
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.2.1 p]

theorem n07a_originalCoefficients_reflection (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    (∀ r θ, (originalCoefficients D S C z).a (r, -θ) =
      (originalCoefficients D S C z).a (r, θ)) ∧
    (∀ r θ, (originalCoefficients D S C z).b (r, -θ) =
      -(originalCoefficients D S C z).b (r, θ)) ∧
    (∀ r θ, (originalCoefficients D S C z).c (r, -θ) =
      (originalCoefficients D S C z).c (r, θ)) :=
  n07a_heightCorrectedCoefficients_reflection _ (n07a_stateHeight_even hS z)

theorem n07a_originalCoefficients_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (originalCoefficients D S C z).a (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).b (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).c (0, Real.pi) :=
  periodic_heightCorrectedCoefficients _ (n07a_stateHeight_periodic hS z)

end ContinuousFlexibility.Analysis
