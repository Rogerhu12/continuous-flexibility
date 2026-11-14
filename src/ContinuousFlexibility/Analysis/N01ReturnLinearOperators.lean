module

public import ContinuousFlexibility.Analysis.N01UniformReturnMargins
public import ContinuousFlexibility.Analysis.CircleReturnWeightedInverse
public import ContinuousFlexibility.Analysis.CircleCompositionModel

/-!
# The actual N01 return operators in the supplied circle space

Optical normalization and the N01 variation bounds give one uniform
sample-weight bound for all small divisors.  The scalar Fourier inverse
therefore realizes an operator on the original physical circle model with
four levels of loss: three angular levels and one sample-weight level.
Both inverse identities retain the required even/zero-mean and odd sectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped NNReal

/-- Packaging takes place in one circle model before any physical-state
types are introduced. All maps are the already constructed actual
Fourier operators. -/
theorem circleReturnOperators_of_weighted_margin
    {T : MaterialData} {γ : ℝ} {S : CircleModelData}
    (hCircle : IsCircleModel T γ S) (travel c : ℕ → ℝ)
    (hc : ∀ m, 0 < c m)
    (hdiv : ∀ m j : ℕ, 1 ≤ j → c m / j ≤ |Real.sin (j * travel m)|)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ m, (c m)⁻¹ ≤ A * T.M (T.sample m))
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m)) :
    ∃ L : S.Space →L[ℝ] S.Space,
      ∃ J : S.Space →ₗ[ℝ] S.Space,
        (∀ v m θ, S.decode (L v) m θ =
          evenPart (fun t => S.decode v m (t + travel m)) θ) ∧
        (∀ g, (∀ m, Function.Even (S.decode g m) ∧ angularMean (S.decode g m) = 0) →
          L (J g) = g ∧ ∀ m θ, S.decode (J g) m (-θ) = -S.decode (J g) m θ) ∧
        (∀ v, (∀ m θ, S.decode v m (-θ) = -S.decode v m θ) → J (L v) = v) ∧
        IsTameLinear S.grading S.grading J 4 0 := by
  have hbound' : ∀ m, (c m)⁻¹ ≤ A * T.M (T.sample m) ^ (1 : ℕ) := by
    simpa only [pow_one] using hbound
  let L : S.Space →L[ℝ] S.Space := circleReturnContinuousLinear hCircle travel
  let J : S.Space →ₗ[ℝ] S.Space :=
    circleReturnInverseLinear hCircle travel c hc hdiv 1 hA hbound' hM hH
  have hL (v : S.Space) : L v = circleReturnLinear hCircle travel v :=
    IsTameLinear.toContinuousLinearMap_apply (circleReturnLinear_tame hCircle travel)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (withSeminorms_graded (fun i => S.level i) S.bond)
      (gradedSeminorm_monotone (fun i => S.level i) S.bond) v
  have hdecode : ∀ v m θ, S.decode (L v) m θ =
      evenPart (fun t => S.decode v m (t + travel m)) θ := by
    intro v m θ
    simpa only [evenPart, circleReturnShift, circleReturnEven] using
      circleReturnContinuousLinear_decode hCircle travel v m θ
  have hright : ∀ g, (∀ m, Function.Even (S.decode g m) ∧ angularMean (S.decode g m) = 0) →
      L (J g) = g ∧ ∀ m θ, S.decode (J g) m (-θ) = -S.decode (J g) m θ := by
    intro g hg
    have heq : L (J g) = g := by
      rw [hL]
      exact circleReturnInverseLinear_right_inverse hCircle travel c hc hdiv 1
        hA hbound' hM hH g (fun m => (hg m).1) (fun m => (hg m).2)
    exact And.intro heq (fun m θ => circleReturnInverseLinear_odd hCircle travel c hc hdiv 1
      hA hbound' hM hH g m θ)
  have hleft : ∀ v, (∀ m θ, S.decode v m (-θ) = -S.decode v m θ) → J (L v) = v := by
    intro v hv
    rw [hL]
    exact circleReturnInverseLinear_left_inverse hCircle travel c hc hdiv 1
      hA hbound' hM hH v hv
  have htame : IsTameLinear S.grading S.grading J 4 0 :=
    circleReturnInverseLinear_tame hCircle travel c hc hdiv 1 hA hbound' hM hH
  exact Exists.intro L (Exists.intro J (And.intro hdecode
    (And.intro hright (And.intro hleft htame))))

theorem N01Properties.returnLinearOperators
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ L : CircleSpace S →L[ℝ] CircleSpace S,
      ∃ J : CircleSpace S →ₗ[ℝ] CircleSpace S,
        (∀ v m θ, (S.circle (3 / 4 : ℝ)).decode (L v) m θ =
          circleRotationDifference S C v m θ) ∧
        (∀ g, IsEvenZeroMeanCircle S g → L (J g) = g ∧ IsOddCircle S (J g)) ∧
        (∀ v, IsOddCircle S v → J (L v) = v) ∧
        IsTameLinear (S.circle (3 / 4 : ℝ)).grading
          (S.circle (3 / 4 : ℝ)).grading J 4 0 := by
  have hCircle : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 _
  have hM : ∀ m, 0 ≤ T.M (T.sample m) :=
    fun m => ((material_circle_sample_weights_pos hT hN.1.1).1 m).le
  have hH : ∀ m, 0 ≤ T.H (T.sample m) :=
    fun m => ((material_circle_sample_weights_pos hT hN.1.1).2 m).le
  let hmarg := hN.uniform_returnMargin_family hS hT
  let A : ℝ := hmarg.choose
  have hA : 0 < A := hmarg.choose_spec.1
  let c : ℕ → ℝ := hmarg.choose_spec.2.choose
  have hc : ∀ m, 0 < c m := hmarg.choose_spec.2.choose_spec.1
  have hbound : ∀ m, (c m)⁻¹ ≤ A * T.M (T.sample m) :=
    hmarg.choose_spec.2.choose_spec.2.1
  have hdiv : ∀ m j : ℕ, 1 ≤ j → c m / j ≤ |Real.sin (j * C.travel m)| :=
    hmarg.choose_spec.2.choose_spec.2.2
  exact circleReturnOperators_of_weighted_margin
    (T := T) (γ := (3 / 4 : ℝ)) (S := S.circle (3 / 4 : ℝ))
    hCircle C.travel c hc hdiv hA.le hbound hM hH

end ContinuousFlexibility.Statements
