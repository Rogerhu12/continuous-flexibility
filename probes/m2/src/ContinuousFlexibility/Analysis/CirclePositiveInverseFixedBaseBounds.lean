import ContinuousFlexibility.Analysis.CircleShiftedForwardFixedBaseBounds
import ContinuousFlexibility.Analysis.TameInverseValueFixedBaseBounds
import ContinuousFlexibility.Analysis.TamePositiveLowerDomain
import ContinuousFlexibility.Analysis.TameTranslatedInverseFixedBaseBounds
import ContinuousFlexibility.Analysis.CircleInverseCompositionGrowth
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Fixed low-base bounds for the genuine positive circle inverse

Only the already given genuine forward and inverse towers are used. The
inverse value bound comes from actual inverse composition; its source is
normalized as a continuous linear map. The fixed-base inverse theorem is
applied once at zero travel, and translation transports the same estimate
to every given tower of the literal positive inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleFixedBaseInversePairSMul (M : CircleModelData) :
    SMul ℝ (M.Space × M.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

include hI in
/-- The true zero-travel inverse has a source-linear one-high value bound,
with base and loss fixed before the spatial order and the low-box radius. -/
theorem circlePositiveInverseComposeLinear_zero_fixedBase_value
    (JP : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
      (fun z : M.Space × M.Space =>
        circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ base loss : ℕ, ∀ R : ℝ, 1 ≤ R → ∀ s : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ e : M.Space,
        (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ) →
        M.grading base e ≤ R → ∀ y : M.Space,
          M.grading s (circlePositiveInverseComposeLinear hM hT hD hγ
            (fun _ => 0) e y) ≤ C *
              ((1 + M.grading (s + loss) e) * M.grading base y +
                M.grading (s + loss) y) := by
  sorry

include hM in
private theorem circleFixedBase_decode_deriv_smul
    (c : ℝ) (e : M.Space) (m : ℕ) (θ : ℝ) :
    deriv (M.decode (c • e) m) θ = c * deriv (M.decode e m) θ := by
  have he : HasDerivAt (M.decode e m) (deriv (M.decode e m) θ) θ :=
    (((hM.2.2.2.1 e).1 m).1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hf : M.decode (c • e) m = fun t => c * M.decode e m t := by
    funext t
    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun (congrFun (M.decode.map_smul c e) m) t
  exact (congrArg (fun f : ℝ → ℝ => deriv f θ) hf).trans (he.const_mul c).deriv

include hD hT hγ hM in
private theorem circleFixedBase_common_lower_domain (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set M.Space, IsOpen U ∧
      U ⊆ circlePositiveLiftDomain M ∧
      (∀ e : M.Space,
        (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ) → e ∈ U) ∧
      ∀ e ∈ U, ∀ m θ,
        c ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ := by
  have h := exists_open_lower_domain_of_smul
    (fun (e : M.Space) (m : ℕ) (θ : ℝ) => deriv (M.decode e m) θ)
    (circlePositiveLiftDomain M) (circlePositiveLiftDomain_isOpen hM hT hD hγ)
    (fun _ => Iff.rfl) (circleFixedBase_decode_deriv_smul hM) a ha
  simpa only [circleAffineLift_deriv hM] using h

include hI in
/-- The given true inverse towers for all travel satisfy one common low
base. Only the derivative loss depends on the parameter order. -/
theorem circlePositiveInverseComposeLinear_fixedBase_oneHigh
    (JF : SmoothDirections univ (fun z : M.Space × M.Space =>
      circleShiftedChartComposeContinuousLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (JP₀ : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
      (fun z : M.Space × M.Space =>
        circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0) z.1 z.2))
    (a : ℝ) (ha : 0 < a) :
    ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (travel : ℕ → ℝ)
        (JP : SmoothDirections (circlePositiveLiftDomain M ×ˢ univ)
          (fun z : M.Space × M.Space =>
            circlePositiveInverseComposeLinear hM hT hD hγ travel z.1 z.2)),
        ∀ x : M.Space × M.Space,
          (∀ m θ, a ≤ deriv (circleAffineLift travel (M.decode x.1) 1 m) θ) →
          pairGrading M.grading M.grading base x ≤ R → ∀ v : Fin n → M.Space × M.Space,
            M.grading s (JP.D n x v) ≤
              C * tameJetSize (pairGrading M.grading M.grading) n s loss base x v := by
  obtain ⟨c, hc, U, hU, hsub, hAU, hlow⟩ :=
    circleFixedBase_common_lower_domain hD hT hγ hM a ha
  have hq : Monotone M.grading := gradedSeminorm_monotone _ _
  refine translatedInverseFamily_fixedBase_oneHigh M.grading hq
    (coordinate_hasInterpolation_pair hq hq hI hI)
    (circleShiftedChartComposeContinuousLinear hM hT hD hγ)
    (circlePositiveInverseComposeLinear hM hT hD hγ)
    (fun _ => 0) (circlePositiveLiftDomain M) U hU hsub
    (fun travel e => ∀ m θ, a ≤ deriv (circleAffineLift travel (M.decode e) 1 m) θ)
    (fun travel e he => hAU e (by simpa only [circleAffineLift_deriv hM] using he))
    JF JP₀
    (fun travel => circleTranslationContinuousLinear hM hT hD hγ (fun m => -travel m))
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals sorry

end ContinuousFlexibility.Statements
