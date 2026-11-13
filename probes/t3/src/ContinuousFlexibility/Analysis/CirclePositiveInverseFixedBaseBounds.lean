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
  classical
  obtain ⟨b₀, ell, hinterp⟩ := hI
  let base : ℕ := max b₀ (ell + 2)
  let loss : ℕ := base + ell + 2
  have hq : Monotone M.grading := gradedSeminorm_monotone _ _
  obtain ⟨A, hA, hHA⟩ := material_circle_power_upper hT hD hγ
  have hw := material_circle_sample_weights_pos hT hD
  refine ⟨base, loss, ?_⟩
  refine linearFamily_fixedBase_value_of_norm_growth M.grading hq
    (fun s v => circleNorm T γ s (M.decode v))
    (fun s v B hB hb => (circleGrading_le_iff_circleNorm hM s v hB).mpr hb)
    (circlePositiveInverseComposeLinear hM hT hD hγ (fun _ => 0)) JP.continuousOn
    (fun e => ∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode e) 1 m) θ)
    ?_ base loss ?_
  · intro x hx
    exact (circlePositiveLiftDomain_iff hM (fun _ => 0) x).mpr
      (fun m θ => ha.trans_le (hx m θ))
  · intro R hR s
    let I := {z : M.Space × M.Space //
      (∀ m θ, a ≤ deriv (circleAffineLift (fun _ => 0) (M.decode z.1) 1 m) θ) ∧
        M.grading base z.1 ≤ R ∧ M.grading base z.2 ≤ 1}
    let e : I → M.Space := fun i => i.val.1
    let u : I → M.Space := fun i => i.val.2
    have hgrowth := circleNorm_inverseCompose_family_growth hM hw.1 hw.2 hA hHA
      base ell (le_max_right _ _)
      (fun b c hb hc => hinterp base b c (le_max_left _ _) hb hc)
      R (zero_le_one.trans hR) e u
      (fun i => i.property.2.1) (fun i => i.property.2.2.trans hR)
      (fun _ => 0) (fun i => circleAffineInverse (fun _ => 0) (e i)) ha
      (fun i => i.property.1)
      (fun i => circleAffineInverse_left (fun _ => 0) (e i) ha i.property.1)
      (fun i => circleAffineInverse_right hM hT hD hγ (fun _ => 0) (e i)) s
    obtain ⟨C, hC, hb⟩ := hgrowth
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
  sorry

end ContinuousFlexibility.Statements
