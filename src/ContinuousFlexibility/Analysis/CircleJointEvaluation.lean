import ContinuousFlexibility.Analysis.CircleAngularJetLinear
import ContinuousFlexibility.Analysis.SmoothDirectionsJointAngular
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.SolveNewtonBridge

/-!
# Actual joint circle evaluation in the projective topology

The existing angular derivative maps are continuous in the supplied
circle model. A single circle seminorm bounds every point evaluation
of a fixed angular order. This proves joint continuity when the angle
and the circle element vary, and the genuine angular hierarchy then
gives the complete joint directional tower.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem continuous_joint_linear_of_uniform_seminorm_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (L : ℝ → E →ₗ[ℝ] ℝ) (p : Seminorm ℝ E) (hp : Continuous p)
    (K : ℝ) (hbound : ∀ θ u, |L θ u| ≤ K * p u)
    (hangle : ∀ u, Continuous (fun θ => L θ u)) :
    Continuous (fun z : ℝ × E => L z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto
      (fun q : ℝ × E => K * p (q.2 - z.2) + |L q.1 z.2 - L z.1 z.2|)
      (𝓝 z) (𝓝 0) := by
    have hc : Continuous
        (fun q : ℝ × E => K * p (q.2 - z.2) + |L q.1 z.2 - L z.1 z.2|) :=
      ((hp.comp (continuous_snd.sub continuous_const)).const_mul K).add
        (((hangle z.2).comp continuous_fst).sub continuous_const).abs
    simpa only [sub_self, map_zero, mul_zero, abs_zero, add_zero] using hc.tendsto z
  apply squeeze_zero (fun q => norm_nonneg _) _ hlim
  intro q
  rw [Real.norm_eq_abs]
  have heq : L q.1 q.2 - L z.1 z.2 =
      L q.1 (q.2 - z.2) + (L q.1 z.2 - L z.1 z.2) := by
    rw [map_sub]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hbound q.1 (q.2 - z.2)) le_rfl)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleDerivativeContinuousLinear_apply
    (hS : IsCircleModel T γ S) (u : S.Space) :
    circleDerivativeContinuousLinear hS u = circleDerivativeLinear hS u :=
  IsTameLinear.toContinuousLinearMap_apply (circleDerivativeLinear_isTame hS)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (withSeminorms_graded (fun i => S.level i) S.bond)
    (gradedSeminorm_monotone (fun i => S.level i) S.bond) u

theorem continuous_circleIteratedDerivativeLinear
    (hS : IsCircleModel T γ S) (b : ℕ) :
    Continuous (circleIteratedDerivativeLinear hS b) := by
  induction b with
  | zero => exact continuous_id
  | succ b ih =>
    have heq : (circleIteratedDerivativeLinear hS (b + 1) : S.Space → S.Space) =
        fun u => circleDerivativeContinuousLinear hS (circleIteratedDerivativeLinear hS b u) := by
      funext u
      change circleDerivativeLinear hS (circleIteratedDerivativeLinear hS b u) = _
      exact (circleDerivativeContinuousLinear_apply hS _).symm
    rw [heq]
    exact (circleDerivativeContinuousLinear hS).continuous.comp ih

def circleAngularJetEvaluationCLM (hS : IsCircleModel T γ S)
    (b m : ℕ) (θ : ℝ) : S.Space →L[ℝ] ℝ :=
  { circleAngularJetEvaluationLinear hS b m θ with
    cont := by
      have hc := (continuous_apply θ).comp ((continuous_apply m).comp
        (hS.2.2.1.comp (continuous_circleIteratedDerivativeLinear hS b)))
      exact hc }

theorem circleAngularJetEvaluationCLM_apply (hS : IsCircleModel T γ S)
    (b m : ℕ) (θ : ℝ) (u : S.Space) :
    circleAngularJetEvaluationCLM hS b m θ u = iteratedDeriv b (S.decode u m) θ :=
  circleAngularJetEvaluationLinear_apply hS b m θ u

theorem circleDecoded_iteratedDeriv_contDiff (hS : IsCircleModel T γ S)
    (u : S.Space) (m b : ℕ) : ContDiff ℝ ∞ (iteratedDeriv b (S.decode u m)) := by
  have h := ((hS.2.2.2.1 (circleIteratedDerivativeLinear hS b u)).1 m).1
  have heq : S.decode (circleIteratedDerivativeLinear hS b u) m =
      iteratedDeriv b (S.decode u m) :=
    congrFun (circleIteratedDerivativeLinear_decode hS b u) m
  exact heq ▸ h

theorem circleDecoded_iteratedDeriv_hasDerivAt (hS : IsCircleModel T γ S)
    (u : S.Space) (m b : ℕ) (θ : ℝ) :
    HasDerivAt (iteratedDeriv b (S.decode u m))
      (iteratedDeriv (b + 1) (S.decode u m) θ) θ := by
  have h := ((circleDecoded_iteratedDeriv_contDiff hS u m b).differentiable (by simp) θ).hasDerivAt
  simpa only [iteratedDeriv_succ] using h

theorem continuous_circleAngularJetEvaluation
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m)) (b m : ℕ) :
    Continuous (fun p : ℝ × S.Space => iteratedDeriv b (S.decode p.2 m) p.1) := by
  have hbound (θ : ℝ) (u : S.Space) :
      |circleAngularJetEvaluationLinear hS b m θ u| ≤
        (2 * circleSobolevConstant * T.H (T.sample m) ^ γ) * S.grading (b + 1) u := by
    rw [circleAngularJetEvaluationLinear_apply]
    exact (circleModel_iteratedDeriv_abs_le hS hH u m b θ).trans_eq (by ring)
  have hangle (u : S.Space) :
      Continuous (fun θ => circleAngularJetEvaluationLinear hS b m θ u) := by
    have heq : (fun θ => circleAngularJetEvaluationLinear hS b m θ u) =
        iteratedDeriv b (S.decode u m) := by
      funext θ
      exact circleAngularJetEvaluationLinear_apply hS b m θ u
    rw [heq]
    exact (circleDecoded_iteratedDeriv_contDiff hS u m b).continuous
  have hc := continuous_joint_linear_of_uniform_seminorm_bound
    (circleAngularJetEvaluationLinear hS b m) (S.grading (b + 1))
    (continuous_gradedSeminorm (fun i => S.level i) S.bond (b + 1))
    _ hbound hangle
  apply hc.congr
  intro p
  exact circleAngularJetEvaluationLinear_apply hS b m p.1 p.2

/-- Every actual parameter jet is evaluated by the same continuous
angular evaluation functional. -/
def circleDecodedAngularDirections
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → S.Space} (hS : IsCircleModel T γ S)
    (J : SmoothDirections U f) (b m : ℕ) (θ : ℝ) :
    SmoothDirections U (fun x => iteratedDeriv b (S.decode (f x) m) θ) :=
  (solveSmoothDirectionsPostcomp J (circleAngularJetEvaluationCLM hS b m θ)).congrOn
    (fun x _ => circleAngularJetEvaluationCLM_apply hS b m θ (f x))

theorem circleDecodedAngularDirections_jet
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → S.Space} (hS : IsCircleModel T γ S)
    (J : SmoothDirections U f) (b m : ℕ) (θ : ℝ) (k : ℕ) (x : E) (v : Fin k → E) :
    (circleDecodedAngularDirections hS J b m θ).D k x v =
      iteratedDeriv b (S.decode (J.D k x v) m) θ := by
  change circleAngularJetEvaluationCLM hS b m θ (J.D k x v) = _
  exact circleAngularJetEvaluationCLM_apply hS b m θ (J.D k x v)

/-- Decode a genuine circle-valued tower while the angular argument also
varies. The derivatives are actual derivatives in the original source
topology. -/
def circleDecodedJointDirections
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → S.Space}
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    (J : SmoothDirections U f) (m : ℕ) :
    SmoothDirections (U ×ˢ univ) (fun p : E × ℝ => S.decode (f p.1) m p.2) := by
  let K (b : ℕ) (θ : ℝ) := circleDecodedAngularDirections hS J b m θ
  have hcont (k b : ℕ) :
      ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => (K b p.1).D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)) := by
    have hj : ContinuousOn (fun p : ℝ × (E × (Fin k → E)) => J.D k p.2.1 p.2.2)
        (univ ×ˢ (U ×ˢ univ)) :=
      (J.continuous k).comp continuousOn_snd (fun p hp => hp.2)
    have hm : ContinuousOn
        (fun p : ℝ × (E × (Fin k → E)) => (p.1, J.D k p.2.1 p.2.2))
        (univ ×ˢ (U ×ˢ univ)) := continuousOn_fst.prodMk hj
    have hc := (continuous_circleAngularJetEvaluation hS hH b m).comp_continuousOn hm
    apply hc.congr
    intro p hp
    exact circleDecodedAngularDirections_jet hS J b m p.1 k p.2.1 p.2.2
  have hangle (k b : ℕ) (θ : ℝ) (x : E) (_hx : x ∈ U) (v : Fin k → E) :
      HasDerivAt (fun ψ => (K b ψ).D k x v) ((K (b + 1) θ).D k x v) θ := by
    simpa only [K, circleDecodedAngularDirections_jet] using
      circleDecoded_iteratedDeriv_hasDerivAt hS (J.D k x v) m b θ
  exact (angularTowerJointDirections K hcont hangle).congrOn
    (fun p hp => by simp only [iteratedDeriv_zero])

/-- The actual decoder, with both its circle element and angle variable. -/
def circleJointEvaluationDirections
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m)) (m : ℕ) :
    SmoothDirections (univ : Set (S.Space × ℝ))
      (fun p : S.Space × ℝ => S.decode p.1 m p.2) := by
  have J := circleDecodedJointDirections hS hH
    (smoothDirectionsLinear (ContinuousLinearMap.id ℝ S.Space)) m
  simpa only [univ_prod_univ, ContinuousLinearMap.id_apply] using J

/-- The decoded circle displacement with its actual affine lift. The
translation is fixed and may vary arbitrarily with the circle index. -/
def circleAffineLiftJointDirections
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f : E → S.Space}
    (hS : IsCircleModel T γ S) (hH : ∀ m, 0 < T.H (T.sample m))
    (J : SmoothDirections U f) (travel : ℕ → ℝ) (m : ℕ) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => p.2 + travel m + S.decode (f p.1) m p.2) := by
  let L : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let R := (smoothDirectionsLinear (ContinuousLinearMap.id ℝ ℝ)).compAffine L
    (travel m) (J.open_domain.prod isOpen_univ) (fun _ _ => mem_univ _)
  let K := circleDecodedJointDirections hS hH J m
  apply (smoothDirectionsAdd R K).congrOn
  intro p hp
  change (travel m + p.2) + S.decode (f p.1) m p.2 = _
  ring

end ContinuousFlexibility.Statements
