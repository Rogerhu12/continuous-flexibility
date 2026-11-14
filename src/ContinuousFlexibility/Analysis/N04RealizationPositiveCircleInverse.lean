module

public import ContinuousFlexibility.Analysis.CircleSingleComponentJets
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
public import ContinuousFlexibility.Analysis.CircleJointEvaluation
public import ContinuousFlexibility.Analysis.SpacesTraceCircleBounds

/-!
# The actual circle inverse with topological state parameters

The finite endpoint data are realized in the existing circle model.
Its proved positive-lift inversion supplies a genuine joint tower for
the literal chosen inverse. No normed structure on the parameter space,
inverse regularity premise, or change of parameter domain is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  {U : Set E}

/-- Realize supplied angular towers in the original circle space. The
uniform seminorm bounds supply the joint continuity needed for this step. -/
theorem n04Realization_singleComponentDirections
    (hS : IsCircleModel T γ S) (hU : IsOpen U) (hc : Convex ℝ U)
    (hM : ∀ i, 0 ≤ T.M (T.sample i)) (hH : ∀ i, 0 ≤ T.H (T.sample i))
    (f : E → ℝ → ℝ)
    (hf : ∀ x ∈ U, ContDiff ℝ ∞ (f x))
    (hperiod : ∀ x ∈ U, Function.Periodic (f x) Real.pi)
    (J : ∀ b θ, SmoothDirections U (fun x => iteratedDeriv b (f x) θ))
    (hbound : ∀ b, UniformScalarJetSeminormBounds (J b)) (m : ℕ) :
    ∃ F : E → S.Space, ∃ K : SmoothDirections U F,
      ∀ x ∈ U, S.decode (F x) = circleSingleComponentField m (f x) := by
  classical
  let F : E → S.Space := fun x =>
    if hx : x ∈ U then
      circleRealize hS (circleSingleComponentField m (f x))
        (circleSingleComponentField_member T γ m (f x) (hf x hx) (hperiod x hx))
    else 0
  have hF (x : E) (hx : x ∈ U) :
      S.decode (F x) = circleSingleComponentField m (f x) := by
    simp only [F, dif_pos hx]
    exact circleRealize_decode _ _ _
  have hangle (b : ℕ) (θ : ℝ) (x : E) (hx : x ∈ U) :
      HasDerivAt (iteratedDeriv b (f x)) (iteratedDeriv (b + 1) (f x) θ) θ := by
    rw [iteratedDeriv_succ]
    exact ((spaces_contDiff_iteratedDeriv (hf x hx) b).differentiable
      (by simp) θ).hasDerivAt
  have hper (x : E) (hx : x ∈ U) :
      Function.Periodic (fun θ => iteratedDeriv 0 (f x) θ) Real.pi := by
    simpa only [iteratedDeriv_zero] using hperiod x hx
  have hreal := exists_singleComponent_circle_smoothDirections J hU hc hbound
    hangle hper m hS hM hH F
    (fun x hx => by simpa only [iteratedDeriv_zero] using hF x hx)
  exact ⟨F, hreal.choose, hF⟩

/-- Invert the actual lift represented by a single-component displacement.
The returned tower is for `Function.invFun φ`, on the original product domain. -/
def n04Realization_circleInverseJointDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (φ : E → ℝ → ℝ) (F : E → S.Space) (J : SmoothDirections U F) (m : ℕ)
    (hF : ∀ x ∈ U,
      S.decode (F x) = circleSingleComponentField m (fun θ => φ x θ - θ))
    (hpositive : ∀ x ∈ U, ∀ θ, 0 < deriv (φ x) θ) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => Function.invFun (φ p.1) p.2) := by
  have hlift (x : E) (hx : x ∈ U) :
      circleAffineLift (fun _ => 0) (S.decode (F x)) 1 m = φ x := by
    funext θ
    rw [hF x hx]
    simp only [circleAffineLift, circleSingleComponentField,
      ite_true, one_mul, add_zero]
    ring
  have hpos : MapsTo F U (circlePositiveLiftDomain S) := by
    intro x hx
    apply (circlePositiveLiftDomain_iff hS (fun _ => 0) (F x)).mpr
    intro i θ
    by_cases him : i = m
    · subst i
      rw [hlift x hx]
      exact hpositive x hx θ
    · have heq : circleAffineLift (fun _ => 0) (S.decode (F x)) 1 i =
          (fun t : ℝ => t) := by
        funext t
        rw [hF x hx]
        simp only [circleAffineLift, circleSingleComponentField,
          if_neg him, one_mul, add_zero]
      rw [heq, deriv_id'']
      exact zero_lt_one
  let G : E → S.Space :=
    fun x => circlePositiveInversePerturbation hS hT hD hγ (fun _ => 0) (F x)
  let K : SmoothDirections U G :=
    circleInversePerturbationDirections hS hT hD hγ hi (fun _ => 0) J hpos
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hD).2 i
  apply (circleAffineLiftJointDirections hS hH K (fun _ => 0) m).congr
  intro p hp
  have hd : S.decode (G p.1) m p.2 =
      circleAffineInverse (fun _ => 0) (F p.1) m p.2 - (p.2 - 0) :=
    congrArg (fun e : ℕ → ℝ → ℝ => e m p.2)
      (circlePositiveInversePerturbation_decode hS hT hD hγ (fun _ => 0)
        (F p.1) (hpos hp.1))
  have hinv : circleAffineInverse (fun _ => 0) (F p.1) m p.2 =
      Function.invFun (φ p.1) p.2 :=
    congrArg (fun f : ℝ → ℝ => Function.invFun f p.2) (hlift p.1 hp.1)
  rw [hd, hinv]
  ring

end ContinuousFlexibility.Analysis
