module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsCalculus
public import ContinuousFlexibility.Analysis.CircleJointEvaluation

/-!
# Uniform angular evaluation of the actual circle jets

The circle norm already contains every component, so angular evaluation
introduces only its original sample height weight. A single output order
controls the entire finite prefix of angular derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

/-- Evaluate a genuine circle-valued parameter jet at any component and
angle, uniformly over all angular orders up to the requested order. -/
theorem n04PositiveGeometry_endpointBounds_angleEvaluation
    {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (hH : ∀ m, 0 < T.H (T.sample m))
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) {U : Set E} {f : E → M.Space}
    (J : SmoothDirections U f) {n s loss B : ℕ} {K : ℝ}
    {x : E} (hx : x ∈ U) (v : Fin n → E)
    (hbound : M.grading (s + 1) (J.D n x v) ≤
      K * tameJetSize p n (s + 1) loss B x v)
    (b : ℕ) (hb : b ≤ s) (m : ℕ) (θ : ℝ)
    (Jθ : SmoothDirections U (fun y => iteratedDeriv b (M.decode (f y) m) θ)) :
    |Jθ.D n x v| ≤
      (2 * circleSobolevConstant * K) * T.H (T.sample m) ^ γ *
        tameJetSize p n s (loss + 1) B x v := by
  have hjet : Jθ.D n x v = iteratedDeriv b (M.decode (J.D n x v) m) θ :=
    (congrArg (fun A => A v)
      (Jθ.unique (circleDecodedAngularDirections hM J b m θ) n x hx)).trans
        (circleDecodedAngularDirections_jet hM J b m θ n x v)
  have hgrade : M.grading (b + 1) (J.D n x v) ≤
      K * tameJetSize p n (s + 1) loss B x v :=
    ((gradedSeminorm_monotone (fun j => M.level j) M.bond)
      (Nat.add_le_add_right hb 1) (J.D n x v)).trans hbound
  have hweight : tameJetSize p n (s + 1) loss B x v =
      tameJetSize p n s (loss + 1) B x v := by
    have he : s + 1 + loss = s + (loss + 1) := by omega
    simp only [tameJetSize, he]
  have hsob : 0 ≤ 2 * circleSobolevConstant :=
    mul_nonneg (by norm_num) circleSobolevConstant_nonneg
  calc
    _ = |iteratedDeriv b (M.decode (J.D n x v) m) θ| := congrArg abs hjet
    _ ≤ (2 * circleSobolevConstant * M.grading (b + 1) (J.D n x v)) *
        T.H (T.sample m) ^ γ :=
      ContinuousFlexibility.Statements.circleModel_iteratedDeriv_abs_le hM hH
        (J.D n x v) m b θ
    _ ≤ (2 * circleSobolevConstant *
        (K * tameJetSize p n (s + 1) loss B x v)) * T.H (T.sample m) ^ γ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrade hsob)
        (Real.rpow_nonneg (hH m).le _)
    _ = _ := by rw [hweight]; ring

/-- A complete fixed-base circle tower gives one common-base estimate
for every decoded angular scalar tower, uniformly in component and
angle. The one additional high derivative is the Sobolev evaluation. -/
theorem n04PositiveGeometry_endpointBounds_decoded_oneHigh
    {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (hH : ∀ m, 0 < T.H (T.sample m))
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {p : ℕ → Seminorm ℝ E} {U : Set E} {f : E → M.Space}
    {J : SmoothDirections U f} (hJ : N04EndpointFixedBaseBounds p M.grading J) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ ell : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ b : ℕ, b ≤ s → ∀ m : ℕ, ∀ θ : ℝ,
        ∀ Jθ : SmoothDirections U (fun y => iteratedDeriv b (M.decode (f y) m) θ),
        ∀ x ∈ U, p B x ≤ R → ∀ v : Fin n → E,
          |Jθ.D n x v| ≤ K * T.H (T.sample m) ^ γ *
            tameJetSize p n s ell B x v := by
  refine hJ.elim ?_
  intro B hB
  refine ⟨B, fun n => ?_⟩
  refine (hB n).elim ?_
  intro ell hell
  refine ⟨ell + 1, fun R hR s => ?_⟩
  refine (hell R hR (s + 1)).elim ?_
  intro K hK
  refine ⟨2 * circleSobolevConstant * K,
    mul_nonneg (mul_nonneg (by norm_num) circleSobolevConstant_nonneg) hK.1, ?_⟩
  intro b hb m θ Jθ x hx hxR v
  exact n04PositiveGeometry_endpointBounds_angleEvaluation hM hH p J hx v
    (hK.2 x hx hxR v) b hb m θ Jθ

end ContinuousFlexibility.Analysis
