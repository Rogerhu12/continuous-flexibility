module

public import ContinuousFlexibility.Analysis.N01cJointJetContinuity
public import ContinuousFlexibility.Analysis.N01cStateAngleSmoothDirections
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Joint jet continuity from local grading bounds

A continuous seminorm controls a true multilinear map once it controls
that map on its unit ball. Applied to two consecutive genuine jets on a
convex grading neighbourhood, this gives joint continuity in the state,
external variables and every direction. The source remains a topological
real module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Strict seminorm balls with any fixed centre are convex. -/
theorem convex_seminormDisplacement_lt
    (p : Seminorm ℝ X) (center : X) (R : ℝ) :
    Convex ℝ {x : X | p (x - center) < R} := by
  intro x hx y hy a b ha hb hab
  change p (x - center) < R at hx
  change p (y - center) < R at hy
  have he : a • x + b • y - center =
      a • (x - center) + b • (y - center) := by
    have hc : a • center + b • center = center := by
      rw [← add_smul, hab, one_smul]
    calc
      _ = a • x + b • y - (a • center + b • center) := by rw [hc]
      _ = _ := by rw [smul_sub, smul_sub]; abel
  have hbound : p (a • x + b • y - center) ≤
      a * p (x - center) + b * p (y - center) := by
    rw [he]
    simpa only [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb] using
        map_add_le_add p (a • (x - center)) (b • (y - center))
  have hstrict : a * p (x - center) + b * p (y - center) < a * R + b * R := by
    by_cases hbpos : 0 < b
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.le ha)
        (mul_lt_mul_of_pos_left hy hbpos)
    · have hb0 : b = 0 := le_antisymm (le_of_not_gt hbpos) hb
      have ha1 : a = 1 := by linarith
      simpa only [ha1, hb0, one_mul, zero_mul, add_zero] using hx
  exact hbound.trans_lt (hstrict.trans_eq (by rw [← add_mul, hab, one_mul]))

/-- The existing unit-ball normalization also controls seminorm kernels,
and includes the empty multilinear arity. -/
theorem multilinear_abs_le_product_of_unitBound
    {k : ℕ} (A : X [×k]→L[ℝ] ℝ) (p : Seminorm ℝ X)
    {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ v : Fin k → X, (∀ i, p (v i) < 1) → |A v| ≤ C) :
    ∀ v : Fin k → X, |A v| ≤ C * ∏ i, p (v i) := by
  have hn := multilinear_bound_of_unitBall A (normSeminorm ℝ ℝ) p 0 hC (a := 1)
    (fun v hv => by
      simpa [coe_normSeminorm, Real.norm_eq_abs] using hunit v hv)
  intro v
  simpa [coe_normSeminorm, multilinearTameSize, Real.norm_eq_abs] using hn v

/-- Actual finite-affine smoothness and bounded consecutive unit-ball
jets imply evaluated joint continuity on the original open domain. -/
theorem stateAngularJets_joint_continuous_of_graded_bounds
    (p : ℕ → Seminorm ℝ X) (hp : ∀ n, Continuous (p n)) (center : X)
    {U : Set X} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : X × PolarPoint → ℝ} (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hjets : ∀ b K : ℕ, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ q : PolarPoint, ∀ x ∈ U,
      ∀ R : ℝ, 1 ≤ R → p N (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p N (v i) < 1) →
        |(J b q).D k x v| ≤ C * R) :
    ∀ b k, ContinuousOn
      (fun z : (X × PolarPoint) × (Fin k → X) => (J b z.1.2).D k z.1.1 z.2)
      ((U ×ˢ (univ : Set PolarPoint)) ×ˢ univ) := by
  intro b k
  rintro ⟨⟨x₀, q₀⟩, v₀⟩ hz
  have hx₀ : x₀ ∈ U := hz.1.1
  obtain ⟨N, C, hC, hb⟩ := hjets b (k + 1)
  let R : ℝ := 1 + p N (x₀ - center)
  let V : Set X := U ∩ {x : X | p N (x - center) < R}
  have hR : 1 ≤ R := le_add_of_nonneg_right (apply_nonneg (p N) _)
  have hV : IsOpen V := hU.inter
    (isOpen_Iio.preimage ((hp N).comp (continuous_id.sub continuous_const)))
  have hcV : Convex ℝ V := hconv.inter (convex_seminormDisplacement_lt (p N) center R)
  have hxV : x₀ ∈ V := by
    refine ⟨hx₀, ?_⟩
    change p N (x₀ - center) < 1 + p N (x₀ - center)
    linarith
  have hVU : V ⊆ U := fun x hx => hx.1
  have hCR : 0 ≤ C * R := mul_nonneg hC (zero_le_one.trans hR)
  have hprod {j : ℕ} (hj : j ≤ k + 1) (q : PolarPoint)
      (x : X) (hx : x ∈ V) (v : Fin j → X) :
      |(J b q).D j x v| ≤ (C * R) * ∏ i, p N (v i) :=
    multilinear_abs_le_product_of_unitBound ((J b q).D j x) (p N) hCR
      (fun w hw => hb j hj q x hx.1 R hR hx.2.le w hw) v
  have hfixed (v : Fin k → X) :
      ContinuousAt (fun q : PolarPoint => (J b q).D k x₀ v) q₀ :=
    (contDiff_stateJet_external hU (hf.angular hU b) (J b) k v hx₀).continuous.continuousAt
  exact (continuousAt_stateJetEvaluation_of_nextJet_bound (J b)
    (p N) (hp N) (C * R) k v₀ hV hcV hxV hVU
    (Filter.univ_mem : (univ : Set PolarPoint) ∈ 𝓝 q₀) hfixed
    (fun q _ v => hprod (Nat.le_succ k) q x₀ hxV v)
    (fun q _ x hx v => hprod le_rfl q x hx v)).continuousWithinAt

/-- This constructor retains the actual word tower and all its
time/state/direction evaluation continuity. -/
def continuousTimeSpeedTower_of_graded_stateAngularJets
    (p : ℕ → Seminorm ℝ X) (hp : ∀ n, Continuous (p n)) (center : X)
    {U : Set X} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : X × PolarPoint → ℝ} (hf : IsFiniteAffineTimeSmooth U f)
    (J : ∀ b : ℕ, ∀ q : PolarPoint, SmoothDirections U
      (fun x => iteratedDeriv b (fun θ => f (x, (q.1, θ))) q.2))
    (hjets : ∀ b K : ℕ, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ q : PolarPoint, ∀ x ∈ U,
      ∀ R : ℝ, 1 ≤ R → p N (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p N (v i) < 1) →
        |(J b q).D k x v| ≤ C * R) :
    ContinuousTimeSpeedTower U f :=
  continuousTimeSpeedTower_of_stateAngularJets hU hf J
    (stateAngularJets_joint_continuous_of_graded_bounds p hp center hU hconv hf J hjets)

end ContinuousFlexibility.Analysis
