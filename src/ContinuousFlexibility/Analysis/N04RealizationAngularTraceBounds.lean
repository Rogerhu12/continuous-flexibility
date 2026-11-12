import ContinuousFlexibility.Analysis.N04RealizationLogHeightTraceRegularity

/-!
# The actual parameter jets of an angular trace

The existing mixed representation has the supplied angular tower at
radial order zero and the zero tower at every positive radial order.
Uniqueness identifies any genuine mixed tower with these same data.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n04Realization_angularTrace_jet_bound
    {U : Set X} {f : X → ℝ → ℝ} {a b k : ℕ} {q : PolarPoint}
    (J : SmoothDirections U (fun x => mixedDerivative a b (fun p => f x p.2) q))
    (JA : SmoothDirections U (fun x => iteratedDeriv b (f x) q.2))
    {x : X} (hx : x ∈ U) (v : Fin k → X)
    {M H t : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hb : ‖JA.D k x v‖ ≤ M * parameterHeightWeight H k * t ^ b) :
    ‖J.D k x v‖ ≤ M * parameterHeightWeight H k * t ^ (a + b) := by
  by_cases ha : a = 0
  · subst a
    let J0 : SmoothDirections U (fun y => iteratedDeriv b (f y) q.2) :=
      J.congr (fun _ _ => by
        simp only [n04Realization_mixedDerivative_angularField, ite_true])
    have heq := HasProjectiveJetsOn.unique J.open_domain
      J0.hasProjectiveJetsOn JA.hasProjectiveJetsOn k x hx
    have hd : J.D k x v = JA.D k x v :=
      congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    simpa only [hd, Nat.zero_add] using hb
  · let J0 : SmoothDirections U (fun _ : X => (0 : ℝ)) :=
      J.congr (fun _ _ => by
        simp only [n04Realization_mixedDerivative_angularField, if_neg ha])
    have hz : J.D k x v = 0 := by
      by_cases hk : k = 0
      · subst k
        exact smoothDirections_D_zero_apply J0 hx v
      · exact smoothDirections_D_constant J0 (Nat.pos_of_ne_zero hk) hx v
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH k)) (pow_nonneg ht _)

end ContinuousFlexibility.Analysis
