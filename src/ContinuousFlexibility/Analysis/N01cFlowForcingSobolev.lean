import ContinuousFlexibility.Analysis.N01cCircleForcingProducts
import ContinuousFlexibility.Analysis.N01cFlowForcingExpansion

/-!
# Sobolev one-high products for the genuine truncated flow forcing

The forcing is exactly the finite sum obtained by expanding the actual
speed tower on its graph slots.  Its circle Sobolev norm is bounded by
one high factor in each actual product. The hypotheses here only identify
the qualitative smooth periodic factors; no flow or forcing size estimate
is assumed. Substitution of the speed estimates and the strict lower-order
induction then leaves the common-base state interpolation step.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff ENNReal BigOperators

variable {P : ℝ} [Fact (0 < P)]

/-- A finite sum of actual derivative towers is controlled in the same
Sobolev order. The harmless constant uses no input norm. -/
theorem circle_sobolevNorm_finite_sum_le_of_derivatives
    {ι : Type*} [Fintype ι] (f : ι → ℕ → C(AddCircle P, ℝ))
    (hf : ∀ i, ∀ n : ℕ, ∀ θ : ℝ,
      HasDerivAt (fun η : ℝ => f i n (η : AddCircle P))
        (f i (n + 1) (θ : AddCircle P)) θ) (s : ℕ) :
    circleRealSobolevNorm (s : ℝ) (∑ i, f i 0) ≤
      (2 : ℝ) ^ (s + 1) * ∑ i, circleRealSobolevNorm (s : ℝ) (f i 0) := by
  classical
  have hsum (n : ℕ) (θ : ℝ) :
      HasDerivAt (fun η : ℝ => (∑ i, f i n) (η : AddCircle P))
        ((∑ i, f i (n + 1)) (θ : AddCircle P)) θ := by
    simpa only [ContinuousMap.sum_apply] using
      HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hf i n θ)
  have hL (n : ℕ) (hns : n ≤ s) :
      (eLpNorm (∑ i, f i n) 2 AddCircle.haarAddCircle).toReal ≤
        ∑ i, circleRealSobolevNorm (s : ℝ) (f i 0) := by
    simpa only [ContinuousMap.coe_sum] using
      (circle_l2_sum_le (fun i => f i n)).trans
        (Finset.sum_le_sum (fun i _ => circle_real_derivative_l2_le_sobolev (f i) (hf i) hns))
  calc
    _ ≤ (2 : ℝ) ^ s *
        ((eLpNorm (∑ i, f i 0) 2 AddCircle.haarAddCircle).toReal +
          (eLpNorm (∑ i, f i s) 2 AddCircle.haarAddCircle).toReal) := by
      simpa only [ContinuousMap.coe_sum] using
        circle_real_sobolevNorm_le_derivative_endpoints (fun n => ∑ i, f i n) hsum s
    _ ≤ (2 : ℝ) ^ s *
        ((∑ i, circleRealSobolevNorm (s : ℝ) (f i 0)) +
          ∑ i, circleRealSobolevNorm (s : ℝ) (f i 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hL 0 (Nat.zero_le s)) (hL s le_rfl)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- A partition together with the slots using the state component. -/
abbrev FlowForcingChoice (N : ℕ) :=
  (c : _root_.OrderedFinpartition N) × Finset (Fin c.length)

section Forcing

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {G : E × PolarPoint → ℝ}
  (J : ContinuousTimeSpeedTower U G) (Θ : ℝ → E × ℝ → ℝ) {N : ℕ}
  (B : ℝ → ∀ k : ℕ, k < N → ContinuousStateVariation U k)
  (p : E × ℝ) (v : Fin N → E)

/-- Each factor is either the actual selected speed derivative or the
actual selected lower variation, as a function of the initial angle. -/
def flowForcingFactors (d : FlowForcingChoice N) :
    Fin (d.1.length + 1) → ℝ → ℝ :=
  Fin.cons (fun α => flowSelectedSpeedCoefficient J (Θ α) d.1 d.2 p v)
    (fun i α => flowSelectedLowerFactor (B α) d.1 d.2 p v i)

/-- The original truncated forcing is exactly this finite sum of products. -/
theorem truncatedFlowForcing_eq_finite_products (α : ℝ) :
    truncatedFlowForcing J (Θ α) (B α) p v =
      ∑ d : FlowForcingChoice N, ∏ i, flowForcingFactors J Θ B p v d i α := by
  classical
  rw [truncatedFlowForcing_eq_selected_products]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro s _
  simp only [flowForcingFactors, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem truncatedFlowForcing_periodic_of_factors
    (hp : ∀ d i, Function.Periodic (flowForcingFactors J Θ B p v d i) P) :
    Function.Periodic (fun α => truncatedFlowForcing J (Θ α) (B α) p v) P := by
  classical
  intro α
  change truncatedFlowForcing J (Θ (α + P)) (B (α + P)) p v =
    truncatedFlowForcing J (Θ α) (B α) p v
  rw [truncatedFlowForcing_eq_finite_products, truncatedFlowForcing_eq_finite_products]
  apply Finset.sum_congr rfl
  intro d _
  exact Finset.prod_congr rfl (fun i _ => hp d i α)

theorem truncatedFlowForcing_contDiff_of_factors
    (hf : ∀ d i, ContDiff ℝ ∞ (flowForcingFactors J Θ B p v d i)) :
    ContDiff ℝ ∞ (fun α => truncatedFlowForcing J (Θ α) (B α) p v) := by
  classical
  have he : (fun α => truncatedFlowForcing J (Θ α) (B α) p v) =
      fun α => ∑ d : FlowForcingChoice N, ∏ i, flowForcingFactors J Θ B p v d i α :=
    funext (truncatedFlowForcing_eq_finite_products J Θ B p v)
  rw [he]
  exact ContDiff.sum (fun d _ => contDiff_prod (fun i _ => hf d i))

/-- Canonical circle jets of the genuine truncated forcing. -/
def truncatedFlowForcingCircleJet
    (hp : ∀ d i, Function.Periodic (flowForcingFactors J Θ B p v d i) P)
    (hf : ∀ d i, ContDiff ℝ ∞ (flowForcingFactors J Θ B p v d i))
    (n : ℕ) : C(AddCircle P, ℝ) :=
  periodicCircleJet (fun α => truncatedFlowForcing J (Θ α) (B α) p v)
    (truncatedFlowForcing_periodic_of_factors J Θ B p v hp)
    (truncatedFlowForcing_contDiff_of_factors J Θ B p v hf) n

theorem truncatedFlowForcingCircleJet_eq_sum_products
    (hp : ∀ d i, Function.Periodic (flowForcingFactors J Θ B p v d i) P)
    (hf : ∀ d i, ContDiff ℝ ∞ (flowForcingFactors J Θ B p v d i))
    (n : ℕ) :
    truncatedFlowForcingCircleJet J Θ B p v hp hf n =
      ∑ d : FlowForcingChoice N,
        circleProductJet (flowForcingFactors J Θ B p v d) (hp d) (hf d) n := by
  classical
  ext θ
  induction θ using QuotientAddGroup.induction_on
  rename_i α
  simp only [truncatedFlowForcingCircleJet, periodicCircleJet_coe_apply,
    ContinuousMap.sum_apply, circleProductJet_coe_apply]
  have he : (fun η => truncatedFlowForcing J (Θ η) (B η) p v) =
      fun η => ∑ d : FlowForcingChoice N, ∏ i, flowForcingFactors J Θ B p v d i η :=
    funext (truncatedFlowForcing_eq_finite_products J Θ B p v)
  rw [he]
  exact iteratedDeriv_fun_sum (fun d _ =>
    (contDiff_prod (fun i _ => hf d i)).contDiffAt.of_le (by simp))

/-- The actual higher-variation forcing has precisely one high factor
in every finite product. The speed factor is an actual mixed-slot speed
jet, and the other factors are the actual strict lower variations. -/
theorem truncatedFlowForcing_sobolev_le
    (hp : ∀ d i, Function.Periodic (flowForcingFactors J Θ B p v d i) P)
    (hf : ∀ d i, ContDiff ℝ ∞ (flowForcingFactors J Θ B p v d i))
    (s : ℕ) :
    circleRealSobolevNorm (s : ℝ)
        (truncatedFlowForcingCircleJet J Θ B p v hp hf 0) ≤
      (2 : ℝ) ^ (s + 1) *
        ∑ d : FlowForcingChoice N, circleProductSobolevConstant P d.1.length s *
          ∑ j : Fin (d.1.length + 1),
            circleRealSobolevNorm (s : ℝ)
              (periodicCircleJet (flowForcingFactors J Θ B p v d j) (hp d j) (hf d j) 0) *
            ∏ i ∈ Finset.univ.erase j,
              circleRealSobolevNorm 1
                (periodicCircleJet (flowForcingFactors J Θ B p v d i) (hp d i) (hf d i) 0) := by
  classical
  rw [truncatedFlowForcingCircleJet_eq_sum_products]
  apply (circle_sobolevNorm_finite_sum_le_of_derivatives
    (fun d => circleProductJet (flowForcingFactors J Θ B p v d) (hp d) (hf d))
    (fun d => circleProductJet_hasDerivAt
      (flowForcingFactors J Θ B p v d) (hp d) (hf d)) s).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun d _ =>
    circleProductJet_sobolev_le (flowForcingFactors J Θ B p v d) (hp d) (hf d) s)

end Forcing

end ContinuousFlexibility.Analysis

