module

public import ContinuousFlexibility.Analysis.N04NegativeChartProjectionJets
public import ContinuousFlexibility.Analysis.N04NegativeChartProjectionBounds
public import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
public import ContinuousFlexibility.Analysis.CylinderMixedJetNorms

/-!
# Mixed state and spatial jets of the literal root projections

The joint tower first identifies the genuine state jet with the raw
even or divided odd projection of the same input jet. Spatial locality
then permits the sharp root estimate on the positive half-plane. No
periodicity or degree-one lift is required of a positive state slice.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem rootProjection_prefix_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (odd : Bool) (G : ℝ × ℝ × ℝ → ℝ),
      ContDiff ℝ ∞ G → ∀ M : ℝ, 0 ≤ M →
      ∀ n : ℕ, n ≤ s →
      CSBound (n + if odd then 1 else 0)
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ)) G M →
      ∀ x ∈ Ioc (0 : ℝ) 1, ∀ θ : ℝ,
        ‖iteratedFDeriv ℝ n
          (if odd then rootOddCoefficient G else rootEven G) (x, θ)‖ ≤ C * M := by
  classical
  choose c hc hb using fun n : Fin (s + 1) => n04NegativeChart_rootProjection_allAngle_bound n.val
  let C : ℝ := 1 + ∑ n : Fin (s + 1), c n
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => (hc n).le)))
  refine ⟨C, hC, fun odd G hG M hM n hn hraw x hx θ => ?_⟩
  let i : Fin (s + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hi : c i ≤ C := (Finset.single_le_sum (fun j _ => (hc j).le)
    (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  exact (hb i odd G hG M hraw x hx θ).trans
    (mul_le_mul_of_nonneg_right hi hM)

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The output is a bound on every supplied actual mixed parameter
tower. The constant is independent of the state space and its finite
representatives, the component, angle, and all evaluated directions. -/
theorem n04NegativeChart_rootProjection_mixedParameter_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (odd : Bool) (U : Set X), IsOpen U → Convex ℝ U →
      ∀ Ω : Set PolarPoint, IsOpen Ω → Convex ℝ Ω → (∀ p ∈ Ω, 0 < p.1) →
      ∀ (G : X → ℝ × ℝ × ℝ → ℝ) (f : X × PolarPoint → ℝ),
      ∀ JG : ∀ q, SmoothDirections U (fun x => G x q),
      ∀ JF : SmoothDirections (U ×ˢ Ω) f,
      (∀ x ∈ U, ∀ p : PolarPoint, p ∈ Ω →
        f (x, p) = if odd then rootOddCoefficient (G x) p else rootEven (G x) p) →
      ∀ n : ℕ, ∀ x ∈ U, ∀ v : Fin n → X,
      ContDiff ℝ ∞ (fun q => (JG q).D n x v) →
      ∀ M : ℝ, 0 ≤ M →
      ∀ a b : ℕ, a + b ≤ s →
      CSBound (a + b + if odd then 1 else 0)
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
        (fun q => (JG q).D n x v) M →
      ∀ q : PolarPoint, q ∈ Ω → q.1 ∈ Ioc (0 : ℝ) 1 →
      ∀ Q : SmoothDirections U (fun y => mixedDerivative a b (fun p => f (y, p)) q),
        |Q.D n x v| ≤ C * M := by
  obtain ⟨C, hC, hb⟩ := rootProjection_prefix_bound s
  refine ⟨C, hC, fun odd U hU hc Ω hΩ hcΩ hΩpos G f JG JF heq n x hx v hG M hM
    a b hab hraw q hqp hq Q => ?_⟩
  have hconvex : Convex ℝ (U ×ˢ Ω) := hc.prod hcΩ
  let g : ℝ × ℝ × ℝ → ℝ := fun p => (JG p).D n x v
  have hstate (p : PolarPoint) (hp : p ∈ Ω) :
      JF.D n (x, p) (fun i => (v i, 0)) =
        (if odd then rootOddCoefficient g else rootEven g) p := by
    let K : SmoothDirections U
        (fun y => if odd then rootOddCoefficient (G y) p else rootEven (G y) p) :=
      (JF.freezeSpatial hU p hp).congrOn (fun y hy => heq y hy p hp)
    have hK : K.D n x v = JF.D n (x, p) (fun i => (v i, 0)) :=
      JF.freezeSpatial_apply hU p hp n x v
    rw [← hK]
    cases odd with
    | false => exact n04NegativeChart_rootEven_stateJet JG p K n x hx v
    | true => exact n04NegativeChart_rootOddCoefficient_stateJet JG p (hΩpos p hp).ne' K n x hx v
  have hsmooth : ContDiffOn ℝ ∞
      (if odd then rootOddCoefficient g else rootEven g) Ω := by
    cases odd with
    | false => exact (contDiffOn_rootEven hG).mono (fun p hp => ⟨(hΩpos p hp).le, mem_univ _⟩)
    | true => exact (contDiffOn_rootOddCoefficient hG).mono (fun p hp => ⟨(hΩpos p hp).le, mem_univ _⟩)
  rw [n04Realization_mixedParameter_eq_joint JF hU hΩ hconvex a b n x hx q hqp Q v,
    mixedDerivative_congr_on_open hΩ hstate a b hqp]
  exact (abs_mixedDerivative_le_norm_iteratedFDeriv hΩ hsmooth a b hqp).trans
    (hb odd g hG M hM (a + b) hab hraw q.1 hq q.2)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_mixedParameter_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_rootProjection_mixedParameter_bound
