import ContinuousFlexibility.Analysis.WeightedJointComposition
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Operations on joint growth with one high parameter factor

Increasing a common low order and loss preserves the actual estimates.
Pairing combines uniformly bounded families, and ordinary smooth maps
on a finite-dimensional target preserve unweighted joint growth by the
fixed interpolation budget. This supplies the discriminant polynomial
before taking its positive square root.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E P F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem UniformWeightedJointGrowth.mono
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W : I → ℝ} (hW : ∀ i, 0 ≤ W i)
    {U : Set E} {V : I → Set P} {f : I → E × P → F}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {base loss B L : ℕ} (hJ : UniformWeightedJointGrowth p W J base loss)
    (hb : base ≤ B) (hl : loss ≤ L) : UniformWeightedJointGrowth p W J B L := by
  intro R hR n
  obtain ⟨C, Q, hC, hQ, hc⟩ := hJ R hR n
  refine ⟨C, Q, hC, hQ, fun i x hx hlow y hy v hv => ?_⟩
  have hh := hc i x hx ((hp hb x).trans hlow) y hy v (fun j =>
    (add_le_add (hp hb (v j).1) le_rfl).trans (hv j))
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg (hW i) _))
  exact add_le_add (add_le_add le_rfl (hp (Nat.add_le_add_left hl n) x))
    (Finset.sum_le_sum (fun j _ => hp (Nat.add_le_add_left hl n) (v j).1))

theorem UniformWeightedJointGrowth.withWeight
    {p : ℕ → Seminorm ℝ E} {U : Set E} {V : I → Set P} {f : I → E × P → F}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p (fun _ => 1) J base loss) (W : I → ℝ) :
    UniformWeightedJointGrowth p W J base loss := by
  intro R hR n
  obtain ⟨C, Q, hC, _, hb⟩ := hJ R hR n
  refine ⟨C, 0, hC, le_rfl, fun i x hx hlow y hy v hv => ?_⟩
  simpa only [Real.one_rpow, Real.rpow_zero] using hb i x hx hlow y hy v hv

theorem UniformWeightedJointGrowth.prodMk
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {U : Set E} {V : I → Set P} {f : I → E × P → F} {g : I → E × P → G}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hK : UniformWeightedJointGrowth p W K base loss) :
    UniformWeightedJointGrowth p W (fun i => smoothDirectionsProd (J i) (K i)) base loss := by
  intro R hR n
  obtain ⟨A, P₀, hA, hP, hb⟩ := hJ R hR n
  obtain ⟨B, Q, hB, hQ, hc⟩ := hK R hR n
  refine ⟨A + B, P₀ + Q, add_nonneg hA hB, add_nonneg hP hQ, ?_⟩
  intro i x hx hlow y hy v hv
  let Z : ℝ := 1 + p (n + loss) x + ∑ j : Fin n, p (n + loss) (v j).1
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hpower : 0 ≤ W i ^ (P₀ + Q) := Real.rpow_nonneg (zero_le_one.trans (hW i)) _
  have ha : A * W i ^ P₀ * Z ≤ (A + B) * W i ^ (P₀ + Q) * Z := by
    apply mul_le_mul_of_nonneg_right _ hZ
    exact mul_le_mul (le_add_of_nonneg_right hB)
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_right hQ))
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (add_nonneg hA hB)
  have hb' : B * W i ^ Q * Z ≤ (A + B) * W i ^ (P₀ + Q) * Z := by
    apply mul_le_mul_of_nonneg_right _ hZ
    exact mul_le_mul (le_add_of_nonneg_left hA)
      (Real.rpow_le_rpow_of_exponent_le (hW i) (le_add_of_nonneg_left hP))
      (Real.rpow_nonneg (zero_le_one.trans (hW i)) _) (add_nonneg hA hB)
  change max ‖(J i).D n (x, y) v‖ ‖(K i).D n (x, y) v‖ ≤ _
  exact max_le ((hb i x hx hlow y hy v hv).trans ha)
    ((hc i x hx hlow y hy v hv).trans hb')

/-- A bounded low parameter ball gives a bounded range in a proper
normed target. All ordinary outer jets are bounded on that one ball. -/
theorem UniformWeightedJointGrowth.comp_smooth_unweighted
    [ProperSpace F]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hIp : HasInterpolation p)
    {U : Set E} {V : I → Set P} {f : I → E × P → F}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p (fun _ => 1) J base loss)
    (g : F → G) (hg : ContDiff ℝ ∞ g)
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => g (f i z))) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧
      UniformWeightedJointGrowth p (fun _ => 1) K B L := by
  have houter : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p (max base loss) x ≤ R → ∀ y ∈ V i,
        ‖contDiffOnJetFamily g univ k (f i (x, y))‖ ≤ C * (1 : ℝ) ^ Q := by
    intro R hR k
    obtain ⟨A, Q₀, hA, _, hzero⟩ := hJ R hR 0
    have hcont : Continuous (iteratedFDeriv ℝ k g) := hg.continuous_iteratedFDeriv (by simp)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : F) (A * (1 + R))).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max C 0, 0, le_max_right _ _, le_rfl, ?_⟩
    intro i x hx hlow y hy
    have hvalue : ‖f i (x, y)‖ ≤ A * (1 + p loss x) := by
      have h := hzero i x hx ((hp (le_max_left _ _) x).trans hlow) y hy
        Fin.elim0 (fun j => Fin.elim0 j)
      simpa only [(J i).zero (x, y) ⟨hx, hy⟩, Nat.zero_add,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, Real.one_rpow, mul_one] using h
    have hball : f i (x, y) ∈ Metric.closedBall (0 : F) (A * (1 + R)) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hvalue.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((hp (le_max_right _ _) x).trans hlow)) hA)
    change ‖iteratedFDerivWithin ℝ k g univ (f i (x, y))‖ ≤ _
    rw [iteratedFDerivWithin_univ, Real.rpow_zero, mul_one]
    exact (hC _ hball).trans (le_max_left _ _)
  obtain ⟨B, L, hb, ho, h⟩ := hJ.comp_contDiff hp hIp (fun _ => le_rfl)
    isOpen_univ hg.contDiffOn (fun _ _ _ => mem_univ _) (max base loss) houter
  exact ⟨B, L, hb, (le_max_right _ _).trans ho,
    h.congr K (fun _ _ _ => rfl)⟩

end ContinuousFlexibility.Analysis
