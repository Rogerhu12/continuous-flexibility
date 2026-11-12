import ContinuousFlexibility.Analysis.WeightedJointOperations
import ContinuousFlexibility.Analysis.PolynomialProductOuterJets

/-!
# Products of actual weighted joint towers with fixed loss

Pairing the two genuine towers and postcomposing with multiplication
uses one finite-partition budget. The range on a common low ball grows
by a component power, so every outer product jet has the required
uniform bound. No high seminorm is multiplied by another high seminorm
in the resulting estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem UniformWeightedJointGrowth.mul
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hIp : HasInterpolation p)
    {W : I → ℝ} (hW : ∀ i, 1 ≤ W i)
    {U : Set E} {V : I → Set P} {f g : I → E × P → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)}
    {K : ∀ i, SmoothDirections (U ×ˢ V i) (g i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hK : UniformWeightedJointGrowth p W K base loss)
    (H : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => f i z * g i z)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W H B L := by
  let QJ := fun i => smoothDirectionsProd (J i) (K i)
  have hQJ : UniformWeightedJointGrowth p W QJ base loss := hJ.prodMk hp hW hK
  let m : ℝ × ℝ → ℝ := fun z => z.1 * z.2
  have hm : ContDiff ℝ ∞ m := contDiff_fst.mul contDiff_snd
  have houter : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p (max base loss) x ≤ R → ∀ y ∈ V i,
        ‖contDiffOnJetFamily m univ k (f i (x, y), g i (x, y))‖ ≤ C * W i ^ Q := by
    intro R hR k
    obtain ⟨A, P₀, hA, hP₀, hzero⟩ := hQJ R hR 0
    obtain ⟨C, Q, hC, hQ, hb⟩ := norm_iteratedFDeriv_mul_on_polynomial_ball W hW
      (mul_nonneg hA (add_nonneg zero_le_one hR)) hP₀ k
    refine ⟨C, Q, hC, hQ, fun i x hx hlow y hy => ?_⟩
    have hvalue : ‖(f i (x, y), g i (x, y))‖ ≤ A * W i ^ P₀ * (1 + p loss x) := by
      have h := hzero i x hx ((hp (le_max_left _ _) x).trans hlow) y hy
        Fin.elim0 (fun j => Fin.elim0 j)
      simpa only [(QJ i).zero (x, y) ⟨hx, hy⟩, Nat.zero_add,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero] using h
    have hball : ‖(f i (x, y), g i (x, y))‖ ≤ (A * (1 + R)) * W i ^ P₀ := by
      exact hvalue.trans ((mul_le_mul_of_nonneg_left
        (add_le_add le_rfl ((hp (le_max_right _ _) x).trans hlow))
        (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))).trans_eq (by ring))
    change ‖iteratedFDerivWithin ℝ k m univ (f i (x, y), g i (x, y))‖ ≤ _
    rw [iteratedFDerivWithin_univ]
    exact hb i _ hball
  obtain ⟨B, L, hb, ho, h⟩ := hQJ.comp_contDiff hp hIp hW isOpen_univ hm.contDiffOn
    (fun _ _ _ => mem_univ _) (max base loss) houter
  exact ⟨B, L, hb, (le_max_right _ _).trans ho,
    h.congr H (fun _ _ _ => rfl)⟩

end ContinuousFlexibility.Analysis
