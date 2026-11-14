module

public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseMixedGrowth
public import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
public import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficientJetSupport

/-!
# Physical mixed bounds from fixed strips and common zero germs

The joint strip towers and the global mixed towers differentiate the same
function. Uniqueness transfers the strip estimate before its positive
weight is moved to the physical point. Off the strips, a common spatial
zero germ makes every mixed parameter jet zero. The low base is selected
before all parameter orders, and each loss before the spatial order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A fixed strip-or-zero cover transfers strong mixed growth to any
genuine mixed tower on the full physical domain. -/
theorem n04PulledFields_mixedPhysical_of_strips_or_zero
    {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) {U : Set E} {Ω : Set PolarPoint}
    (hU : IsOpen U) (V : I → Set PolarPoint) (hV : ∀ i, IsOpen (V i))
    (hc : ∀ i, Convex ℝ (U ×ˢ V i))
    (W F : I → ℝ) (hW : ∀ i, 1 ≤ W i) (hF : ∀ i, 0 ≤ F i)
    (Ephys Hphys : PolarPoint → ℝ)
    (hE : ∀ y ∈ Ω, 0 ≤ Ephys y) (hH : ∀ y ∈ Ω, 0 ≤ Hphys y)
    (hcost : ∀ Q : ℝ, 0 ≤ Q → ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧
      ∀ i y, y ∈ V i → F i * W i ^ Q ≤ K * Ephys y ^ A * Hphys y)
    {f : E → PolarPoint → ℝ}
    (RF : MixedJetRegularity U Ω f)
    (J : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => f z.1 z.2))
    (hcover : ∀ y ∈ Ω, (∃ i, y ∈ V i) ∨
      ∀ x ∈ U, f x =ᶠ[𝓝 y] fun _ => 0)
    (hg : N04PulledFieldsFixedBaseMixedGrowth p W F J) :
    ∃ B : ℕ, ∀ n : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ C Q : ℝ,
      0 ≤ C ∧ 0 ≤ Q ∧ ∀ x, x ∈ U → p B x ≤ 1 →
      ∀ y (hy : y ∈ Ω), ∀ a b : ℕ, a + b ≤ s → ∀ v : Fin n → E,
        |(RF.parameter a b y hy).D n x v| ≤
          C * Ephys y ^ Q * Hphys y * oneHighVariationWeight p B (s + L) x v := by
  obtain ⟨B, hB⟩ := hg
  refine ⟨B, fun n => ?_⟩
  obtain ⟨L, hL⟩ := hB n
  refine ⟨L, fun s => ?_⟩
  obtain ⟨C, P, hC, hP, hb⟩ := hL.mixed_oneHigh hW hF hV hc 1 zero_le_one s
  obtain ⟨K, A, hK, hA, htransfer⟩ := hcost P hP
  refine ⟨C * K, A, mul_nonneg hC hK, hA, fun x hx hxB y hy a b hab v => ?_⟩
  have hweight : 0 ≤ oneHighVariationWeight p B (s + L) x v :=
    oneHighVariationWeight_nonneg _ _ _ _ _
  rcases hcover y hy with ⟨i, hi⟩ | hz
  · have hjet := n04Realization_mixedParameter_eq_joint (J i) hU (hV i) (hc i)
      a b n x hx y hi (RF.parameter a b y hy) v
    rw [hjet]
    calc
      _ ≤ C * F i * W i ^ P * oneHighVariationWeight p B (s + L) x v :=
        hb i x hx hxB y hi v a b hab
      _ = C * (F i * W i ^ P) * oneHighVariationWeight p B (s + L) x v := by ring
      _ ≤ C * (K * Ephys y ^ A * Hphys y) *
          oneHighVariationWeight p B (s + L) x v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (htransfer i y hi) hC) hweight
      _ = _ := by ring
  · have hzero : EqOn (fun z => mixedDerivative a b (f z) y) (fun _ => 0) U := by
      intro z hzU
      exact (mixedDerivative_congr_of_eventuallyEq (hz z hzU) a b).trans
        (by simp only [mixedDerivative, iteratedDeriv_const, ite_self])
    rw [(RF.parameter a b y hy).jets_zero_of_eqOn_zero hzero n x hx v, abs_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC hK) (Real.rpow_nonneg (hE y hy) A))
        (hH y hy)) hweight

end ContinuousFlexibility.Analysis
