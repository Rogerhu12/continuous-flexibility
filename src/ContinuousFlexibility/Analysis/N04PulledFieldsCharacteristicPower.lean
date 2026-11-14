module

public import ContinuousFlexibility.Analysis.N04PulledFieldsTransportPowerGrowth
public import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBasePrefixRadius
public import ContinuousFlexibility.Analysis.WeightedJointMixedInterpolation

/-!
# Characteristic powers with one low grading before all orders

The genuine joint growth already controls a mixed jet at the sum of its
parameter and spatial orders. Fixed-base interpolation assigns the
parameter part to the finite prefix charge, preserving one low grading
for every parameter order and every spatial order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A full genuine joint-growth estimate supplies the transport power
prefix with a base chosen before the maximum parameter order. -/
theorem UniformWeightedJointGrowth.n04PulledFields_fixedBase_mixedPowerGrowth
    {p : ℕ → Seminorm ℝ E} {W : I → ℝ}
    {U : Set E} {V : I → Set PolarPoint} {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i)) :
    ∃ B : ℕ, base ≤ B ∧ ∀ K : ℕ, ∃ highLoss shift : ℕ,
      N04PulledFieldsMixedPowerGrowth p W (fun _ => 1) J K B highLoss shift := by
  obtain ⟨B, hB, hprefix⟩ := n04PulledFields_fixedBase_affine_prefix_power
    p hp hIp base (fun k => k + loss)
  refine ⟨B, hB, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  let highLoss : ℕ := B + shift * K + 1
  refine ⟨highLoss, shift, fun R hR N k hk a b hab => ?_⟩
  obtain ⟨Cj, P, hCj, hP, hj⟩ := hJ R hR (k + a + b)
  obtain ⟨Ci, hCi, hi⟩ := hshift R hR N
  refine ⟨Cj * Ci, P, mul_nonneg hCj (zero_le_one.trans hCi), hP,
    fun i x hx hxlow w hwlow y hy => ?_⟩
  let high : ℕ := k + a + b + loss
  have hxbase : p base x ≤ R := (hp hB x).trans hxlow
  have hwbase : p base w ≤ 1 := (hp hB w).trans hwlow
  have hjoint (v : Fin (k + a + b) → E × PolarPoint)
      (hv : ∀ j, p base (v j).1 + ‖(v j).2‖ ≤ 1) :
      |(J i).D (k + a + b) (x, y) v| ≤
        (Cj * W i ^ P) * ((1 + p high x) + ∑ j, p high (v j).1) := by
    simpa only [Real.norm_eq_abs] using hj i x hx hxbase y hy v hv
  have hm := (J i).mixedJet_unit_bound_of_jointJet (hV i) (hc i)
    (p base) (p high) k a b x hx y hy (Cj * W i ^ P) (1 + p high x)
    hjoint (fun _ => w) (fun _ => hwbase)
  let Q : ℝ := 1 + p (N + highLoss) x + p (N + highLoss) w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + highLoss)) x, apply_nonneg (p (N + highLoss)) w]
  have hindex : B + N + shift * K + 1 = N + highLoss := by
    dsimp only [highLoss]
    omega
  have hxQ : p (B + N + shift * K + 1) x ≤ Q := by
    rw [hindex]
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + highLoss)) w]
  have hwQ : p (B + N + shift * K + 1) w ≤ Q := by
    rw [hindex]
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + highLoss)) x]
  have horder : high = a + b + (k + loss) := by dsimp only [high]; omega
  have hscale : (1 + p high x) + (∑ _j : Fin k, p high w) ≤
      Ci * Q ^ (((a + b + shift * k : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
    simpa only [horder] using
      hi k hk (a + b) hab x hxlow (fun _ : Fin k => w) (fun _ => hwlow)
        Q hQ hxQ (fun _ => hwQ)
  have hcoef : 0 ≤ Cj * W i ^ P :=
    mul_nonneg hCj (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  exact hm.trans ((mul_le_mul_of_nonneg_left hscale hcoef).trans_eq (by
    dsimp only [Q]
    ring))

end ContinuousFlexibility.Analysis
