module

public import ContinuousFlexibility.Analysis.CircleUniformAngularInterpolation
public import ContinuousFlexibility.Analysis.JointMixedTameBounds
public import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus

/-!
# One interpolation scale for actual mixed characteristic jets

At a fixed maximum parameter order, the joint tame loss and all parameter
orders are absorbed in one low order. Spatial restriction inserts only
the two fixed unit directions. Interpolation therefore charges exactly
the total spatial order, while retaining the component weight power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The mixed diagonal jet of the supplied genuine tower has a common
power-growth scale. The low order is fixed before the radius and the
total spatial order; constants and geometric powers precede the label
and all evaluation variables. -/
theorem UniformWeightedJointGrowth.mixed_diagonal_spatial_interpolation
    {p : ℕ → Seminorm ℝ E} {W : I → ℝ}
    {U : Set E} {V : I → Set PolarPoint} {f : I → E × PolarPoint → ℝ}
    {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    (hV : ∀ i, IsOpen (V i)) (hc : ∀ i, Convex ℝ (U ×ˢ V i)) (nmax : ℕ) :
    ∃ B : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ N k : ℕ, k ≤ nmax → ∀ a b : ℕ, a + b ≤ N →
      ∃ C P : ℝ, 0 ≤ C ∧ 0 ≤ P ∧
        ∀ i x, x ∈ U → ∀ w : E, p B x ≤ R → p B w ≤ 1 →
        ∀ y ∈ V i,
        |jointMixedDiagonal (J i) k a b x w y| ≤
          C * W i ^ P *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              (((a + b : ℕ) : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨B, hB, hinterp⟩ :=
    hasInterpolation_spatial_affine_rpow_bound p hp hIp base (nmax + loss)
  refine ⟨B, hB, fun R hR N k hk a b hab => ?_⟩
  obtain ⟨Cj, P, hCj, hP, hj⟩ := hJ R hR (k + a + b)
  obtain ⟨Ci, hCi, hi⟩ := hinterp R hR N (a + b) hab k
  refine ⟨Cj * Ci, P, mul_nonneg hCj hCi, hP,
    fun i x hx w hxlow hwlow y hy => ?_⟩
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
  have hindex : high ≤ a + b + (nmax + loss) := by dsimp only [high]; omega
  have horder : 1 + p high x + ∑ _j : Fin k, p high w ≤
      1 + p (a + b + (nmax + loss)) x +
        ∑ _j : Fin k, p (a + b + (nmax + loss)) w :=
    add_le_add (add_le_add le_rfl (hp hindex x))
      (Finset.sum_le_sum (fun _ _ => hp hindex w))
  let Q : ℝ := 1 + p (N + B + 1) x + p (N + B + 1) w
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) x,
      apply_nonneg (p (N + B + 1)) w]
  have hxQ : p (N + B + 1) x ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) w]
  have hwQ : p (N + B + 1) w ≤ Q := by
    dsimp only [Q]
    linarith only [apply_nonneg (p (N + B + 1)) x]
  have hscale := hi x (fun _ : Fin k => w) Q hxlow (fun _ => hwlow)
    hxQ (fun _ => hwQ) hQ
  have hcoef : 0 ≤ Cj * W i ^ P :=
    mul_nonneg hCj (Real.rpow_nonneg (zero_le_one.trans (hW i)) _)
  exact (hm.trans (mul_le_mul_of_nonneg_left horder hcoef)).trans
    ((mul_le_mul_of_nonneg_left hscale hcoef).trans_eq (by dsimp only [Q]; ring))

end ContinuousFlexibility.Analysis
