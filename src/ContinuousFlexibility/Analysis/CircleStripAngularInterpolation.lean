import ContinuousFlexibility.Analysis.JointMixedCircleEvaluation
import ContinuousFlexibility.Analysis.CircleUniformAngularInterpolation
import ContinuousFlexibility.Analysis.TameUniformSmoothFamily

/-!
# Uniform angular estimates on the actual spatial strips

A family of radius selectors covers every point of every strip.  The
constants for the circle family are selected before the selector, so
identification with the genuine spatial tower gives constants uniform
in the physical radius as well as the component and the angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {I E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {H : CircleModelData}
  {U : Set E} {p : ℕ → Seminorm ℝ E}

/-- Every pure angular jet of the actual spatial family is controlled
by the same selector-independent circle estimate. -/
theorem UniformSmoothFamilyOn.realized_strip_angular_interpolation
    {g : I → E → H.Space} (hg : UniformSmoothFamilyOn p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m))
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      f m (x, (rsel i m, θ)) = H.decode (g i x) m θ)
    (nmax : ℕ) :
    ∃ B : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          C * T.H (T.sample m) ^ γ *
            (1 + p (N + B + 1) x + p (N + B + 1) w) ^
              ((b : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨K, hK⟩ := hg
  obtain ⟨B, hb⟩ := hK.circle_diagonal_angular_interpolation hp hIp hH hpos nmax
  refine ⟨B, fun R hR N n hn b hbN => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR N n hn b hbN
  refine ⟨C, hC, fun m x hx w hxlow hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy
  have hid := jointMixedDiagonal_eq_circleAngularJet (J m) hH (K i) m hr
    (heq i m hr) n b x w hx y.2
  have hpoint := hc i x hx w hxlow hwlow m y.2
  have hyeta : (rsel i m, y.2) = y := by rw [hi]
  rw [hyeta] at hid
  exact (congrArg abs hid).trans_le hpoint

/-- A fixed affine offset and a bounded sample-height factor can be
absorbed into the numerical constant. This applies to the old-flow
slope, whose circle decoder represents its deviation from one. -/
theorem UniformSmoothFamilyOn.realized_strip_angular_interpolation_add_const
    {g : I → E → H.Space} (hg : UniformSmoothFamilyOn p H.grading U g)
    (hp : Monotone p) (hIp : HasInterpolation p) (hH : IsCircleModel T γ H)
    (hpos : ∀ m, 0 < T.H (T.sample m)) (KH : ℝ) (hKH : 0 ≤ KH)
    (hheight : ∀ m, T.H (T.sample m) ^ γ ≤ KH)
    (l h : ℕ → ℝ) (rsel : I → ℕ → ℝ)
    (hcover : ∀ m r, r ∈ Ioo (l m) (h m) → ∃ i, rsel i m = r)
    {f : ℕ → E × PolarPoint → ℝ}
    (J : ∀ m, SmoothDirections (U ×ˢ (Ioo (l m) (h m) ×ˢ univ)) (f m))
    (c : ℝ)
    (heq : ∀ i m, rsel i m ∈ Ioo (l m) (h m) → ∀ x ∈ U, ∀ θ,
      f m (x, (rsel i m, θ)) = c + H.decode (g i x) m θ)
    (nmax : ℕ) :
    ∃ B : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ N n : ℕ, n ≤ nmax → ∀ b : ℕ, b ≤ N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m x, x ∈ U → ∀ w : E,
        p B x ≤ R → p B w ≤ 1 → ∀ y : PolarPoint, y.1 ∈ Ioo (l m) (h m) →
        |jointMixedDiagonal (J m) n 0 b x w y| ≤
          C * (1 + p (N + B + 1) x + p (N + B + 1) w) ^
            ((b : ℝ) / ((N : ℝ) + 1)) := by
  obtain ⟨K, hK⟩ := hg
  obtain ⟨B, hb⟩ := hK.circle_diagonal_angular_interpolation hp hIp hH hpos nmax
  refine ⟨B, fun R hR N n hn b hbN => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb R hR N n hn b hbN
  refine ⟨|c| + C * KH, add_nonneg (abs_nonneg _) (mul_nonneg hC hKH),
    fun m x hx w hxlow hwlow y hy => ?_⟩
  obtain ⟨i, hi⟩ := hcover m y.1 hy
  have hr : rsel i m ∈ Ioo (l m) (h m) := hi.symm ▸ hy
  have hid := jointMixedDiagonal_eq_circleAngularJet_add_const (J m) hH (K i) m hr c
    (heq i m hr) n b x w hx y.2
  have hyeta : (rsel i m, y.2) = y := by rw [hi]
  rw [hyeta] at hid
  let q := (1 + p (N + B + 1) x + p (N + B + 1) w) ^
    ((b : ℝ) / ((N : ℝ) + 1))
  have hq : 1 ≤ q := by
    apply Real.one_le_rpow
    · linarith only [apply_nonneg (p (N + B + 1)) x,
        apply_nonneg (p (N + B + 1)) w]
    · positivity
  have hc0 : |(if n = 0 ∧ b = 0 then c else 0)| ≤ |c| := by
    split_ifs <;> simp only [abs_zero, abs_nonneg, le_refl]
  have hbnd := hc i x hx w hxlow hwlow m y.2
  calc
    _ ≤ |(if n = 0 ∧ b = 0 then c else 0)| +
        |iteratedDeriv b (H.decode ((K i).D n x (fun _ => w)) m) y.2| := by
          rw [hid]
          exact abs_add_le _ _
    _ ≤ |c| * q + (C * KH) * q := add_le_add
      (hc0.trans (by nlinarith only [hq, abs_nonneg c]))
      (hbnd.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hheight m) hC) (zero_le_one.trans hq)))
    _ = _ := by dsimp only [q]; ring

/-- Enlarging the low order enlarges the common high scale by the same
amount. This allows independently constructed primitive families to
share one scale before the radial induction. -/
theorem common_spatial_scale_mono
    (hp : Monotone p) {B B' N d : ℕ} (hB : B ≤ B')
    (x w : E) :
    (1 + p (N + B + 1) x + p (N + B + 1) w) ^
        ((d : ℝ) / ((N : ℝ) + 1)) ≤
      (1 + p (N + B' + 1) x + p (N + B' + 1) w) ^
        ((d : ℝ) / ((N : ℝ) + 1)) := by
  have hindex : N + B + 1 ≤ N + B' + 1 := by omega
  apply Real.rpow_le_rpow
  · positivity
  · exact add_le_add (add_le_add le_rfl (hp hindex x)) (hp hindex w)
  · positivity

end ContinuousFlexibility.Analysis
