module

public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Abel

/-!
# Taylor and Newton estimates in a projective grading

The second directional jet bounds the Taylor remainder on an actual closed
segment. Applying this estimate to the quadratic right-inverse identity gives
the residual bound after a Newton step. For a smoothed step the remaining
first-order term is exactly the derivative applied to the smoothing error.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem projectiveLineDerivAt_along_affine
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    {f : V → W} {df : W} {x d : V} {t : ℝ}
    (hf : HasProjectiveLineDerivAt f df (x + t • d) d) :
    HasProjectiveCurveDerivAt (fun s : ℝ => f (x + s • d)) df t := by
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    zero_add, zero_smul, add_zero, add_smul, add_assoc] using hf

private theorem norm_curve_quadratic_remainder_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f f₁ f₂ : ℝ → W} {M : ℝ}
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖f₂ t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖f t - f 0 - t • f₁ 0‖ ≤ M / 2 * t ^ 2 := by
  have hg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖f₁ s - f₁ 0‖ ≤ M * s := by
    simpa only [sub_zero] using
      norm_image_sub_le_of_norm_deriv_le_segment'
        (fun u hu => (h₂ u hu).hasDerivWithinAt)
        (fun u hu => hM u (Ico_subset_Icc_self hu)) s hs
  let r : ℝ → W := fun s => f s - f 0 - s • f₁ 0
  have hr (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt r (f₁ s - f₁ 0) s := by
    have hline : HasDerivAt (fun u : ℝ => u • f₁ 0) (f₁ 0) s := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const (f₁ 0)
    exact ((h₁ s hs).sub_const (f 0)).sub hline
  have hB (s : ℝ) : HasDerivAt (fun u : ℝ => M / 2 * u ^ 2) (M * s) s := by
    have hd : HasDerivAt (fun u : ℝ => M / 2 * (u * u)) (M / 2 * (s + s)) s := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
        ((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul (M / 2)
    have hcoef : M / 2 * (s + s) = M * s := by ring
    simpa only [pow_two, hcoef] using hd
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := (0 : ℝ)) (b := 1) (f := r) (f' := fun s => f₁ s - f₁ 0)
    (B := fun s => M / 2 * s ^ 2) (B' := fun s => M * s)
    (fun s hs => (hr s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hr s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [r]) hB (fun s hs => hg s (Ico_subset_Icc_self hs)) ht

private theorem seminorm_newton_cancel_le
    {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (p : Seminorm ℝ Y) (D : X →ₗ[ℝ] Y) (d v : X) (r rnext q : Y) {M : ℝ}
    (hD : D v = r + q) (hT : p (rnext - r - D d) ≤ M) :
    p rnext ≤ p q + p (D (d + v)) + M := by
  let T := rnext - r - D d
  have hres : rnext = T + D (d + v) - q := by
    rw [map_add D d v, hD]
    dsimp only [T]
    abel
  calc
    p rnext = p (T + D (d + v) - q) := congrArg (fun y => p y) hres
    _ ≤ p (T + D (d + v)) + p q := map_sub_le_add p _ _
    _ ≤ p T + p (D (d + v)) + p q := add_le_add (map_add_le_add p T (D (d + v))) (le_refl (p q))
    _ = p q + p (D (d + v)) + p T := by ring
    _ ≤ p q + p (D (d + v)) + M := add_le_add_right (show p T ≤ M from hT) _

section ProjectiveTarget

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
variable {bond : ∀ n, F (n + 1) →L[ℝ] F n}
variable {f : V → ProjectiveLimit F bond} {J : ProjectiveJetFamily V (ProjectiveLimit F bond)}
variable {U : Set V}

/-- A uniform bound for the true second jet along a closed segment gives the
quadratic remainder estimate in the actual finite-maximum grading. -/
theorem projectiveTaylorRemainder_le
    (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U) {x d : V}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U) (s : ℕ) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, gradedSeminorm F bond s
      (J 2 (x + t • d) (Fin.cons d (Fin.cons d Fin.elim0))) ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    gradedSeminorm F bond s
      (f (x + t • d) - f x - t • projectiveJetHeadLinear J 0 x Fin.elim0 d) ≤ M / 2 * t ^ 2 := by
  have hM₀ : 0 ≤ M :=
    (apply_nonneg (gradedSeminorm F bond s) _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hnonneg : 0 ≤ M / 2 * t ^ 2 := mul_nonneg (div_nonneg hM₀ (by norm_num)) (sq_nonneg t)
  apply (gradedSeminorm_le_iff F bond s _ hnonneg).mpr
  intro i hi
  let g₀ : ℝ → F i := fun u => (f (x + u • d)).1 i
  let g₁ : ℝ → F i := fun u => (projectiveFirstJetValue J (x + u • d) d).1 i
  let g₂ : ℝ → F i := fun u => (J 2 (x + u • d) (Fin.cons d (Fin.cons d Fin.elim0))).1 i
  have hd₁ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : HasDerivAt g₀ (g₁ u) u :=
    (hasProjectiveCurveDerivAt_iff_levels _ _ _).mp
      (projectiveLineDerivAt_along_affine (hJ.hasLineDerivAt hU (hseg u hu) d)) i
  have hd₂ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : HasDerivAt g₁ (g₂ u) u :=
    (hasProjectiveCurveDerivAt_iff_levels _ _ _).mp
      (projectiveLineDerivAt_along_affine
        (hJ.2.2 1 (x + u • d) (hseg u hu) d (Fin.cons d Fin.elim0))) i
  have hg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖g₂ u‖ ≤ M :=
    (norm_coordinate_le_graded F bond hi _).trans (hM u hu)
  change ‖(f (x + t • d)).1 i - (f x).1 i -
    t • (projectiveJetHeadLinear J 0 x Fin.elim0 d).1 i‖ ≤ M / 2 * t ^ 2
  simpa only [g₀, g₁, projectiveFirstJetValue, projectiveJetHeadLinear_apply,
    zero_smul, add_zero] using norm_curve_quadratic_remainder_le hd₁ hd₂ hg ht

set_option maxHeartbeats 500000 in
/-- The actual quadratic right-inverse identity cancels the first-order
Newton term. An arbitrary chosen increment contributes its exact derivative
defect, so this estimate also applies after smoothing the increment. -/
theorem projectiveNewtonStep_residual_le
    (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U) {x d : V}
    (V₀ : ProjectiveLimit F bond →ₗ[ℝ] V)
    (Q : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt f (y + Q (f x) y) x (V₀ y))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U) (s : ℕ) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, gradedSeminorm F bond s
      (J 2 (x + t • d) (Fin.cons d (Fin.cons d Fin.elim0))) ≤ M) :
    gradedSeminorm F bond s (f (x + d)) ≤ gradedSeminorm F bond s (Q (f x) (f x)) +
      gradedSeminorm F bond s (projectiveJetHeadLinear J 0 x Fin.elim0 (d + V₀ (f x))) + M / 2 := by
  let D := projectiveJetHeadLinear J 0 x Fin.elim0
  have hx : x ∈ U := by
    simpa only [zero_smul, add_zero] using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hD : D (V₀ (f x)) = f x + Q (f x) (f x) := by
    simpa only [D, projectiveJetHeadLinear_apply, projectiveFirstJetValue] using
      (hJ.hasLineDerivAt hU hx (V₀ (f x))).unique (hV (f x))
  have hT : gradedSeminorm F bond s (f (x + d) - f x - D d) ≤ M / 2 := by
    simpa only [D, one_smul, one_pow, mul_one] using
      projectiveTaylorRemainder_le hU hJ hseg s hM (t := 1) ⟨zero_le_one, le_rfl⟩
  exact seminorm_newton_cancel_le (gradedSeminorm F bond s) D.toLinearMap
    d (V₀ (f x)) (f x) (f (x + d)) (Q (f x) (f x)) hD hT

end ProjectiveTarget

/-- A smoothed Newton update changes the state at a fixed real parameter.
The derivative defect is the original correction minus its smoothing, with
zero parameter component. -/
theorem projectiveSmoothedNewtonStep_residual_le
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    {f : X × ℝ → ProjectiveLimit F bond} {J : ProjectiveJetFamily (X × ℝ) (ProjectiveLimit F bond)}
    {U : Set (X × ℝ)} (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U) (z : X × ℝ)
    (V₀ : ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt (fun x => f (x, z.2))
      (y + Q (f z) y) z.1 (V₀ y))
    (S : X →L[ℝ] X) (s : ℕ) {M : ℝ} :
    let d : X × ℝ := (-S (V₀ (f z)), 0)
    (∀ t ∈ Icc (0 : ℝ) 1, z + t • d ∈ U) →
    (∀ t ∈ Icc (0 : ℝ) 1, gradedSeminorm F bond s
      (J 2 (z + t • d) (Fin.cons d (Fin.cons d Fin.elim0))) ≤ M) →
    gradedSeminorm F bond s (f (z.1 - S (V₀ (f z)), z.2)) ≤
      gradedSeminorm F bond s (Q (f z) (f z)) + gradedSeminorm F bond s
        (projectiveJetHeadLinear J 0 z Fin.elim0 (V₀ (f z) - S (V₀ (f z)), 0)) + M / 2 := by
  dsimp only
  intro hseg hM
  let d : X × ℝ := (-S (V₀ (f z)), 0)
  let V₁ : ProjectiveLimit F bond →ₗ[ℝ] X × ℝ := V₀.prod 0
  have hV₁ (y : ProjectiveLimit F bond) :
      HasProjectiveLineDerivAt f (y + Q (f z) y) z (V₁ y) := by
    have he : (fun t : ℝ => f (z + t • V₁ y)) =
        (fun t : ℝ => f (z.1 + t • V₀ y, z.2)) := by
      funext t
      change f (z.1 + t • V₀ y, z.2 + t • (0 : ℝ)) = _
      rw [smul_zero, add_zero]
    unfold HasProjectiveLineDerivAt
    rw [he]
    exact hV y
  have h := projectiveNewtonStep_residual_le hU hJ (x := z) (d := d) V₁ Q hV₁ hseg s hM
  have hz : z + d = (z.1 - S (V₀ (f z)), z.2) := by
    apply Prod.ext
    · exact (sub_eq_add_neg _ _).symm
    · exact add_zero _
  have hd : d + V₁ (f z) = (V₀ (f z) - S (V₀ (f z)), 0) := by
    apply Prod.ext
    · change -S (V₀ (f z)) + V₀ (f z) = V₀ (f z) - S (V₀ (f z))
      rw [sub_eq_add_neg, add_comm]
    · change (0 : ℝ) + 0 = 0
      exact add_zero _
  rw [hz, hd] at h
  exact h

end ContinuousFlexibility.Analysis
