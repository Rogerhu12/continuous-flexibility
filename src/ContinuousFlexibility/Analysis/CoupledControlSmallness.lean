module

public import ContinuousFlexibility.Analysis.TameJetLocalBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform smallness of a vanishing parameter family

Joint continuity of a linear family gives a locally uniform fiber norm
bound. Applying this to the actual parameter derivative and using the
mean-value inequality makes a family vanishing at parameter zero uniformly
small. This supplies the Banach-space step in the second Neumann inverse;
no continuity in an operator-norm topology is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

section FiberBound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem coupled_linear_bound_of_ball
    (L : E →ₗ[ℝ] F) {δ : ℝ} (hδ : 0 < δ)
    (hL : ∀ u, ‖u‖ < δ → ‖L u‖ < 1) (u : E) :
    ‖L u‖ ≤ (2 / δ) * ‖u‖ := by
  by_cases hu : u = 0
  · simp only [hu, map_zero, norm_zero, mul_zero, le_refl]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let a : ℝ := δ / (2 * ‖u‖)
  have ha : 0 < a := div_pos hδ (mul_pos (by norm_num) hnorm)
  have hscaled : ‖a • u‖ = δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp only [a]
    field_simp [hnorm.ne'] <;> ring
  have hsmall := hL (a • u) (hscaled.trans_lt (by linarith only [hδ]))
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hsmall
  have hcancel : a * ((2 / δ) * ‖u‖) = 1 := by
    dsimp only [a]
    field_simp [hδ.ne', hnorm.ne'] <;> ring
  exact le_of_mul_le_mul_left (hsmall.le.trans hcancel.symm.le) ha

/-- Joint continuity at the zero fiber bounds all nearby fiber operators. -/
theorem coupled_exists_uniform_fiber_bound
    {Z : Type*} [TopologicalSpace Z] (L : Z → E →L[ℝ] F) {z0 : Z}
    (hL : ContinuousAt (fun z : Z × E => L z.1 z.2) (z0, 0)) :
    ∃ W : Set Z, W ∈ 𝓝 z0 ∧ ∃ K : ℝ, 0 < K ∧ ∀ z ∈ W, ‖L z‖ ≤ K := by
  have hsmall : {z : Z × E | ‖L z.1 z.2‖ < 1} ∈ 𝓝 (z0, 0) :=
    hL.norm.preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨W, hW, V, hV, hWV⟩ := mem_nhds_prod_iff.mp hsmall
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨W, hW, 2 / δ, div_pos (by norm_num) hδ, ?_⟩
  intro z hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  apply coupled_linear_bound_of_ball (L z).toLinearMap hδ
  intro u hu
  exact hWV (show (z, u) ∈ W ×ˢ V from
    ⟨hz, hball (by simpa only [Metric.mem_ball, dist_zero_right] using hu)⟩)

end FiberBound

section Parameter

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform bound for the true parameter derivative controls the fiber
norm by the absolute parameter on the same strip. -/
theorem coupled_parameter_family_norm_le
    (A D : X × ℝ → E →L[ℝ] F) {W : Set X} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hzero : ∀ x ∈ W, ∀ u, A (x, 0) u = 0)
    (hderiv : ∀ x ∈ W, ∀ t, |t| < δ → ∀ u,
      HasDerivAt (fun q : ℝ => A (x, q) u) (D (x, t) u) t)
    (hbound : ∀ x ∈ W, ∀ t, |t| < δ → ‖D (x, t)‖ ≤ K)
    {x : X} (hx : x ∈ W) {q : ℝ} (hq : |q| < δ) :
    ‖A (x, q)‖ ≤ K * |q| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (abs_nonneg q))
  intro u
  have hdiff (t : ℝ) (ht : t ∈ Ioo (-δ) δ) := hderiv x hx t (abs_lt.mpr ht) u
  have hd (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      ‖deriv (fun s : ℝ => A (x, s) u) t‖ ≤ K * ‖u‖ := by
    rw [(hdiff t ht).deriv]
    exact ((D (x, t)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hbound x hx t (abs_lt.mpr ht)) (norm_nonneg u))
  have hline := (convex_Ioo (-δ) δ).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hdiff t ht).differentiableAt) hd
    (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨neg_lt_zero.mpr hδ, hδ⟩) (abs_lt.mp hq)
  rw [hzero x hx u, sub_zero, sub_zero, Real.norm_eq_abs] at hline
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hline

/-- A jointly continuous parameter derivative gives one neighborhood and
one positive parameter radius for an operator norm strictly below `1/4`. -/
theorem coupled_exists_small_parameter_family
    (A D : X × ℝ → E →L[ℝ] F) {U : Set (X × ℝ)} {x0 : X}
    (hU : IsOpen U) (hx0 : (x0, 0) ∈ U)
    (hzero : ∀ x, (x, 0) ∈ U → ∀ u, A (x, 0) u = 0)
    (hderiv : ∀ z ∈ U, ∀ u,
      HasDerivAt (fun q : ℝ => A (z.1, q) u) (D z u) z.2)
    (hD : ContinuousAt (fun z : (X × ℝ) × E => D z.1 z.2) ((x0, 0), 0)) :
    ∃ W : Set X, W ∈ 𝓝 x0 ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ W, ∀ q : ℝ, |q| < δ → (x, q) ∈ U ∧ ‖A (x, q)‖ < (1 / 4 : ℝ) := by
  obtain ⟨V, hV, K, hK, hbound⟩ := coupled_exists_uniform_fiber_bound D hD
  obtain ⟨W, hW, I, hI, hWI⟩ :=
    mem_nhds_prod_iff.mp (inter_mem hV (hU.mem_nhds hx0))
  obtain ⟨δ0, hδ0, hδI⟩ := Metric.mem_nhds_iff.mp hI
  have hstrip (x : X) (hx : x ∈ W) (q : ℝ) (hq : |q| < δ0) :
      (x, q) ∈ V ∩ U :=
    hWI ⟨hx, hδI (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hq)⟩
  let δ : ℝ := min δ0 (1 / (4 * (K + 1)))
  have hδ : 0 < δ := lt_min hδ0 (by positivity)
  refine ⟨W, hW, δ, hδ, ?_⟩
  intro x hx q hq
  have hq0 : |q| < δ0 := hq.trans_le (min_le_left _ _)
  refine ⟨(hstrip x hx q hq0).2, ?_⟩
  have hnorm := coupled_parameter_family_norm_le A D hδ0 hK.le
    (fun x hx u => hzero x (hstrip x hx 0 (by simpa using hδ0)).2 u)
    (fun x hx t ht u => hderiv (x, t) (hstrip x hx t ht).2 u)
    (fun x hx t ht => hbound (x, t) (hstrip x hx t ht).1) hx hq0
  have hqsmall : |q| < 1 / (4 * (K + 1)) := hq.trans_le (min_le_right _ _)
  have hscaled : (4 * (K + 1)) * |q| < 1 := by
    have hdpos : 0 < 4 * (K + 1) := by positivity
    simpa only [mul_comm] using (lt_div_iff₀ hdpos).mp hqsmall
  have hquarter : K * |q| < (1 / 4 : ℝ) := by
    nlinarith only [hscaled, abs_nonneg q]
  exact hnorm.trans_lt hquarter

end Parameter

end ContinuousFlexibility.Analysis
