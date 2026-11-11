import ContinuousFlexibility.Radial.SeedCentralCutoff

/-!
# The central profile and second-mode solution with exact cone ends

The profile and height are normalized at radius one. They recover the
unscaled central model on the retained interval. Every critical point is
therefore an original simple turning point; the added parts are increasing.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem connectorHeight_const_shift (k : ℝ → ℝ) (y₀ κ₀ r : ℝ) :
    connectorHeight k y₀ κ₀ r = exp κ₀ * connectorHeight k y₀ 0 r := by
  simp only [connectorHeight, connectorLogHeight, zero_add, exp_add]

namespace SeedCentralCutoff

def profile (K : SeedCentralCutoff) : ℝ → ℝ :=
  connectorProfile K.slope 0 (log (centralRadialProfile 1 1))

def height (K : SeedCentralCutoff) : ℝ → ℝ :=
  connectorHeight K.slope 0 (log (centralKernelHeight 1))

theorem profile_pos (K : SeedCentralCutoff) {r : ℝ} (hr : 0 < r) :
    0 < K.profile r :=
  connectorProfile_pos _ _ _ hr

theorem height_pos (K : SeedCentralCutoff) (r : ℝ) :
    0 < K.height r :=
  connectorHeight_pos _ _ _ _

theorem profile_smooth (K : SeedCentralCutoff) :
    ContDiffOn ℝ ∞ K.profile (Ioi 0) :=
  connectorProfile_contDiffOn K.smooth K.below_four _ _

theorem height_smooth (K : SeedCentralCutoff) :
    ContDiffOn ℝ ∞ K.height (Ioi 0) :=
  connectorHeight_contDiffOn K.smooth _ _

theorem equation (K : SeedCentralCutoff) {r : ℝ} (hr : 0 < r) :
    radialJacobi 4 K.profile K.height r = 0 :=
  radialJacobi_connector K.smooth K.below_four _ _ _ hr

theorem profile_retained_log (K : SeedCentralCutoff) {y : ℝ}
    (hy : y ∈ Ioo K.left K.right) :
    K.profile (exp y) = centralRadialProfile 1 (exp y) := by
  have hw (t : ℝ) : ContDiffAt ℝ ∞ (centralRadialProfile 1) (exp t) :=
    (contDiffOn_centralRadialProfile 1).contDiffAt (Ioi_mem_nhds (exp_pos t))
  have hu (t : ℝ) : ContDiffAt ℝ ∞ centralKernelHeight (exp t) :=
    contDiffOn_centralKernelHeight.contDiffAt (Ioi_mem_nhds (exp_pos t))
  have hode (t : ℝ) :
      radialJacobi 4 (centralRadialProfile 1) centralKernelHeight (exp t) = 0 := by
    have h := radialJacobi_centralKernel 1 (centralModelCoordinate (exp t))
    rwa [centralRadius_modelCoordinate (exp_pos t)] at h
  have he := connectorProfile_reconstruct K.smooth K.below_four isOpen_Ioo
    (convex_Ioo K.left K.right).isPreconnected ⟨K.left_neg, K.right_pos⟩
    (fun t _ => (hw t).differentiableAt (by simp))
    (fun t _ => (hu t).differentiableAt (by simp))
    (fun t _ => ((hu t).derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
    (fun t _ => centralRadialProfile_pos (by norm_num) (exp_pos t))
    (fun t _ => (centralKernelHeight_pos _).ne')
    (fun t _ => hode t) (fun t ht => K.retained t ⟨ht.1.le, ht.2.le⟩) y hy
  simpa only [profile, exp_zero, sub_zero] using he

theorem height_retained_log (K : SeedCentralCutoff) {y : ℝ}
    (hy : y ∈ Ioo K.left K.right) :
    K.height (exp y) = centralKernelHeight (exp y) := by
  have he := connectorHeight_reconstruct K.smooth isOpen_Ioo
    (convex_Ioo K.left K.right).isPreconnected ⟨K.left_neg, K.right_pos⟩
    (fun t _ => (contDiffOn_centralKernelHeight.contDiffAt
      (Ioi_mem_nhds (exp_pos t))).differentiableAt (by simp))
    (fun t _ => (centralKernelHeight_pos _).ne')
    (fun t ht => K.retained t ⟨ht.1.le, ht.2.le⟩) y hy
  rw [height, connectorHeight_const_shift, exp_log (centralKernelHeight_pos 1)]
  simpa only [exp_zero] using he.symm

theorem profile_retained_germ (K : SeedCentralCutoff) {y : ℝ}
    (hy : y ∈ Ioo K.left K.right) :
    K.profile =ᶠ[𝓝 (exp y)] centralRadialProfile 1 :=
  eventuallyEq_of_eqOn_exp isOpen_Ioo hy (fun _ ht => K.profile_retained_log ht)

theorem height_retained_germ (K : SeedCentralCutoff) {y : ℝ}
    (hy : y ∈ Ioo K.left K.right) :
    K.height =ᶠ[𝓝 (exp y)] centralKernelHeight :=
  eventuallyEq_of_eqOn_exp isOpen_Ioo hy (fun _ ht => K.height_retained_log ht)

theorem profile_deriv_pos (K : SeedCentralCutoff) {r : ℝ} (hr : 0 < r)
    (hout : log r ≤ K.left ∨ K.right ≤ log r) :
    0 < deriv K.profile r := by
  have hratio : (3 / 4 : ℝ) ≤
      (K.slope (log r) ^ 2 - K.slope (log r) + deriv K.slope (log r)) /
        (4 - K.slope (log r)) := by
    rcases hout with h | h
    · exact K.positive_left _ h
    · exact K.positive_right _ h
  have hnum : 0 < K.slope (log r) ^ 2 - K.slope (log r) +
      deriv K.slope (log r) :=
    (div_pos_iff_of_pos_right (sub_pos.mpr (K.below_four _))).mp
      (lt_of_lt_of_le (by norm_num) hratio)
  exact deriv_connectorProfile_pos K.smooth K.below_four _ _ hr hnum

theorem profile_simple_critical (K : SeedCentralCutoff) {r : ℝ} (hr : 0 < r)
    (hzero : deriv K.profile r = 0) :
    deriv (deriv K.profile) r ≠ 0 := by
  by_cases hy : log r ∈ Ioo K.left K.right
  · have hg := K.profile_retained_germ hy
    rw [exp_log hr] at hg
    rw [hg.deriv.deriv_eq]
    apply centralRadialProfile_simple_turning (by norm_num) hr
    rw [← hg.deriv_eq]
    exact hzero
  · have hout : log r ≤ K.left ∨ K.right ≤ log r := by
      by_cases hl : K.left < log r
      · exact Or.inr (le_of_not_gt (fun hh => hy ⟨hl, hh⟩))
      · exact Or.inl (le_of_not_gt hl)
    have hp := K.profile_deriv_pos hr hout
    rw [hzero] at hp
    exact False.elim (lt_irrefl 0 hp)

theorem exact_cones (K : SeedCentralCutoff) :
    ∃ cL cR aL aR : ℝ, 0 < cL ∧ 0 < cR ∧ 0 < aL ∧ 0 < aR ∧
      (∀ r, 0 < r → log r < K.left - 1 →
        K.profile r = cL * r ∧ K.height r = aL * r ^ (2 : ℝ)) ∧
      (∀ r, 0 < r → K.right + 1 < log r →
        K.profile r = cR * r ∧ K.height r = aR * r ^ (-2 : ℝ)) := by
  let cL := exp (connectorLogProfile K.slope 0 (log (centralRadialProfile 1 1))
    (K.left - 2))
  let cR := exp (connectorLogProfile K.slope 0 (log (centralRadialProfile 1 1))
    (K.right + 2))
  let aL := exp (connectorLogHeight K.slope 0 (log (centralKernelHeight 1))
    (K.left - 2) - 2 * (K.left - 2))
  let aR := exp (connectorLogHeight K.slope 0 (log (centralKernelHeight 1))
    (K.right + 2) - (-2) * (K.right + 2))
  refine ⟨cL, cR, aL, aR, exp_pos _, exp_pos _, exp_pos _, exp_pos _, ?_, ?_⟩
  · intro r hr hlog
    constructor
    · let y₁ := min (log r) (K.left - 2) - 1
      exact connectorProfile_eq_cone_of_two K.smooth K.below_four
        (fun y hy => K.left_cone y hy.2.le) _ _
        ⟨by dsimp only [y₁]; linarith [min_le_right (log r) (K.left - 2)],
          by linarith⟩
        ⟨by dsimp only [y₁]; linarith [min_le_left (log r) (K.left - 2)], hlog⟩
    · exact connectorHeight_eq_power_of_const K.smooth isOpen_Iio
        (convex_Iio (K.left - 1)).isPreconnected
        (fun y hy => K.left_cone y hy.le) _ _ (by change K.left - 2 < K.left - 1; linarith)
        hr hlog
  · intro r hr hlog
    constructor
    · let y₂ := max (log r) (K.right + 2) + 1
      exact connectorProfile_eq_cone_of_neg_two K.smooth K.below_four
        (fun y hy => K.right_cone y hy.1.le) _ _
        ⟨by linarith, by dsimp only [y₂]; linarith [le_max_right (log r) (K.right + 2)]⟩
        ⟨hlog, by dsimp only [y₂]; linarith [le_max_left (log r) (K.right + 2)]⟩
    · exact connectorHeight_eq_power_of_const K.smooth isOpen_Ioi
        (convex_Ioi (K.right + 1)).isPreconnected
        (fun y hy => K.right_cone y hy.le) _ _ (by change K.right + 1 < K.right + 2; linarith)
        hr hlog

end SeedCentralCutoff
end ContinuousFlexibility.Radial
