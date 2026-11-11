import ContinuousFlexibility.Analysis.SeeleyPeriodicJetBounds
import ContinuousFlexibility.Analysis.BoundaryTaylorExtension

/-!
# A fixed joint smooth extension of periodic half-plane fields

A fixed radial cutoff supplies all uniform jet bounds needed for the
reflection series. It is used only on the reflected negative side:
the final function equals the original field on the entire closed
half-plane. Near the boundary the cutoff is one, so the two definitions
have the same smooth neighborhood germ. The operator and coefficients
are independent of every derivative order and of the angular period.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private def seeleyCutoffField (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  boundaryTaylorCutoff p.1 * f p

/-- The reflection formula preserves angular periodicity even when that
periodicity is given only on the original half-plane. -/
theorem seeleyCylinderExtend_periodic_of_halfPlane
    {ι : Type*} (S : SeeleyData ι) {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T) (r : ℝ) :
    Function.Periodic (fun θ => seeleyCylinderExtend S f (r, θ)) T := by
  intro θ
  change seeleyCylinderExtend S f (r, θ + T) = seeleyCylinderExtend S f (r, θ)
  by_cases hr : 0 ≤ r
  · rw [seeleyCylinderExtend_of_nonneg S f (p := (r, θ + T)) hr,
      seeleyCylinderExtend_of_nonneg S f (p := (r, θ)) hr]
    exact hperiod r hr θ
  · dsimp only [seeleyCylinderExtend]
    simp only [seeleyExtend, if_neg hr, seeleyReflection]
    apply tsum_congr
    intro i
    have hp : f (-S.b i * r, θ + T) = f (-S.b i * r, θ) :=
      hperiod (-S.b i * r)
        (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (S.b_nonneg i))
          (lt_of_not_ge hr).le) θ
    exact congrArg (fun u : ℝ => (S.a i * (-S.b i) ^ 0) • u) hp

private theorem seeleyCutoffField_periodic
    {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (r : ℝ) (hr : 0 ≤ r) :
    Function.Periodic (fun θ => seeleyCutoffField f (r, θ)) T := by
  intro θ
  change boundaryTaylorCutoff r * f (r, θ + T) = boundaryTaylorCutoff r * f (r, θ)
  have hp : f (r, θ + T) = f (r, θ) := hperiod r hr θ
  exact congrArg (fun u : ℝ => boundaryTaylorCutoff r * u) hp

private theorem contDiff_seeleyCutoffExtension
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T) :
    ContDiff ℝ ∞ (seeleyCylinderExtend seeleyData (seeleyCutoffField f)) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => boundaryTaylorCutoff p.1) :=
    boundaryTaylorCutoff.contDiff.comp contDiff_fst
  have hg : ContDiffOn ℝ ∞ (seeleyCutoffField f) seeleyHalfPlane :=
    hc.contDiffOn.mul hf
  have hz : ∀ p, (1 : ℝ) < p.1 → seeleyCutoffField f p = 0 := by
    intro p hp
    have hd : boundaryTaylorCutoff.rOut ≤ dist p.1 0 := by
      change (1 / 3 : ℝ) ≤ dist p.1 0
      rw [Real.dist_eq, sub_zero]
      exact (by norm_num : (1 / 3 : ℝ) ≤ 1).trans (hp.le.trans (le_abs_self _))
    change boundaryTaylorCutoff p.1 * f p = 0
    rw [boundaryTaylorCutoff.zero_of_le_dist hd, zero_mul]
  exact contDiff_seeleyCylinderExtend_of_contDiffOn seeleyData hg
    (seeleyWithinMixedJet_bounded_of_periodic_of_zero_after hg hT
      (seeleyCutoffField_periodic hperiod) hz)

/-- The same operator preserves the entire original half-plane and uses
the cutoff reflection only on the other side of the boundary. -/
def seeleyPeriodicExtension (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.1 then f p else seeleyCylinderExtend seeleyData (seeleyCutoffField f) p

@[simp] theorem seeleyPeriodicExtension_of_nonneg
    (f : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    seeleyPeriodicExtension f p = f p := by
  simp only [seeleyPeriodicExtension, if_pos hp]

private theorem seeleyPeriodicExtension_boundary_germ
    (f : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hp : p.1 = 0) :
    seeleyPeriodicExtension f =ᶠ[𝓝 p]
      seeleyCylinderExtend seeleyData (seeleyCutoffField f) := by
  have hlim : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝 p) (𝓝 0) := by
    simpa only [hp] using continuous_fst.tendsto p
  filter_upwards [boundaryTaylorCutoff.eventuallyEq_one.comp_tendsto hlim] with q hq
  by_cases hr : 0 ≤ q.1
  · rw [seeleyPeriodicExtension_of_nonneg f hr,
      seeleyCylinderExtend_of_nonneg seeleyData (seeleyCutoffField f) hr]
    change f q = boundaryTaylorCutoff q.1 * f q
    have hq' : boundaryTaylorCutoff q.1 = 1 := by
      simpa only [Function.comp_apply, Pi.one_apply] using hq
    rw [hq', one_mul]
  · simp only [seeleyPeriodicExtension, if_neg hr]

/-- A one-sided jointly smooth periodic field has one global jointly
smooth extension. All bounds needed by the series are derived from
periodicity, a fixed radial cutoff, and compactness. -/
theorem contDiff_seeleyPeriodicExtension
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T) :
    ContDiff ℝ ∞ (seeleyPeriodicExtension f) := by
  have hneg := contDiff_seeleyCutoffExtension hf hT hperiod
  apply contDiff_iff_contDiffAt.mpr
  intro p
  rcases lt_trichotomy p.1 0 with hp | hp | hp
  · apply hneg.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
    simp only [seeleyPeriodicExtension, if_neg (not_le.mpr hq)]
  · exact hneg.contDiffAt.congr_of_eventuallyEq (seeleyPeriodicExtension_boundary_germ f hp)
  · have hH : seeleyHalfPlane ∈ 𝓝 p := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
      exact ⟨hq.le, mem_univ _⟩
    apply (hf.contDiffAt hH).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
    exact seeleyPeriodicExtension_of_nonneg f hq.le

theorem seeleyPeriodicExtension_periodic
    {f : ℝ × ℝ → ℝ} {T : ℝ}
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T) (r : ℝ) :
    Function.Periodic (fun θ => seeleyPeriodicExtension f (r, θ)) T := by
  intro θ
  change seeleyPeriodicExtension f (r, θ + T) = seeleyPeriodicExtension f (r, θ)
  by_cases hr : 0 ≤ r
  · rw [seeleyPeriodicExtension_of_nonneg f (p := (r, θ + T)) hr,
      seeleyPeriodicExtension_of_nonneg f (p := (r, θ)) hr]
    exact hperiod r hr θ
  · dsimp only [seeleyPeriodicExtension]
    simp only [if_neg hr]
    exact seeleyCylinderExtend_periodic_of_halfPlane seeleyData
      (seeleyCutoffField_periodic hperiod) r θ

/-- Every ordinary Fréchet jet of the extension on the closed half-plane
equals the corresponding actual within-jet of the original field. -/
theorem iteratedFDeriv_seeleyPeriodicExtension_eq_within
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f seeleyHalfPlane)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ∀ r, 0 ≤ r → Function.Periodic (fun θ => f (r, θ)) T)
    (n : ℕ) {p : ℝ × ℝ} (hp : p ∈ seeleyHalfPlane) :
    iteratedFDeriv ℝ n (seeleyPeriodicExtension f) p =
      iteratedFDerivWithin ℝ n f seeleyHalfPlane p := by
  calc
    _ = iteratedFDerivWithin ℝ n (seeleyPeriodicExtension f) seeleyHalfPlane p :=
      (iteratedFDerivWithin_eq_iteratedFDeriv (n := n) uniqueDiffOn_seeleyHalfPlane
        ((contDiff_seeleyPeriodicExtension hf hT hperiod).contDiffAt.of_le (by simp)) hp).symm
    _ = _ := iteratedFDerivWithin_congr
      (fun q hq => seeleyPeriodicExtension_of_nonneg f hq.1) hp n

end ContinuousFlexibility.Analysis
