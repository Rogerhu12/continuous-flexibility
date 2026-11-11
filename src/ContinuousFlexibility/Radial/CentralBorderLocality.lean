import ContinuousFlexibility.Radial.CentralTrueBorder

/-!
# Locality of the genuine metric border

A compact metric control only uses the profile and kernel near its closed
support.  This gives global equality of the resulting actual columns, even
when the profiles have different values outside that neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

theorem radialJacobi_border_zero_of_notMem_tsupport
    {w φ χ : ℝ → ℝ} {r : ℝ} (hr : r ∉ tsupport χ) :
    radialJacobi 4 (fun t => w t * χ t) φ r = 0 := by
  have hχ := notMem_tsupport_iff_eventuallyEq.mp hr
  have hv : (fun t => w t * χ t) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
    filter_upwards [hχ] with t ht
    change χ t = 0 at ht
    rw [ht, mul_zero]
  have hg : (fun t => (w t * χ t) * deriv φ t) =ᶠ[𝓝 r]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hχ] with t ht
    change χ t = 0 at ht
    rw [ht, mul_zero, zero_mul]
  simp only [radialJacobi]
  rw [hg.deriv_eq, hv.deriv_eq]
  simp

/-- The same metric control produces exactly the same global column when
the profile and kernel agree on an open neighborhood of its closed support. -/
theorem radialJacobi_border_congr_on_support
    {w φ w' φ' χ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hχ : tsupport χ ⊆ U)
    (hw : EqOn w w' U) (hφ : EqOn φ φ' U) :
    (fun r => radialJacobi 4 (fun t => w t * χ t) φ r) =
      (fun r => radialJacobi 4 (fun t => w' t * χ t) φ' r) := by
  funext r
  by_cases hr : r ∈ U
  · have hv : EqOn (fun t => w t * χ t) (fun t => w' t * χ t) U := by
      intro t ht
      rw [hw ht]
    have hg : EqOn (fun t => (w t * χ t) * deriv φ t)
        (fun t => (w' t * χ t) * deriv φ' t) U := by
      intro t ht
      rw [hw ht, hφ.deriv hU ht]
    simp only [radialJacobi]
    rw [hg.deriv hU hr, hv.deriv hU hr, hφ hr]
  · have hχr : r ∉ tsupport χ := fun ht => hr (hχ ht)
    rw [radialJacobi_border_zero_of_notMem_tsupport (w := w) (φ := φ) hχr,
      radialJacobi_border_zero_of_notMem_tsupport (w := w') (φ := φ') hχr]

/-- A function smooth on positive radii admits a globally smooth representative
on any prescribed relatively compact positive interval.  This auxiliary
representative is used only to apply the existing integration-by-parts lemma. -/
theorem exists_contDiff_eqOn_positive_interval {f : ℝ → ℝ} {l h : ℝ}
    (hl : 0 < l) (hlh : l < h)
    (hf : ∀ r, 0 < r → ContDiffAt ℝ ∞ f r) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (Ioo l h) := by
  let m : ℝ := (l + h) / 2
  let d : ℝ := (h - l) / 2
  let β : ContDiffBump m :=
    ⟨d + l / 8, d + l / 4, by dsimp only [d]; linarith, by linarith⟩
  have hsupport : tsupport (β : ℝ → ℝ) ⊆ Ioi (0 : ℝ) := by
    rw [β.tsupport_eq, Real.closedBall_eq_Icc]
    intro r hr
    change m - (d + l / 4) ≤ r ∧ r ≤ m + (d + l / 4) at hr
    change 0 < r
    dsimp only [m, d] at hr
    linarith [hr.1]
  refine ⟨fun r => β r * f r, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro r
    by_cases hr : r ∈ tsupport (β : ℝ → ℝ)
    · exact β.contDiffAt.mul (hf r (hsupport hr))
    · have hzero : (fun r => β r * f r) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hr] with t ht
        change β t = 0 at ht
        rw [ht, zero_mul]
      exact ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) r) hzero
  · intro r hr
    have hball : r ∈ Metric.closedBall m β.rIn := by
      rw [Real.closedBall_eq_Icc]
      change m - (d + l / 8) ≤ r ∧ r ≤ m + (d + l / 8)
      dsimp only [m, d]
      constructor <;> linarith [hr.1, hr.2]
    rw [β.one_of_mem_closedBall hball, one_mul]

end ContinuousFlexibility.Radial
