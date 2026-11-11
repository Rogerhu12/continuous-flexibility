import ContinuousFlexibility.Radial.SeedLogarithmicSlope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Reconstruction and exact cone germs of a prescribed-slope connector

The primitives in LogSlopeConnector recover the original profile and the
original signed solution wherever the prescribed slope agrees with its
actual logarithmic slope. Agreement is on an open connected set, so the
result supplies equality of all germs at a splice, rather than just
matching values. The constant-slope height formula treats both cone
powers in the same theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- Equality in an open set of logarithmic coordinates gives a radial germ. -/
theorem eventuallyEq_of_eqOn_exp {f g : ℝ → ℝ} {J : Set ℝ} {y₀ : ℝ}
    (hJ : IsOpen J) (hy₀ : y₀ ∈ J)
    (heq : ∀ y ∈ J, f (exp y) = g (exp y)) :
    f =ᶠ[𝓝 (exp y₀)] g := by
  have ht : Tendsto log (𝓝 (exp y₀)) (𝓝 y₀) := by
    simpa only [log_exp] using (continuousAt_log (exp_pos y₀).ne').tendsto
  filter_upwards [ht.eventually (hJ.mem_nhds hy₀),
    Ioi_mem_nhds (exp_pos y₀)] with r hr hrpos
  simpa only [exp_log hrpos] using heq (log r) hr

/-- Recover a signed solution from its logarithmic slope and one value. -/
theorem connectorHeight_reconstruct {k u : ℝ → ℝ} {J : Set ℝ} {y₀ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hy₀ : y₀ ∈ J)
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hne : ∀ y ∈ J, u (exp y) ≠ 0)
    (hks : EqOn k (seedLogSlope u) J) :
    ∀ y ∈ J, u (exp y) =
      u (exp y₀) * connectorHeight k y₀ 0 (exp y) := by
  let G : ℝ → ℝ := connectorLogHeight k y₀ 0
  let F : ℝ → ℝ := fun y => u (exp y) * exp (-G y)
  have hd (y : ℝ) (hy : y ∈ J) : HasDerivAt F 0 y := by
    have h := ((hu y hy).hasDerivAt.comp y (hasDerivAt_exp y)).mul
      ((hasDerivAt_connectorLogHeight hk y₀ 0 y).neg.exp)
    apply h.congr_deriv
    have hm : deriv u (exp y) * exp y = u (exp y) * k y := by
      rw [hks hy, seedLogSlope]
      field_simp [hne y hy]
      <;> ring
    simp only [Function.comp_apply]
    rw [hm]
    ring
  intro y hy
  have hc : F y = F y₀ :=
    hJ.is_const_of_deriv_eq_zero hconn
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) hy hy₀
  have hG₀ : G y₀ = 0 := connectorLogHeight_self k y₀ 0
  change u (exp y) * exp (-G y) = u (exp y₀) * exp (-G y₀) at hc
  rw [hG₀, neg_zero, exp_zero, mul_one, exp_neg] at hc
  have he : u (exp y) = u (exp y₀) * exp (G y) :=
    (div_eq_iff (exp_pos (G y)).ne').mp (by
      simpa only [div_eq_mul_inv] using hc)
  rw [connectorHeight, log_exp]
  exact he

/-- The reconstruction holds as a full germ, with the sign in the constant. -/
theorem connectorHeight_reconstruct_germ {k u : ℝ → ℝ} {J : Set ℝ} {y₀ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hJ : IsOpen J) (hconn : IsPreconnected J)
    (hy₀ : y₀ ∈ J)
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hne : ∀ y ∈ J, u (exp y) ≠ 0)
    (hks : EqOn k (seedLogSlope u) J) :
    (fun r => u (exp y₀) * connectorHeight k y₀ 0 r) =ᶠ[𝓝 (exp y₀)] u := by
  apply eventuallyEq_of_eqOn_exp hJ hy₀
  intro y hy
  exact (connectorHeight_reconstruct hk hJ hconn hy₀ hu hne hks y hy).symm

/-- On a connected logarithmic interval where the actual second-mode
equation holds, the profile primitive reconstructs the original profile. -/
theorem connectorProfile_reconstruct {k w u : ℝ → ℝ} {J : Set ℝ} {y₀ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hk4 : ∀ y, k y < 4)
    (hJ : IsOpen J) (hconn : IsPreconnected J) (hy₀ : y₀ ∈ J)
    (hw : ∀ y ∈ J, DifferentiableAt ℝ w (exp y))
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hu' : ∀ y ∈ J, DifferentiableAt ℝ (deriv u) (exp y))
    (hwpos : ∀ y ∈ J, 0 < w (exp y))
    (hune : ∀ y ∈ J, u (exp y) ≠ 0)
    (hode : ∀ y ∈ J, radialJacobi 4 w u (exp y) = 0)
    (hks : EqOn k (seedLogSlope u) J) :
    ∀ y ∈ J, connectorProfile k y₀ (log (w (exp y₀)) - y₀) (exp y) =
      w (exp y) := by
  let F : ℝ → ℝ := fun y => log (w (exp y)) - y
  have hd (y : ℝ) (hy : y ∈ J) :
      HasDerivAt F (seedProfileSlope w y - 1) y := by
    have h := (((hw y hy).hasDerivAt.comp y (hasDerivAt_exp y)).log
      (hwpos y hy).ne').sub (hasDerivAt_id' y)
    apply h.congr_deriv
    simp only [seedProfileSlope, Function.comp_apply]
    ring
  have hslope (y : ℝ) (hy : y ∈ J) :
      connectorSlope k y = seedProfileSlope w y - 1 := by
    have hkgerm : k =ᶠ[𝓝 y] seedLogSlope u :=
      Filter.eventuallyEq_of_mem (hJ.mem_nhds hy) (fun t ht => hks ht)
    have hden : 4 - seedLogSlope u y ≠ 0 := by
      rw [← hks hy]
      exact (sub_pos.mpr (hk4 y)).ne'
    rw [connectorSlope, hks hy, hkgerm.deriv_eq,
      deriv_seedLogSlope_of_radialJacobi (hw y hy) (hu y hy) (hu' y hy)
        (hwpos y hy).ne' (hune y hy) (hode y hy)]
    field_simp [hden]
    <;> ring
  have heq : EqOn F (connectorLogProfile k y₀ (F y₀)) J := by
    refine hJ.eqOn_of_deriv_eq hconn
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y _ => (hasDerivAt_connectorLogProfile hk hk4 y₀ (F y₀) y).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_) hy₀ ?_
    · rw [(hd y hy).deriv,
        (hasDerivAt_connectorLogProfile hk hk4 y₀ (F y₀) y).deriv]
      exact (hslope y hy).symm
    · exact (connectorLogProfile_self k y₀ (F y₀)).symm
  intro y hy
  change connectorProfile k y₀ (F y₀) (exp y) = w (exp y)
  rw [connectorProfile, log_exp, ← heq hy]
  dsimp only [F]
  rw [exp_sub, exp_log (hwpos y hy)]
  field_simp

theorem connectorProfile_reconstruct_germ {k w u : ℝ → ℝ} {J : Set ℝ} {y₀ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hk4 : ∀ y, k y < 4)
    (hJ : IsOpen J) (hconn : IsPreconnected J) (hy₀ : y₀ ∈ J)
    (hw : ∀ y ∈ J, DifferentiableAt ℝ w (exp y))
    (hu : ∀ y ∈ J, DifferentiableAt ℝ u (exp y))
    (hu' : ∀ y ∈ J, DifferentiableAt ℝ (deriv u) (exp y))
    (hwpos : ∀ y ∈ J, 0 < w (exp y))
    (hune : ∀ y ∈ J, u (exp y) ≠ 0)
    (hode : ∀ y ∈ J, radialJacobi 4 w u (exp y) = 0)
    (hks : EqOn k (seedLogSlope u) J) :
    connectorProfile k y₀ (log (w (exp y₀)) - y₀) =ᶠ[𝓝 (exp y₀)] w :=
  eventuallyEq_of_eqOn_exp hJ hy₀
    (connectorProfile_reconstruct hk hk4 hJ hconn hy₀ hw hu hu' hwpos hune hode hks)

/-- A constant slope makes the primitive affine on its whole connected set. -/
theorem connectorLogHeight_eq_affine_of_const {k : ℝ → ℝ} {J : Set ℝ}
    (hk : ContDiff ℝ ∞ k) (hJ : IsOpen J) (hconn : IsPreconnected J)
    {a : ℝ} (hka : EqOn k (fun _ => a) J)
    (y₀ κ₀ : ℝ) {y₃ : ℝ} (hy₃ : y₃ ∈ J) :
    ∀ y ∈ J, connectorLogHeight k y₀ κ₀ y =
      connectorLogHeight k y₀ κ₀ y₃ + a * (y - y₃) := by
  let G : ℝ → ℝ := connectorLogHeight k y₀ κ₀
  have hd (y : ℝ) :
      HasDerivAt (fun y => G y₃ + a * (y - y₃)) a y := by
    simpa only [mul_one] using
      (((hasDerivAt_id' y).sub_const y₃).const_mul a).const_add (G y₃)
  exact hJ.eqOn_of_deriv_eq hconn
    (fun y _ => (hasDerivAt_connectorLogHeight hk y₀ κ₀ y).differentiableAt.differentiableWithinAt)
    (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    (fun y hy => by
      rw [(hasDerivAt_connectorLogHeight hk y₀ κ₀ y).deriv, (hd y).deriv]
      exact hka hy)
    hy₃ (by simp only [sub_self, mul_zero, add_zero])

/-- Exact height on a cone; in particular this applies to both powers ±2. -/
theorem connectorHeight_eq_power_of_const {k : ℝ → ℝ} {J : Set ℝ}
    (hk : ContDiff ℝ ∞ k) (hJ : IsOpen J) (hconn : IsPreconnected J)
    {a : ℝ} (hka : EqOn k (fun _ => a) J)
    (y₀ κ₀ : ℝ) {y₃ : ℝ} (hy₃ : y₃ ∈ J) {r : ℝ}
    (hr : 0 < r) (hrJ : log r ∈ J) :
    connectorHeight k y₀ κ₀ r =
      exp (connectorLogHeight k y₀ κ₀ y₃ - a * y₃) * r ^ a := by
  have he := connectorLogHeight_eq_affine_of_const hk hJ hconn hka y₀ κ₀ hy₃ (log r) hrJ
  rw [connectorHeight, he, rpow_def_of_pos hr, ← exp_add]
  congr 1
  ring

end ContinuousFlexibility.Radial
