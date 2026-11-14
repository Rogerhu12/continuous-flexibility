module

public import ContinuousFlexibility.Radial.TerminalMorseLiftEnergy

/-!
# Extending the actual cutoff-energy integral to the inner interval

Only the derivative of the physical cutoff contributes to this energy.
Its support lies strictly inside the same model cap, so enlarging the
integration interval leaves the actual cutoff-energy error unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory
open scoped ContDiff

theorem terminalCapCutoffEnergy_support_of_deriv {w χ u : ℝ → ℝ} {a b : ℝ}
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hd : tsupport (deriv χ) ⊆ Icc a b) :
    Function.support (terminalCapCutoffEnergy w χ u) ⊆ Ioo a b := by
  have hs : Function.support (terminalCapCutoffEnergy w χ u) ⊆ Icc a b := by
    intro r hr
    apply hd
    apply subset_tsupport
    intro hz
    exact hr (by simp only [terminalCapCutoffEnergy, hz, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul])
  have hopen := (terminalCapCutoffEnergy_continuous hw hχ hu).isOpen_support
  simpa only [interior_Icc] using hopen.subset_interior_iff.mpr hs

theorem terminalCapCutoffEnergy_integral_of_deriv_support {w χ u : ℝ → ℝ}
    {a b lo hi : ℝ} (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hu : ContDiff ℝ ∞ u) (hd : tsupport (deriv χ) ⊆ Icc a b)
    (hlo : lo ≤ a) (hhi : b ≤ hi) :
    (∫ r in lo..hi, terminalCapCutoffEnergy w χ u r) =
      ∫ r in a..b, terminalCapCutoffEnergy w χ u r := by
  have hs := terminalCapCutoffEnergy_support_of_deriv hw hχ hu hd
  have hsmall : Function.support (terminalCapCutoffEnergy w χ u) ⊆ Ioc a b :=
    fun _ hr => ⟨(hs hr).1, (hs hr).2.le⟩
  have hlarge : Function.support (terminalCapCutoffEnergy w χ u) ⊆ Ioc lo hi :=
    fun _ hr => ⟨hlo.trans_lt (hs hr).1, (hs hr).2.le.trans hhi⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hlarge,
    intervalIntegral.integral_eq_integral_of_support_subset hsmall]

theorem terminalMorsePhysicalCutoff_derivative_inside_cap (side : Bool)
    {A B s : ℝ} {r : ℝ → ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    tsupport (deriv (terminalMorsePhysicalCutoff side A B s r)) ⊆
      Ioo (terminalMorseLayerRadius side A B s r 0)
        (terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A)) := by
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL := terminalMorseLayerLength_pos side hA
  have hm := terminalMorseLayerRadius_strictMono side hB hAB hs hr
  have hlo := hm ⟨le_rfl, hL.le⟩
    ⟨by linarith only [hL], by linarith only [hL]⟩
    (by linarith only [hL] : (0 : ℝ) < terminalMorseLayerLength side A / 4)
  have hhi := hm
    ⟨by linarith only [hL], by linarith only [hL]⟩ ⟨hL.le, le_rfl⟩
    (by linarith only [hL] : terminalMorseLayerLength side A / 2 < terminalMorseLayerLength side A)
  intro x hx
  have hmem := terminalMorsePhysicalCutoff_tsupport_deriv side hB hAB hs hr hx
  exact ⟨hlo.trans_le hmem.1, hmem.2.trans_lt hhi⟩

theorem terminalMorse_cutoffEnergy_integral_cap (side : Bool)
    {A B s lo hi : ℝ} {r w u : ℝ → ℝ} (hB : 0 < B) (hAB : 4 * B < A)
    (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u)
    (hlo : lo ≤ terminalMorseLayerRadius side A B s r 0)
    (hhi : terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A) ≤ hi) :
    (∫ z in lo..hi, terminalCapCutoffEnergy w (terminalMorsePhysicalCutoff side A B s r) u z) =
      ∫ z in (terminalMorseLayerRadius side A B s r 0)..
        (terminalMorseLayerRadius side A B s r (terminalMorseLayerLength side A)),
        terminalCapCutoffEnergy w (terminalMorsePhysicalCutoff side A B s r) u z := by
  exact terminalCapCutoffEnergy_integral_of_deriv_support hw
    (terminalMorsePhysicalCutoff_smooth side A B s r) hu
    ((terminalMorsePhysicalCutoff_derivative_inside_cap side hB hAB hs hr).trans
      Ioo_subset_Icc_self) hlo hhi

end ContinuousFlexibility.Radial
