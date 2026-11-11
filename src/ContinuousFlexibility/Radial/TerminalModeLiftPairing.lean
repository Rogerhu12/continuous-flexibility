import ContinuousFlexibility.Radial.ModeInnerSourcePairing
import ContinuousFlexibility.Radial.TerminalMorseEnergySeparation

/-!
# Actual mode pairings for terminal cutoff sources

This bridges the true L² representative and regional source projection
to the already proved physical density integral. Diagonal entries are
the actual cutoff energy, and off-diagonal entries vanish by the
proved separation of the two cutoffs.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem terminalModeLiftSource_pairing_eq_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h lamLeft lamRight : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D)
    {L F : RadialModePair D} {ell χ η u v : ℝ → ℝ}
    (hLrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell)
    (hell : EqOn ell (terminalCapLift lamLeft χ u) (Icc l h))
    (hFrep : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      terminalCapHilbertSource lamRight D.w η v)
    (hFfix : modeInnerSource D l h F = F) (hFscalar : F.2 = 0) :
    modePairing D L F = ∫ x in l..h, matchingDensity D x *
      terminalCapLift lamLeft χ u x * terminalCapHilbertSource lamRight D.w η v x := by
  rw [modeInnerSource_pairing_eq_integral hD hlh hsub L F hFfix hFscalar hLrep]
  calc
    _ = ∫ x in l..h, matchingDensity D x * terminalCapLift lamLeft χ u x * F.1 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc l h := by simpa only [uIcc_of_le hlh] using hx
      change matchingDensity D x * ell x * F.1 x =
        matchingDensity D x * terminalCapLift lamLeft χ u x * F.1 x
      rw [hell hx']
    _ = _ := by
      apply matchingSubinterval_congr_ae hD hlh hsub
      filter_upwards [hFrep] with x hx
      change matchingDensity D x * terminalCapLift lamLeft χ u x * F.1 x =
        matchingDensity D x * terminalCapLift lamLeft χ u x *
          terminalCapHilbertSource lamRight D.w η v x
      rw [hx]

theorem terminalModeLiftSource_pairing_energy {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h lam : ℝ} (hlh : l ≤ h)
    (hsub : Icc l h ⊆ radialCore D) (hlam : 0 < lam)
    {L F : RadialModePair D} {ell χ u : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hLrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell)
    (hell : EqOn ell (terminalCapLift lam χ u) (Icc l h))
    (hFrep : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] terminalCapHilbertSource lam D.w χ u)
    (hFfix : modeInnerSource D l h F = F) (hFscalar : F.2 = 0)
    (hderivSupport : tsupport (deriv χ) ⊆ Ioo l h) :
    modePairing D L F = (∫ x in l..h, terminalCapCutoffEnergy D.w χ u x) / lam := by
  rw [terminalModeLiftSource_pairing_eq_integral hD hlh hsub hLrep hell hFrep hFfix hFscalar]
  have hleft : deriv χ l = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl l) (hderivSupport hx).1)
  have hright : deriv χ h = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hx
    exact (lt_irrefl h) (hderivSupport hx).2)
  have hg := matchingProfileGeometry hD
  have hcore (x : ℝ) (hx : x ∈ uIcc l h) : x ∈ radialCore D :=
    hsub (by simpa only [uIcc_of_le hlh] using hx)
  exact terminalCapLift_source_density_pairing hlam hg.2.2.1.1 hχ hu hleft hright
    (fun x hx => (hg.1.trans (hcore x hx).1).ne')
    (fun x hx => (hg.2.2.2.2.1 x (hcore x hx)).ne')

theorem terminalModeLiftSource_pairing_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {l h lamLeft lamRight : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D)
    {L F : RadialModePair D} {ell χ η u v : ℝ → ℝ}
    (hLrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell)
    (hell : EqOn ell (terminalCapLift lamLeft χ u) (Icc l h))
    (hFrep : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] terminalCapHilbertSource lamRight D.w η v)
    (hFfix : modeInnerSource D l h F = F) (hFscalar : F.2 = 0)
    (hsep : Disjoint (tsupport χ) (tsupport η)) :
    modePairing D L F = 0 := by
  rw [terminalModeLiftSource_pairing_eq_integral hD hlh hsub hLrep hell hFrep hFfix hFscalar]
  calc
    _ = ∫ _x in l..h, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change matchingDensity D x * terminalCapLift lamLeft χ u x *
        terminalCapHilbertSource lamRight D.w η v x = 0
      rw [mul_assoc, terminalCapLift_source_mixed_zero hsep, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

theorem terminalCapCutoffEnergy_support (w χ u : ℝ → ℝ) :
    Function.support (terminalCapCutoffEnergy w χ u) ⊆ tsupport (deriv χ) := by
  intro x hx
  apply subset_tsupport (deriv χ)
  intro hz
  exact hx (by simp only [terminalCapCutoffEnergy, hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul])

theorem terminalCapCutoffEnergy_integral_restrict {l h a b : ℝ} (hla : l ≤ a) (hbh : b ≤ h)
    {w χ u : ℝ → ℝ} (hs : tsupport (deriv χ) ⊆ Ioo a b) :
    (∫ x in l..h, terminalCapCutoffEnergy w χ u x) =
      ∫ x in a..b, terminalCapCutoffEnergy w χ u x := by
  have hf := (terminalCapCutoffEnergy_support w χ u).trans hs
  have hinner : Function.support (terminalCapCutoffEnergy w χ u) ⊆ Ioc l h := by
    intro x hx
    exact ⟨hla.trans_lt (hf hx).1, (hf hx).2.le.trans hbh⟩
  have hcap : Function.support (terminalCapCutoffEnergy w χ u) ⊆ Ioc a b :=
    fun x hx => ⟨(hf hx).1, (hf hx).2.le⟩
  exact (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hinner).trans
    (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hcap).symm

theorem terminalMorseCap_deriv_support (long : Bool) {A B s : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r) :
    tsupport (deriv (terminalMorsePhysicalCutoff long A B s r)) ⊆
      Ioo (terminalMorseLayerRadius long A B s r 0)
        (terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A)) := by
  let L := terminalMorseLayerLength long A
  let R := terminalMorseLayerRadius long A B s r
  have hA : 0 < A := (mul_pos (by norm_num) hB).trans hAB
  have hL : 0 < L := terminalMorseLayerLength_pos long hA
  have hm := terminalMorseLayerRadius_strictMono long hB hAB hs hr
  have hleft : R 0 < terminalMorseLayerLeft long A B s r :=
    hm ⟨le_rfl, hL.le⟩ ⟨by linarith only [hL], by linarith only [hL]⟩
      (by linarith only [hL])
  have hright : terminalMorseLayerRight long A B s r < R L :=
    hm ⟨by linarith only [hL], by linarith only [hL]⟩ ⟨hL.le, le_rfl⟩
      (by linarith only [hL])
  intro x hx
  have h := terminalMorsePhysicalCutoff_tsupport_deriv long hB hAB hs hr hx
  exact ⟨hleft.trans_le h.1, h.2.trans_lt hright⟩

/-- The exact diagonal mode pairing is the same actual cap integral
whose relative exponentially small bound has already been proved. -/
theorem terminalModeMorseLiftSource_pairing_energy {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (long : Bool)
    {A B s lam l h : ℝ} {r u ell : ℝ → ℝ} {L F : RadialModePair D}
    (hB : 0 < B) (hAB : 4 * B < A) (hs : 0 < s) (hr : IsNormalizedMorseCell A B r)
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) (hlam : 0 < lam)
    (hu : ContDiff ℝ ∞ u)
    (hleft : l ≤ terminalMorseLayerRadius long A B s r 0)
    (hright : terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A) ≤ h)
    (hLrep : (L.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ell)
    (hell : EqOn ell (terminalCapLift lam (terminalMorsePhysicalCutoff long A B s r) u) (Icc l h))
    (hFrep : (F.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      terminalCapHilbertSource lam D.w (terminalMorsePhysicalCutoff long A B s r) u)
    (hFfix : modeInnerSource D l h F = F) (hFscalar : F.2 = 0) :
    modePairing D L F =
      (∫ x in terminalMorseLayerRadius long A B s r 0..
        terminalMorseLayerRadius long A B s r (terminalMorseLayerLength long A),
          terminalCapCutoffEnergy D.w (terminalMorsePhysicalCutoff long A B s r) u x) / lam := by
  have hsupp := terminalMorseCap_deriv_support long hB hAB hs hr
  have hsinner : tsupport (deriv (terminalMorsePhysicalCutoff long A B s r)) ⊆ Ioo l h := by
    intro x hx
    exact ⟨hleft.trans_lt (hsupp hx).1, (hsupp hx).2.trans_le hright⟩
  rw [terminalModeLiftSource_pairing_energy hD hlh hsub hlam
    (terminalMorsePhysicalCutoff_smooth long A B s r) hu hLrep hell hFrep hFfix hFscalar hsinner]
  rw [terminalCapCutoffEnergy_integral_restrict hleft hright hsupp]

end ContinuousFlexibility.Radial

