module

public import ContinuousFlexibility.Radial.MorseRealizationBasic
public import ContinuousFlexibility.Radial.MorseChainScales

/-!
# Pulling an actual physical state back to a retained Morse cell

The value and scaled physical flux are pulled back along the actual
radius chart.  Differentiating the realized profile identity on the
closed interval also covers the retained cut points.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem morseRealized_state_pullback {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} {j scale : ℝ} {u z : ℝ → ℝ}
    (h : MorseChainRealization T σ D C) (hσ : ∀ k, 1 ≤ σ k ∧ σ k ≤ 2)
    (hscale : 0 < scale) (side : Bool) (n : ℕ) (hn : T.index ≤ n)
    (hstate : ∀ r ∈ Icc (T.radius side n (T.leftX side n))
        (T.radius side n (T.rightX side n)),
      HasDerivAt u (scale / D.w r * z r) r ∧
        HasDerivAt z (j ^ 2 * deriv D.w r / (scale * r) * u r) r) :
    ∀ X ∈ Icc (T.leftX side n) (T.rightX side n),
      HasDerivAt (fun Y => u (T.radius side n Y))
        ((scale / morseChainAmplitude T σ n) * z (T.radius side n X)) X ∧
      HasDerivAt (fun Y => (scale / morseChainAmplitude T σ n) * z (T.radius side n Y))
        (-(j ^ 2 * morseRho (morseChainA T n) (morseChainB T n) X *
          u (T.radius side n X))) X := by
  let R := T.radius side n
  let a := T.leftX side n
  let b := T.rightX side n
  let lam := morseChainAmplitude T σ n
  have hret := h.retained_data side n hn
  have hab : a < b := hret.2.2.2.1.trans hret.2.2.2.2.1
  have hR : ContDiff ℝ ∞ R := h.radius_smooth side n hn
  have hR' : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hw : ContDiff ℝ ∞ D.w := h.geometry.2.2.1.1
  have hlam : 0 < lam := morseChainAmplitude_pos T σ hσ n
  have hprofile : EqOn (fun Y => D.w (R Y)) (fun Y => lam * deriv R Y) (Icc a b) :=
    fun _ hY => h.profile_eq side n hn _ hY
  intro X hX
  have hRX : R X ∈ Icc (R a) (R b) :=
    ⟨(h.radius_strictMonoOn side n hn).monotoneOn (left_mem_Icc.mpr hab.le) hX hX.1,
      (h.radius_strictMonoOn side n hn).monotoneOn hX (right_mem_Icc.mpr hab.le) hX.2⟩
  have hRXpos : 0 < R X := h.radius_positive side n hn X hX
  have hRvpos : 0 < deriv R X := h.derivative_positive side n hn X hX
  have hRd : HasDerivAt R (deriv R X) X := (hR.differentiable (by simp) X).hasDerivAt
  have hcomp := ((hw.differentiable (by simp) (R X)).hasDerivAt).comp X hRd
  have hmodel := ((hR'.differentiable (by simp) X).hasDerivAt).const_mul lam
  have hderivative := derivWithin_congr hprofile (hprofile hX)
  change derivWithin (D.w ∘ R) (Icc a b) X =
    derivWithin (fun Y => lam * deriv R Y) (Icc a b) X at hderivative
  rw [hcomp.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab X hX),
    hmodel.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab X hX)] at hderivative
  have hweight : deriv D.w (R X) * deriv R X =
      -(lam * morseRho (morseChainA T n) (morseChainB T n) X * R X) := by
    rw [hderivative, h.equation side n hn X hX]
    ring
  obtain ⟨hu, hz⟩ := hstate (R X) hRX
  constructor
  · apply (hu.comp X hRd).congr_deriv
    change scale / D.w (R X) * z (R X) * deriv R X = scale / lam * z (R X)
    have hprofileX : D.w (R X) = lam * deriv R X := hprofile hX
    rw [hprofileX]
    field_simp [hlam.ne', hRvpos.ne'] <;> ring
  · apply ((hz.comp X hRd).const_mul (scale / lam)).congr_deriv
    calc
      _ = (j ^ 2 * u (R X) / (lam * R X)) * (deriv D.w (R X) * deriv R X) := by
        field_simp [hscale.ne', hlam.ne', hRXpos.ne'] <;> ring
      _ = (j ^ 2 * u (R X) / (lam * R X)) *
          (-(lam * morseRho (morseChainA T n) (morseChainB T n) X * R X)) := by rw [hweight]
      _ = _ := by field_simp [hlam.ne', hRXpos.ne'] <;> ring

end ContinuousFlexibility.Radial
