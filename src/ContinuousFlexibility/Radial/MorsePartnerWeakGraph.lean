module

public import ContinuousFlexibility.Radial.MorseMaximalDomain

/-!
# The maximal graph of the Morse partner family

The Darboux step changes `α` while keeping `w` and the asymptotic potential
`b` fixed. The shifted resolvent and the positive-potential kernel theorem
identify the distributional graph throughout this parameter family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def morsePartnerPotential (α w b x : ℝ) : ℝ :=
  w ^ 2 * exp (-x) ^ 2 - w * (2 * α + 1) * exp (-x) + b

theorem morsePartnerPotential_contDiff (α w b : ℝ) : ContDiff ℝ ∞ (morsePartnerPotential α w b) :=
  ((contDiff_const.mul (contDiff_id.neg.exp.pow 2)).sub
    (contDiff_const.mul contDiff_id.neg.exp)).add contDiff_const

theorem morsePartnerPotential_paper {A : ℝ} (hA : 0 ≤ A) (j B : ℝ) :
    morsePartnerPotential ((j * sqrt A - 1) / 2) (j * sqrt A) (j ^ 2 * B) =
      Statements.morsePotential j A B := by
  have hw : (j * sqrt A) ^ 2 = j ^ 2 * A := by rw [mul_pow, sq_sqrt hA]
  have hα : 2 * ((j * sqrt A - 1) / 2) + 1 = j * sqrt A := by ring
  have hmix : j * sqrt A * (2 * ((j * sqrt A - 1) / 2) + 1) = j ^ 2 * A := by
    rw [hα, ← pow_two, hw]
  funext x
  rw [morsePartnerPotential, morsePotential_quadratic, hw, hmix]
  ring

theorem morsePartnerPotential_add_shift_ge_one (α w b x : ℝ) :
    1 ≤ morsePartnerPotential α w b x + morseFormShift α b := by
  unfold morsePartnerPotential morseFormShift
  nlinarith only [sq_nonneg (w * exp (-x) - (2 * α + 1) / 2),
    sq_nonneg (2 * α + 1), neg_le_abs b]

theorem morsePartner_weakGraph_iff_compactWeak (α w b : ℝ) (u f : MorseL2) :
    Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u f ↔
      MorseCompactWeakEquation α w b u f := Iff.rfl

private theorem morsePartner_shifted_residual_eq_zero (α w b : ℝ) (u v f : MorseL2)
    (hu : MorseCompactWeakEquation α w b u f)
    (hv : MorseCompactWeakEquation α w b v
      (f + morseFormShift α b • u - morseFormShift α b • v)) : u = v := by
  let V := morsePartnerPotential α w b
  let γ := morseFormShift α b
  have hV : Continuous V := (morsePartnerPotential_contDiff α w b).continuous
  apply sub_eq_zero.mp
  apply morseWeakPositiveKernel_eq_zero (Q := fun x => V x + γ)
    (hV.add continuous_const) (morsePartnerPotential_add_shift_ge_one α w b) (u - v)
  intro φ hφ hcp
  let Hφ := morseExpression α w b φ
  have hP : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hcp
  have hHφ : MemLp Hφ 2 volume := morseCompactImage_memLp hφ hcp α w b
  let P := morseTestPairing φ hP
  let L := morseTestPairing Hφ hHφ
  have huφ : P f = L u := by
    change morseTestPairing φ hP f = morseTestPairing Hφ hHφ u
    rw [morseTestPairing_apply, morseTestPairing_apply]
    exact hu φ hφ hcp
  have hvφ : P (f + γ • u - γ • v) = L v := by
    change morseTestPairing φ hP (f + γ • u - γ • v) = morseTestPairing Hφ hHφ v
    rw [morseTestPairing_apply, morseTestPairing_apply]
    exact hv φ hφ hcp
  let z : MorseL2 := u - v
  have hz : L z = -(γ * P z) := by
    change L (u - v) = -(γ * P (u - v))
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hvφ
    simp only [map_sub]
    linarith only [huφ, hvφ]
  change morseTestPairing Hφ hHφ z = -(γ * morseTestPairing φ hP z) at hz
  rw [morseTestPairing_apply, morseTestPairing_apply] at hz
  have hdd := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2
  have hD : MemLp (deriv (deriv φ)) 2 volume :=
    hdd.continuous.memLp_of_hasCompactSupport hcp.deriv.deriv
  have hVφ : MemLp (fun x => V x * φ x) 2 volume :=
    (hV.mul hφ.continuous).memLp_of_hasCompactSupport hcp.mul_left
  have hDint : Integrable (fun x => z x * deriv (deriv φ) x) volume :=
    (Lp.memLp z).integrable_mul hD
  have hVint : Integrable (fun x => z x * (V x * φ x)) volume := (Lp.memLp z).integrable_mul hVφ
  have hPint : Integrable (fun x => z x * φ x) volume := (Lp.memLp z).integrable_mul hP
  have hsplit : (∫ x : ℝ, z x * Hφ x) =
      -(∫ x : ℝ, z x * deriv (deriv φ) x) + ∫ x : ℝ, z x * (V x * φ x) := by
    calc
      _ = ∫ x : ℝ, -(z x * deriv (deriv φ) x) + z x * (V x * φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [Hφ, V, morseExpression, morsePartnerPotential]
        ring
      _ = _ := by
        have ha := integral_add hDint.neg hVint
        simp only [Pi.neg_apply] at ha
        rw [ha, integral_neg]
  have hshift : (∫ x : ℝ, (V x + γ) * z x * φ x) =
      (∫ x : ℝ, z x * (V x * φ x)) + γ * ∫ x : ℝ, z x * φ x := by
    calc
      _ = ∫ x : ℝ, z x * (V x * φ x) + γ * (z x * φ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_add hVint (hPint.const_mul γ), integral_const_mul]
  change (∫ x : ℝ, z x * deriv (deriv φ) x) = ∫ x : ℝ, (V x + γ) * z x * φ x
  rw [hsplit] at hz
  rw [hshift]
  linarith only [hz]

/-- For fixed positive `w`, every weak `L²` pair belongs to the true associated
graph, for every real partner parameter `α` and asymptotic value `b`. -/
theorem morsePartner_compactWeak_iff_associated (α b : ℝ) {w : ℝ} (hw : 0 < w)
    (u f : MorseL2) :
    MorseCompactWeakEquation α w b u f ↔ (u, f) ∈ morseAssociatedGraph α w b := by
  constructor
  · intro hu
    let γ := morseFormShift α b
    let v := morseShiftedResolvent α b hw (f + γ • u)
    have hv : (v, f + γ • u - γ • v) ∈ morseAssociatedGraph α w b :=
      morseShiftedResolvent_mem_graph α b hw (f + γ • u)
    have hvweak := morseAssociatedGraph_compact_weak α w b _ _ hv
    have he := morsePartner_shifted_residual_eq_zero α w b u v f hu hvweak
    simpa only [he, add_sub_cancel_right] using hv
  · exact morseAssociatedGraph_compact_weak α w b u f

theorem morsePartner_weakGraph_iff_associated (α b : ℝ) {w : ℝ} (hw : 0 < w)
    (u f : MorseL2) :
    Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u f ↔
      (u, f) ∈ morseAssociatedGraph α w b :=
  (morsePartner_weakGraph_iff_compactWeak α w b u f).trans
    (morsePartner_compactWeak_iff_associated α b hw u f)

end ContinuousFlexibility.Radial
