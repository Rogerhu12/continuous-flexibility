module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# Angular regularity of the actual characteristic speed

The corrected determinant separates the characteristic square root into a
continuous radial factor and a smooth angular factor. The radial factor may
vanish or change its radicand's sign: no differentiability of its square root
is used. In particular, the assertions include the closed ends of a control
interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff

/-- The square root depends nonsmoothly only on the radial variable. This
identity is valid for either sign of the radial derivative. -/
theorem polarMinusCharacteristicSpeed_eq_separated
    {w : ℝ → ℝ} (z : PolarPoint → ℝ) {p : PolarPoint}
    (hw : DifferentiableAt ℝ w p.1) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z p)
    (hQ : heightQ (profileEnergy w p) (heightRadial z p)
      (angularPartial (heightAngular z) p) ≠ 0) :
    minusCharacteristicSpeed
        ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ p =
      polarLinearB w z p / polarLinearA w z p -
        Real.sqrt (-w p.1 * deriv w p.1 / p.1) *
          (polarDiscriminant w z p * polarLinearA w z p)⁻¹ := by
  have hdet := polar_corrected_determinant z hw hr hD hQ
  have hdisc : polarLinearB w z p ^ 2 - polarLinearA w z p * polarCorrectedC w z p =
      (-w p.1 * deriv w p.1 / p.1) / polarDiscriminant w z p ^ 2 := by
    calc
      _ = -((w p.1 * deriv w p.1 / p.1) / polarDiscriminant w z p ^ 2) := by
        linarith only [hdet]
      _ = _ := by ring
  have hA : polarLinearA w z p ≠ 0 :=
    mul_ne_zero hQ (inverseDThreeHalves_pos _ hD).ne'
  simp only [minusCharacteristicSpeed, hdisc,
    Real.sqrt_div' _ (sq_nonneg (polarDiscriminant w z p)), Real.sqrt_sq hD.le]
  field_simp [hA, hD.ne']
  <;> ring

/-- Both angular factors are genuinely smooth near every admissible point. -/
theorem contDiffAt_characteristicAngularFactors
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {p : PolarPoint}
    (hw : ContDiffAt ℝ ∞ w p.1) (hz : ContDiffAt ℝ ∞ z p) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant w z p)
    (hQ : heightQ (profileEnergy w p) (heightRadial z p)
      (angularPartial (heightAngular z) p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun x => polarLinearB w z x / polarLinearA w z x) p ∧
      ContDiffAt ℝ ∞ (fun x =>
        (polarDiscriminant w z x * polarLinearA w z x)⁻¹) p := by
  obtain ⟨hA, hB, _⟩ := contDiffAt_heightLinearCoefficients hw hz hr hD hQ
  have hAne : polarLinearA w z p ≠ 0 :=
    mul_ne_zero hQ (inverseDThreeHalves_pos _ hD).ne'
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) p :=
    contDiffAt_const.add ((hw.comp p contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial hz (m := ∞) (by simp)
  have hp := contDiffAt_heightAngular hz (m := ∞) (by simp) hr
  have hd : ContDiffAt ℝ ∞ (polarDiscriminant w z) p :=
    (hE.mul (contDiffAt_const.sub (hp.pow 2))).sub (hk.pow 2)
  exact ⟨hB.div hA hAne, (hd.mul hA).inv (mul_ne_zero hD.ne' hAne)⟩

/-- Periodicity uses the actual coefficient identities, including their
totalized derivatives. It does not need a sign condition on the radicand. -/
theorem polarMinusCharacteristicSpeed_periodic
    (w : ℝ → ℝ) {z : PolarPoint → ℝ} {P : ℝ}
    (hz : Function.Periodic z (0, P)) :
    Function.Periodic
      (minusCharacteristicSpeed
        ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩) (0, P) := by
  obtain ⟨hA, hB, hC⟩ := periodic_heightCorrectedCoefficients w hz
  intro p
  simp only [minusCharacteristicSpeed, hA p, hB p, hC p]

/-- The actual speed has a continuous angular derivative on a closed
strip, although its radial square-root factor need only be continuous. -/
theorem exists_polarMinusCharacteristicSpeed_angularDerivative
    {w : ℝ → ℝ} {z : PolarPoint → ℝ} {l h : ℝ}
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z) (hl : 0 < l)
    (hadm : ∀ r ∈ Icc l h, ∀ θ,
      0 < polarDiscriminant w z (r, θ) ∧
      heightQ (profileEnergy w (r, θ)) (heightRadial z (r, θ))
        (angularPartial (heightAngular z) (r, θ)) ≠ 0) :
    ∃ dG : PolarPoint → ℝ,
      ContinuousOn
        (minusCharacteristicSpeed
          ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩)
        (Icc l h ×ˢ univ) ∧
      ContinuousOn dG (Icc l h ×ˢ univ) ∧
      ∀ r ∈ Icc l h, ∀ θ,
        HasDerivAt
          (fun t => minusCharacteristicSpeed
            ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ (r, t))
          (dG (r, θ)) θ := by
  let R : ℝ → ℝ := fun r => Real.sqrt (-w r * deriv w r / r)
  let b : PolarPoint → ℝ := fun p => polarLinearB w z p / polarLinearA w z p
  let f : PolarPoint → ℝ := fun p =>
    (polarDiscriminant w z p * polarLinearA w z p)⁻¹
  have hlocal (p : PolarPoint) (hp : p ∈ Icc l h ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ b p ∧ ContDiffAt ℝ ∞ f p := by
    exact contDiffAt_characteristicAngularFactors hw.contDiffAt hz.contDiffAt
      (hl.trans_le hp.1.1).ne' (hadm p.1 hp.1 p.2).1 (hadm p.1 hp.1 p.2).2
  have hRc : ContinuousOn R (Icc l h) := by
    have hder : Continuous (deriv w) := (contDiff_infty_iff_deriv.mp hw).2.continuous
    exact ((hw.continuous.neg.mul hder).continuousOn.div continuousOn_id
      (fun r hr => (hl.trans_le hr.1).ne')).sqrt
  have hRstrip : ContinuousOn (fun p : PolarPoint => R p.1) (Icc l h ×ˢ univ) :=
    hRc.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hbc : ContinuousOn b (Icc l h ×ˢ univ) :=
    fun p hp => (hlocal p hp).1.continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc l h ×ˢ univ) :=
    fun p hp => (hlocal p hp).2.continuousAt.continuousWithinAt
  have hbd : ContinuousOn (angularPartial b) (Icc l h ×ˢ univ) := fun p hp =>
    (contDiffAt_angularPartial (hlocal p hp).1 (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hfd : ContinuousOn (angularPartial f) (Icc l h ×ˢ univ) := fun p hp =>
    (contDiffAt_angularPartial (hlocal p hp).2 (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have heq (p : PolarPoint) (hp : p ∈ Icc l h ×ˢ (univ : Set ℝ)) :
      minusCharacteristicSpeed
          ⟨polarLinearA w z, polarLinearB w z, polarCorrectedC w z⟩ p =
        b p - R p.1 * f p :=
    polarMinusCharacteristicSpeed_eq_separated z (hw.differentiable (by simp) p.1)
      (hl.trans_le hp.1.1).ne' (hadm p.1 hp.1 p.2).1 (hadm p.1 hp.1 p.2).2
  refine ⟨fun p => angularPartial b p - R p.1 * angularPartial f p,
    (hbc.sub (hRstrip.mul hfc)).congr heq, hbd.sub (hRstrip.mul hfd), ?_⟩
  intro r hr θ
  have hpoint := hlocal (r, θ) ⟨hr, mem_univ θ⟩
  have hbθ := hasDerivAt_angular_slice (hpoint.1.differentiableAt (by simp))
  have hfθ := hasDerivAt_angular_slice (hpoint.2.differentiableAt (by simp))
  have hder := hbθ.sub (hfθ.const_mul (R r))
  exact hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    heq (r, t) ⟨hr, mem_univ t⟩)

end ContinuousFlexibility.Statements
