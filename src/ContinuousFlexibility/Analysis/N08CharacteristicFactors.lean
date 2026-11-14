module

public import ContinuousFlexibility.Analysis.N08ControlLocality
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Angular regularity of the actual characteristic speed

The square root that can lose radial differentiability is a function of
the radius alone.  Its angular factors are smooth on the geometric domain.
Compact rectangles therefore give genuine Lipschitz bounds in angle even
when the rectangle includes a turning point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

def n08JacobiMinusSpeed (w : ℝ → ℝ) (h : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  polarLinearB w h p / polarLinearA w h p -
    Real.sqrt (polarLinearB w h p ^ 2 - polarLinearA w h p * polarCorrectedC w h p) /
      polarLinearA w h p

def n08CharacteristicDrift (w : ℝ → ℝ) (h : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  polarLinearB w h p / polarLinearA w h p

def n08CharacteristicFactor (w : ℝ → ℝ) (h : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  Real.sqrt (polarDiscriminant w h p) /
    heightQ (profileEnergy w p) (heightRadial h p) (angularPartial (heightAngular h) p)

theorem n08JacobiMinusSpeed_eq_factors {w : ℝ → ℝ} {h : PolarPoint → ℝ}
    {p : PolarPoint} (hw : DifferentiableAt ℝ w p.1) (hr : p.1 ≠ 0)
    (hD : 0 < polarDiscriminant w h p)
    (hQ : 0 < heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p)) :
    n08JacobiMinusSpeed w h p = n08CharacteristicDrift w h p -
      Real.sqrt (-w p.1 * deriv w p.1 / p.1) * n08CharacteristicFactor w h p := by
  have hdet := polar_corrected_determinant h hw hr hD hQ.ne'
  have hrad : polarLinearB w h p ^ 2 - polarLinearA w h p * polarCorrectedC w h p =
      (-w p.1 * deriv w p.1 / p.1) / polarDiscriminant w h p ^ 2 := by
    calc
      _ = -((w p.1 * deriv w p.1 / p.1) / polarDiscriminant w h p ^ 2) := by
        linarith only [hdet]
      _ = _ := by ring
  have hsqrt :
      Real.sqrt (polarLinearB w h p ^ 2 - polarLinearA w h p * polarCorrectedC w h p) =
        Real.sqrt (-w p.1 * deriv w p.1 / p.1) / polarDiscriminant w h p := by
    rw [hrad, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hD.le]
  unfold n08JacobiMinusSpeed n08CharacteristicDrift n08CharacteristicFactor
  rw [hsqrt]
  congr 1
  unfold polarLinearA linearRadial polarScale inverseDThreeHalves
  field_simp [hD.ne', hQ.ne', (Real.sqrt_pos.mpr hD).ne']
  <;> ring

theorem n08_contDiffAt_characteristicFactors {w : ℝ → ℝ} {h : PolarPoint → ℝ}
    {p : PolarPoint} (hw : ContDiffAt ℝ ∞ w p.1) (hh : ContDiffAt ℝ ∞ h p)
    (hr : p.1 ≠ 0) (hD : 0 < polarDiscriminant w h p)
    (hQ : 0 < heightQ (profileEnergy w p) (heightRadial h p)
      (angularPartial (heightAngular h) p)) :
    ContDiffAt ℝ ∞ (n08CharacteristicDrift w h) p ∧
      ContDiffAt ℝ ∞ (n08CharacteristicFactor w h) p := by
  have hc := contDiffAt_heightLinearCoefficients hw hh hr hD hQ.ne'
  have ha : 0 < polarLinearA w h p := mul_pos hQ (inverseDThreeHalves_pos _ hD)
  refine ⟨hc.2.1.div hc.1 ha.ne', ?_⟩
  have hE : ContDiffAt ℝ ∞ (profileEnergy w) p :=
    contDiffAt_const.add ((hw.comp p contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial hh (m := ∞) (by simp)
  have hp := contDiffAt_heightAngular hh (m := ∞) (by simp) hr
  have hpt := contDiffAt_angularPartial hp (m := ∞) (by simp)
  have hd : ContDiffAt ℝ ∞ (polarDiscriminant w h) p :=
    (hE.mul (contDiffAt_const.sub (hp.pow 2))).sub (hk.pow 2)
  exact (hd.sqrt hD.ne').div (hk.add (hE.mul hpt)) hQ.ne'

/-- The needed angle bound is on the actual speed, with an ordinary finite
constant on any compact rectangle in the geometric domain. -/
theorem n08JacobiMinusSpeed_angle_bound {w : ℝ → ℝ} {h : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h) {a b c d : ℝ} (ha : 0 < a)
    (hD : ∀ p ∈ Icc a b ×ˢ Icc c d, 0 < polarDiscriminant w h p)
    (hQ : ∀ p ∈ Icc a b ×ˢ Icc c d,
      0 < heightQ (profileEnergy w p) (heightRadial h p)
        (angularPartial (heightAngular h) p)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ θ ∈ Icc c d, ∀ φ ∈ Icc c d,
      |n08JacobiMinusSpeed w h (t, θ) - n08JacobiMinusSpeed w h (t, φ)| ≤ K * |θ - φ| := by
  let A : PolarPoint → ℝ := n08CharacteristicDrift w h
  let B : PolarPoint → ℝ := n08CharacteristicFactor w h
  let v : ℝ → ℝ := fun t => Real.sqrt (-w t * deriv w t / t)
  let G : PolarPoint → ℝ := fun p => A p - v p.1 * B p
  let Gθ : PolarPoint → ℝ := fun p => angularPartial A p - v p.1 * angularPartial B p
  let I : Set PolarPoint := Icc a b ×ˢ Icc c d
  have hreg (p : PolarPoint) (hp : p ∈ I) :
      ContDiffAt ℝ ∞ A p ∧ ContDiffAt ℝ ∞ B p :=
    n08_contDiffAt_characteristicFactors hw.contDiffAt hh.contDiffAt
      (ha.trans_le hp.1.1).ne' (hD p hp) (hQ p hp)
  have hv : ContinuousOn (fun p : PolarPoint => v p.1) I := by
    have hwd := (contDiff_infty_iff_deriv.mp hw).2.continuous
    exact (((hw.continuous.comp continuous_fst).neg.mul
      (hwd.comp continuous_fst)).continuousOn.div continuous_fst.continuousOn
        (fun p hp => (ha.trans_le hp.1.1).ne')).sqrt
  have hA : ContinuousOn (angularPartial A) I := fun p hp =>
    (contDiffAt_angularPartial (hreg p hp).1 (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hB : ContinuousOn (angularPartial B) I := fun p hp =>
    (contDiffAt_angularPartial (hreg p hp).2 (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hGθ : ContinuousOn Gθ I := hA.sub (hv.mul hB)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hGθ
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht θ hθ φ hφ
  have hder (η : ℝ) (hη : η ∈ Icc c d) :
      HasDerivAt (fun ξ => G (t, ξ)) (Gθ (t, η)) η := by
    have hdA := hasDerivAt_angular_slice ((hreg (t, η) ⟨ht, hη⟩).1.differentiableAt (by simp))
    have hdB := hasDerivAt_angular_slice ((hreg (t, η) ⟨ht, hη⟩).2.differentiableAt (by simp))
    exact hdA.sub (hdB.const_mul (v t))
  have hbound (η : ℝ) (hη : η ∈ Icc c d) : ‖Gθ (t, η)‖ ≤ max M 0 :=
    (hM (t, η) ⟨ht, hη⟩).trans (le_max_left _ _)
  have hm := (convex_Icc c d).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun η hη => (hder η hη).hasDerivWithinAt) hbound hφ hθ
  have heq (η : ℝ) (hη : η ∈ Icc c d) : n08JacobiMinusSpeed w h (t, η) = G (t, η) :=
    n08JacobiMinusSpeed_eq_factors (hw.differentiable (by simp) t)
      (ha.trans_le ht.1).ne' (hD (t, η) ⟨ht, hη⟩) (hQ (t, η) ⟨ht, hη⟩)
  rw [heq θ hθ, heq φ hφ]
  simpa only [Real.norm_eq_abs] using hm

end ContinuousFlexibility.Statements
