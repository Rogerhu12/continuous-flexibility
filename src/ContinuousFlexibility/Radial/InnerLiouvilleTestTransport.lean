import ContinuousFlexibility.Radial.InnerLiouvilleCompactTest

/-!
# Every actual compact physical test comes from an actual model test

The normalized pullback is smooth with compact support in the retained
model interval. Its true derivative cancels the density drift in the
gradient lift. Thus both coordinates of the physical test are images
of the same original Schrodinger energy-core vector.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerLiouvilleTestPullback_closed {R s φ : ℝ → ℝ} {a b lam x : ℝ}
    (hφs : tsupport φ ⊆ Ioo (R a) (R b)) (hx : x ∈ Icc a b) :
    innerLiouvilleTestPullback R s a b lam φ x = Real.sqrt lam * s x * φ (R x) := by
  by_cases hi : x ∈ Ioo a b
  · exact indicator_of_mem hi _
  · have he : x = a ∨ x = b := by
      by_contra hn
      have hxa : x ≠ a := fun h => hn (Or.inl h)
      have hxb : x ≠ b := fun h => hn (Or.inr h)
      exact hi ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    have hz : φ (R x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hRx := hφs h
      rcases he with rfl | rfl
      · exact (lt_irrefl (R a)) hRx.1
      · exact (lt_irrefl (R b)) hRx.2
    rw [innerLiouvilleTestPullback, indicator_of_notMem hi, hz, mul_zero]

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

theorem innerLiouvilleGradientLift_testPullback {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {f d : RadialL2}
    (hf : (f : ℝ → ℝ) =ᵐ[volume] innerLiouvilleTestPullback R s a b lam φ)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] deriv (innerLiouvilleTestPullback R s a b lam φ)) :
    (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] (Ioo (R a) (R b)).indicator (innerGapGradientField φ) := by
  have hlocal : (innerLiouvilleGradientLift D hab hlam hR hs hp hcore hw (f, d) :
      ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))]
        innerGapGradientField φ := by
    apply innerLiouvilleInterval_pushforward_ae D hab hlam hR hs hp hcore hw
      ((Lp.memLp _).restrict (Ioo (R a) (R b))).aestronglyMeasurable
      (innerGapGradientField_continuous hφ).aestronglyMeasurable
    filter_upwards [innerLiouvilleGradientLift_pullback_ae D hab hlam hR hs hp hcore hw f d,
      ae_restrict_of_ae hf, ae_restrict_of_ae hd,
      ae_restrict_mem measurableSet_Ioo] with x hg hfx hdx hx
    have hx' := Ioo_subset_Icc_self hx
    rw [hg, hfx, hdx, innerLiouvilleTestPullback_deriv
      (hR.differentiable (by simp) x) (hs.differentiable (by simp) x)
      (hφ.differentiable (by simp) (R x)) hx,
      innerLiouvilleTestPullback, indicator_of_mem hx,
      innerLiouvilleIntervalAmplitude, innerGapGradientField,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne',
      (Real.sqrt_pos.mpr hlam).ne', (hp x hx').1.ne',
      (hp x hx').2.1.ne', (hp x hx').2.2.ne']
    <;> ring
  filter_upwards [ae_imp_of_ae_restrict hlocal,
    innerLiouvilleGradientLift_support_ae D hab hlam hR hs hp hcore hw f d] with r hi ho
  by_cases hr : r ∈ Ioo (R a) (R b)
  · rw [indicator_of_mem hr]
    exact hi hr
  · rw [indicator_of_notMem hr]
    exact ho hr

variable (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

/-- The inverse test construction includes both actual energy
coordinates. There is no assumed density or test-pullback axiom. -/
theorem innerRadialH1Core_energyLift_preimage {V : ℝ → ℝ} (hV : Continuous V)
    {Q : InnerRadialH1Pair D} (hQ : Q ∈ InnerRadialH1Core D (R a) (R b)) :
    ∃ q : RadialL2 × RadialL2 × RadialL2,
      q ∈ IntervalEnergyCore V a b ∧
        innerLiouvilleEnergyLift D hab hlam hR hs hp hcore hw U hU hv q = Q := by
  rcases hQ with ⟨φ, hφ, hcφ, hφs, hQv, hQd⟩
  have hcomp := innerLiouvilleTestPullback_compact (s := s) (lam := lam)
    hab hR (fun x hx => (hp x hx).2.1) hcφ hφs
  have hsm := innerLiouvilleTestPullback_contDiff (lam := lam) hab hR hs
    (fun x hx => (hp x hx).2.1) hφ hcφ hφs
  obtain ⟨⟨f, d, q⟩, hq, hf, hd⟩ := exists_innerCompactModelEnergyCore hV hsm hcomp.1 hcomp.2
  have hfield := innerLiouvilleFieldLift_eq_indicator D hab hlam hR hs hp hcore hw U hU hv
    f (innerLiouvilleTestPullback R s a b lam φ) φ (ae_restrict_of_ae hf)
    hφ.continuous.continuousOn (fun x hx => by
      rw [innerLiouvilleTestPullback_closed hφs hx]
      field_simp [(Real.sqrt_pos.mpr hlam).ne', (hp x hx).2.2.ne'])
  have hgrad := innerLiouvilleGradientLift_testPullback D hab hlam hR hs hp hcore hw hφ hf hd
  refine ⟨(f, d, q), hq, ?_⟩
  rw [innerLiouvilleEnergyLift_apply]
  exact Prod.ext (Lp.ext (hfield.trans hQv.symm)) (Lp.ext (hgrad.trans hQd.symm))

end ContinuousFlexibility.Radial
