import ContinuousFlexibility.Radial.InnerLiouvilleIntervalMeasure
import ContinuousFlexibility.Radial.InnerL2Restriction

/-!
# The normalized L² equivalence on a retained physical cell

The map sends u to sqrt(12*lam) * s * (R'/R) * u(R).
Surjectivity uses the genuine retained inverse coordinate, so the
construction also applies when the extended Morse radius turns outside
the retained interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff ENNReal

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

def innerLiouvilleIntervalPullback :
    Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (innerSquareDensityPullback (volume.restrict (Ioo a b))
    (innerLiouvilleIntervalAmplitude R s lam)
    (innerLiouvilleIntervalAmplitude_measurable hR hs lam)
    (innerLiouvilleIntervalAmplitude_ne_ae hlam hp)).comp
      (Lp.compMeasurePreservingₗᵢ ℝ R
        (innerLiouvilleInterval_measurePreserving D hab hlam hR hp hcore hw))

theorem innerLiouvilleIntervalPullback_ae
    (u : Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))) :
    (innerLiouvilleIntervalPullback D hab hlam hR hs hp hcore hw u : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioo a b)]
        (fun x => innerLiouvilleIntervalAmplitude R s lam x * u (R x)) := by
  let hmap := innerLiouvilleInterval_measurePreserving D hab hlam hR hp hcore hw
  have hcomp :
      (Lp.compMeasurePreservingₗᵢ ℝ R hmap u : ℝ → ℝ) =ᵐ[
        (volume.restrict (Ioo a b)).withDensity
          (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2))]
        (fun x => u (R x)) := by
    simpa only [Lp.compMeasurePreservingₗᵢ_apply, Function.comp_apply] using
      Lp.coeFn_compMeasurePreserving u hmap
  have hA := innerSquareDensityPullback_ae (volume.restrict (Ioo a b))
    (innerLiouvilleIntervalAmplitude R s lam)
    (innerLiouvilleIntervalAmplitude_measurable hR hs lam)
    (innerLiouvilleIntervalAmplitude_ne_ae hlam hp) (Lp.compMeasurePreservingₗᵢ ℝ R hmap u)
  have hc := (innerSquareDensity_base_ac (volume.restrict (Ioo a b))
    (innerLiouvilleIntervalAmplitude R s lam)
    (innerLiouvilleIntervalAmplitude_measurable hR hs lam)
    (innerLiouvilleIntervalAmplitude_ne_ae hlam hp)).ae_eq hcomp
  unfold innerLiouvilleIntervalPullback
  rw [LinearIsometry.coe_comp, Function.comp_apply]
  filter_upwards [hA, hc] with x hx hc'
  rw [hx, hc']

theorem innerLiouvilleIntervalPullback_surjective :
    Function.Surjective (innerLiouvilleIntervalPullback D hab hlam hR hs hp hcore hw) := by
  intro f
  let hf := (Lp.memLp f).aestronglyMeasurable
  let f₀ : ℝ → ℝ := hf.mk f
  have hf₀ : MemLp f₀ 2 (volume.restrict (Ioo a b)) :=
    MemLp.ae_eq hf.ae_eq_mk (Lp.memLp f)
  let X : ℝ → ℝ := morseCellModelCoordinate R a b
  let u : ℝ → ℝ := fun r => f₀ (X r) / innerLiouvilleIntervalAmplitude R s lam (X r)
  have hX : AEMeasurable X ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) :=
    (innerLiouvilleIntervalCoordinate_continuousOn hab hR
      (fun x hx => (hp x hx).2.1)).aemeasurable measurableSet_Ioo
  have hum : AEStronglyMeasurable u
      ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) :=
    ((hf.stronglyMeasurable_mk.measurable.comp_aemeasurable hX).div
      ((innerLiouvilleIntervalAmplitude_measurable hR hs lam).comp_aemeasurable hX)).
        aestronglyMeasurable
  have hmodel : (fun x => innerLiouvilleIntervalAmplitude R s lam x * u (R x)) =ᵐ[
      volume.restrict (Ioo a b)] f₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' := Ioo_subset_Icc_self hx
    dsimp only [u, X]
    rw [morseCellModelCoordinate_apply
      (morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)) hx']
    have hA := innerLiouvilleIntervalAmplitude_pos hlam
      (hp x hx').1 (hp x hx').2.1 (hp x hx').2.2
    field_simp [hA.ne']
  have hu : MemLp u 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) :=
    (innerLiouvilleInterval_memLp_iff D hab hlam hR hs hp hcore hw u hum).mpr
      (MemLp.ae_eq hmodel.symm hf₀)
  refine ⟨hu.toLp u, ?_⟩
  apply Lp.ext
  filter_upwards
    [innerLiouvilleIntervalPullback_ae D hab hlam hR hs hp hcore hw (hu.toLp u),
      innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw hu.coeFn_toLp,
      hmodel, hf.ae_eq_mk] with x hx hu' hm hf'
  rw [hx, hu', hm, ← hf']

def innerLiouvilleIntervalEquiv :
    Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  LinearIsometryEquiv.ofSurjective
    (innerLiouvilleIntervalPullback D hab hlam hR hs hp hcore hw)
    (innerLiouvilleIntervalPullback_surjective D hab hlam hR hs hp hcore hw)

theorem innerLiouvilleIntervalEquiv_ae
    (u : Lp ℝ 2 ((radialHilbertMeasure D).restrict (Ioo (R a) (R b)))) :
    (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw u : ℝ → ℝ) =ᵐ[
      volume.restrict (Ioo a b)]
        (fun x => innerLiouvilleIntervalAmplitude R s lam x * u (R x)) := by
  unfold innerLiouvilleIntervalEquiv
  rw [LinearIsometryEquiv.coe_ofSurjective]
  exact innerLiouvilleIntervalPullback_ae D hab hlam hR hs hp hcore hw u

theorem innerLiouvilleIntervalEquiv_symm_pullback_ae
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    (fun x => (innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm f (R x)) =ᵐ[
      volume.restrict (Ioo a b)]
        (fun x => f x / innerLiouvilleIntervalAmplitude R s lam x) := by
  have h := innerLiouvilleIntervalEquiv_ae D hab hlam hR hs hp hcore hw
    ((innerLiouvilleIntervalEquiv D hab hlam hR hs hp hcore hw).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h, innerLiouvilleIntervalAmplitude_ne_ae hlam hp] with x hx hn
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using hx.symm

end ContinuousFlexibility.Radial
