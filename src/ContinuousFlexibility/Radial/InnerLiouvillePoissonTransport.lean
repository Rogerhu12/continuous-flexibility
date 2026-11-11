import ContinuousFlexibility.Radial.InnerLiouvillePhysicalRepresentatives
import ContinuousFlexibility.Radial.InnerLiouvilleSmoothRepresentative

/-!
# Actual unit-boundary Poisson columns under Liouville transport

The column, its Lp class, its endpoint values and its scalar all use one
normalization. A radial unit boundary value is obtained by multiplying
the model pair by sqrt(lam)*s at that cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)

include hab hlam hR hs hp hcore hw in
theorem innerLiouvilleInterval_pushforward_ae {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f
      ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))))
    (hg : AEStronglyMeasurable g
      ((radialHilbertMeasure D).restrict (Ioo (R a) (R b))))
    (hfg : (fun x => f (R x)) =ᵐ[volume.restrict (Ioo a b)] (fun x => g (R x))) :
    f =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))] g := by
  have hfm := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw hf.ae_eq_mk
  have hgm := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw hg.ae_eq_mk
  have hm : (fun x => hf.mk f (R x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => hg.mk g (R x)) := hfm.symm.trans (hfg.trans hgm)
  have hm' := (withDensity_absolutelyContinuous (volume.restrict (Ioo a b))
    (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2))).ae_eq hm
  have hm'' : hf.mk f =ᵐ[Measure.map R ((volume.restrict (Ioo a b)).withDensity
      (fun x => ENNReal.ofReal (innerLiouvilleIntervalAmplitude R s lam x ^ 2)))] hg.mk g :=
    (ae_map_iff hR.continuous.measurable.aemeasurable
      (measurableSet_eq_fun hf.stronglyMeasurable_mk.measurable
        hg.stronglyMeasurable_mk.measurable)).mpr hm'
  rw [innerLiouvilleInterval_map_measure D hab hlam hR hp hcore hw] at hm''
  exact hf.ae_eq_mk.trans (hm''.trans hg.ae_eq_mk.symm)

variable (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleFieldLift_eq_indicator
    (f : Lp ℝ 2 (volume : Measure ℝ)) (p u : ℝ → ℝ)
    (hfp : (f : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p)
    (huc : ContinuousOn u (Icc (R a) (R b)))
    (hup : ∀ x ∈ Icc a b, u (R x) = p x / (Real.sqrt lam * s x)) :
    (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f : ℝ → ℝ) =ᵐ[
      radialHilbertMeasure D] (Ioo (R a) (R b)).indicator u := by
  have hlocal : (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f :
      ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo (R a) (R b))] u := by
    apply innerLiouvilleInterval_pushforward_ae D hab hlam hR hs hp hcore hw
      ((Lp.memLp _).restrict (Ioo (R a) (R b))).aestronglyMeasurable
      ((huc.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    filter_upwards
      [innerLiouvilleFieldLift_pullback_ae D hab hlam hR hs hp hcore hw U hU hv f,
        hfp, ae_restrict_mem measurableSet_Ioo] with x hx hfx hxi
    rw [hx, hfx, hup x (Ioo_subset_Icc_self hxi)]
  filter_upwards [ae_imp_of_ae_restrict hlocal,
    innerLiouvilleFieldLift_support_ae D hab hlam hR hs hp hcore hw U hU hv f] with r hi ho
  by_cases hr : r ∈ Ioo (R a) (R b)
  · rw [indicator_of_mem hr]
    exact hi hr
  · rw [indicator_of_notMem hr]
    exact ho hr

def innerLiouvilleUnitPoissonPair (t : ℝ) (P : Lp ℝ 2 (volume : Measure ℝ)) (scalar : ℝ) :
    Lp ℝ 2 (radialHilbertMeasure D) × ℝ :=
  (Real.sqrt lam * s t) •
    innerLiouvillePairLift D hab hlam hR hs hp hcore hw U hU hv (P, scalar)

theorem innerLiouvilleUnitPoissonPair_apply (t : ℝ) (P : Lp ℝ 2 (volume : Measure ℝ)) (scalar : ℝ) :
    innerLiouvilleUnitPoissonPair D hab hlam hR hs hp hcore hw U hU hv t P scalar =
      ((Real.sqrt lam * s t) •
        innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P,
        (Real.sqrt lam * s t) * scalar) := by
  unfold innerLiouvilleUnitPoissonPair
  rw [innerLiouvillePairLift_apply]
  apply Prod.ext
  · rw [Prod.smul_fst]
  · rw [Prod.smul_snd, smul_eq_mul]

/-- The representative has the true local formula at both closed
endpoints. Thus a model unit trace becomes exactly the same radial
unit trace, while the scalar is scaled by sqrt(lam)*s at that cut. -/
theorem exists_innerLiouvilleUnitPoissonRepresentative
    (t : ℝ) (ht : t ∈ Icc a b) (P : Lp ℝ 2 (volume : Measure ℝ)) (scalar : ℝ) (p : ℝ → ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hfp : (P : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] p) :
    ∃ u : ℝ → ℝ,
      (∀ x ∈ Icc a b, (fun y => u (R y)) =ᶠ[𝓝 x]
        (fun y => s t * p y / s y)) ∧
      (∀ r ∈ Icc (R a) (R b), ContDiffAt ℝ ∞ u r) ∧
      ((innerLiouvilleUnitPoissonPair D hab hlam hR hs hp hcore hw U hU hv
        t P scalar).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
          (Ioo (R a) (R b)).indicator u ∧
      u (R t) = p t ∧
      (innerLiouvilleUnitPoissonPair D hab hlam hR hs hp hcore hw U hU hv
        t P scalar).2 = Real.sqrt lam * s t * scalar := by
  obtain ⟨v, hnear, hreg⟩ :=
    exists_innerLiouvilleSmoothRepresentative hab hlam hR hs hp hpp
  let c := Real.sqrt lam * s t
  let u : ℝ → ℝ := fun r => c * v r
  have hu (x : ℝ) (hx : x ∈ Icc a b) :
      (fun y => u (R y)) =ᶠ[𝓝 x] (fun y => s t * p y / s y) := by
    have hsp : ∀ᶠ y in 𝓝 x, 0 < s y :=
      hs.continuous.continuousAt.eventually (lt_mem_nhds (hp x hx).2.2)
    filter_upwards [hnear x hx, hsp] with y hy hsy
    dsimp only [u, c]
    rw [hy]
    field_simp [(Real.sqrt_pos.mpr hlam).ne', hsy.ne']
    <;> ring
  have hvrep := innerLiouvilleFieldLift_eq_indicator D hab hlam hR hs hp hcore hw U hU hv
    P p v hfp (fun r hr => (hreg r hr).continuousAt.continuousWithinAt)
      (fun x hx => (hnear x hx).eq_of_nhds)
  refine ⟨u, hu, (fun r hr => contDiffAt_const.mul (hreg r hr)), ?_, ?_, ?_⟩
  · rw [innerLiouvilleUnitPoissonPair_apply]
    filter_upwards [Lp.coeFn_smul c
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P), hvrep] with r hc hv'
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    rw [hc, hv']
    by_cases hr : r ∈ Ioo (R a) (R b)
    · rw [indicator_of_mem hr, indicator_of_mem hr]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, mul_zero]
  · rw [(hu t ht).eq_of_nhds]
    exact mul_div_cancel_left₀ (p t) (hp t ht).2.2.ne'
  · rw [innerLiouvilleUnitPoissonPair_apply]

end ContinuousFlexibility.Radial
