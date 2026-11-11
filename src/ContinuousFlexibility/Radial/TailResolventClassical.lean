import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import ContinuousFlexibility.Radial.TailTestPairing

/-!
# Classical representatives of the weighted tail resolvent

The Friedrichs graph first gives a weak derivative for the function and a
second weak derivative identity for its weighted flux. Local integration
produces continuous representatives of both. A continuous source then gives
the actual first-order differential system on the open tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- Positive density gives exactly the same null sets on the open tail as
ordinary Lebesgue measure restricted to that interval. -/
theorem tail_ae_eq_iff_volume {T : DeepTailData} {v w : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x) :
    v =ᵐ[deepTailMeasure T] w ↔
      v =ᵐ[volume.restrict (Ioo T.entrance T.endpoint)] w := by
  change (∀ᵐ x ∂deepTailMeasure T, v x = w x) ↔ _
  rw [deepTailMeasure, ae_withDensity_iff' (tail_density_aemeasurable hp)]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with x hx hxin
    exact hx (ENNReal.ofReal_pos.mpr (hpos x hxin)).ne'
  · intro h
    filter_upwards [h] with x hx _
    exact hx

private theorem interval_pairing_congr {a b : ℝ} {φ v w : ℝ → ℝ}
    (hs : Function.support φ ⊆ Ioo a b)
    (hvw : v =ᵐ[volume.restrict (Ioo a b)] w) :
    (∫ x, v x * φ x) = ∫ x, w x * φ x := by
  have h := (ae_restrict_iff' measurableSet_Ioo).mp hvw
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxin : x ∈ Ioo a b
  · rw [hx hxin]
  · have hφ : φ x = 0 := Function.notMem_support.mp (fun h => hxin (hs h))
    simp only [hφ, mul_zero]

/-- Testing the form graph against `(φ, φ')` identifies the weak derivative
of the actual weighted flux. -/
theorem tailFriedrichs_weak_flux {T : DeepTailData} {d s : DeepTailL2 T}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hform : ∀ z ∈ TailFormLift T T.endpoint, ⟪s, z.1⟫_ℝ = ⟪d, z.2⟫_ℝ) :
    HasIntervalWeakDerivative T.entrance T.endpoint
      (fun x => T.p x * d x) (fun x => -(T.p x * s x)) := by
  intro φ hφ hc hs
  have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hds : tsupport (deriv φ) ⊆ Ioo T.entrance T.endpoint :=
    tsupport_deriv_subset.trans hs
  have hφLp := tail_test_memLp hp hpos hφ hc hs
  have hdLp := tail_test_memLp hp hpos hdφ hc.deriv hds
  have hcore : (hφLp.toLp φ, hdLp.toLp (deriv φ)) ∈
      TailEnergyCore T T.endpoint :=
    ⟨φ, hφ, hc, hs, MemLp.coeFn_toLp hφLp, MemLp.coeFn_toLp hdLp⟩
  have hpair := hform (hφLp.toLp φ, hdLp.toLp (deriv φ))
    (subset_closure hcore)
  change ⟪s, hφLp.toLp φ⟫_ℝ = ⟪d, hdLp.toLp (deriv φ)⟫_ℝ at hpair
  rw [tail_inner_right_of_ae s _ (MemLp.coeFn_toLp hφLp),
    tail_inner_right_of_ae d _ (MemLp.coeFn_toLp hdLp),
    tail_integral_mul_test hp hpos ((subset_tsupport φ).trans hs),
    tail_integral_mul_test hp hpos ((subset_tsupport (deriv φ)).trans hds)] at hpair
  calc
    (∫ x, (T.p x * d x) * deriv φ x) =
        ∫ x, d x * (T.p x * deriv φ x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = ∫ x, s x * (T.p x * φ x) := hpair.symm
    _ = -(∫ x, (-(T.p x * s x)) * φ x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring

/-- A resolvent graph solution with continuous source admits actual
continuously differentiable function and flux representatives. The density
only needs to be positive and smooth in the open interval. -/
theorem exists_tailResolvent_classical_rep_of_regular_density {T : DeepTailData}
    (hab : T.entrance < T.endpoint)
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hI : TailFormIdentification T T.endpoint)
    {u f : DeepTailL2 T} {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Ioo T.entrance T.endpoint))
    (hf : (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ)
    (hgraph : TailFriedrichsGraph T T.endpoint u (f + T.Λ • u)) :
    ∃ d : DeepTailL2 T, ∃ U Q : ℝ → ℝ,
      (u, d) ∈ TailFormLift T T.endpoint ∧
      ContinuousOn U (Ioo T.entrance T.endpoint) ∧
      ContinuousOn Q (Ioo T.entrance T.endpoint) ∧
      (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U ∧
      (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] Q ∧
      (∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x) ∧
      (∀ x ∈ Ioo T.entrance T.endpoint,
        HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x) := by
  obtain ⟨d, hud, hform⟩ := hgraph
  let s : DeepTailL2 T := f + T.Λ • u
  let x₀ : ℝ := (T.entrance + T.endpoint) / 2
  have hx₀ : x₀ ∈ Ioo T.entrance T.endpoint := by
    dsimp only [x₀]
    constructor <;> linarith
  have huLoc := tail_locallyIntegrableOn hp hpos u
  have hdLoc := tail_locallyIntegrableOn hp hpos d
  have hsLoc := tail_locallyIntegrableOn hp hpos s
  let Q₀ : ℝ → ℝ := fun x => T.p x * d x
  let H : ℝ → ℝ := fun x => -(T.p x * s x)
  have hQ₀Loc : LocallyIntegrableOn Q₀ (Ioo T.entrance T.endpoint) :=
    hdLoc.continuousOn_mul hp.continuousOn isOpen_Ioo.isLocallyClosed
  have hHLoc : LocallyIntegrableOn H (Ioo T.entrance T.endpoint) :=
    (hsLoc.continuousOn_mul hp.continuousOn isOpen_Ioo.isLocallyClosed).neg
  have hflux : HasIntervalWeakDerivative T.entrance T.endpoint Q₀ H :=
    tailFriedrichs_weak_flux hp hpos hform
  obtain ⟨cQ, hQae⟩ := exists_intervalWeakPrimitive_rep hQ₀Loc hHLoc hx₀ hflux
  let Q : ℝ → ℝ := fun x => cQ + intervalWeakPrimitive x₀ H x
  have hQae' : Q₀ =ᵐ[volume.restrict (Ioo T.entrance T.endpoint)] Q := hQae
  have hQcont : ContinuousOn Q (Ioo T.entrance T.endpoint) :=
    continuousOn_const.add (continuousOn_intervalWeakPrimitive hHLoc hx₀)
  let D : ℝ → ℝ := fun x => Q x / T.p x
  have hDcont : ContinuousOn D (Ioo T.entrance T.endpoint) :=
    hQcont.div hp.continuousOn (fun x hx => (hpos x hx).ne')
  have hdAE : (d : ℝ → ℝ) =ᵐ[volume.restrict (Ioo T.entrance T.endpoint)] D := by
    filter_upwards [hQae', ae_restrict_mem measurableSet_Ioo] with x hx hxin
    apply (eq_div_iff (hpos x hxin).ne').mpr
    simpa only [Q₀, mul_comm] using hx
  have huWeak : HasIntervalWeakDerivative T.entrance T.endpoint
      (u : ℝ → ℝ) D := by
    intro φ hφ hc hs
    have hw := hI.1 u d hud φ hφ hc hs
    rw [interval_pairing_congr ((subset_tsupport φ).trans hs) hdAE] at hw
    exact hw
  obtain ⟨cU, U, hUformula, huAE, hUd⟩ :=
    exists_interval_classical_rep huLoc hDcont hx₀ huWeak
  have hUcont : ContinuousOn U (Ioo T.entrance T.endpoint) :=
    fun x hx => (hUd x hx).continuousAt.continuousWithinAt
  let Hc : ℝ → ℝ := fun x => -(T.p x * (ψ x + T.Λ * U x))
  have hHccont : ContinuousOn Hc (Ioo T.entrance T.endpoint) :=
    (hp.continuousOn.mul (hψ.add (continuousOn_const.mul hUcont))).neg
  have hsAE : (s : ℝ → ℝ) =ᵐ[deepTailMeasure T]
      fun x => ψ x + T.Λ * u x := by
    filter_upwards [Lp.coeFn_add f (T.Λ • u), Lp.coeFn_smul T.Λ u, hf]
      with x hAdd hSmul hfx
    change s x = ψ x + T.Λ * u x
    change (f + T.Λ • u) x = f x + (T.Λ • u) x at hAdd
    change (T.Λ • u) x = T.Λ * u x at hSmul
    exact hAdd.trans (by rw [hSmul, hfx])
  have hHAE : H =ᵐ[volume.restrict (Ioo T.entrance T.endpoint)] Hc := by
    filter_upwards [(tail_ae_eq_iff_volume hp hpos).mp hsAE, huAE] with x hsx hux
    dsimp only [H, Hc]
    rw [hsx, hux]
  have hQformula (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      Q x = cQ + intervalWeakPrimitive x₀ Hc x := by
    dsimp only [Q, intervalWeakPrimitive]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hHAE] with t ht htin
    exact ht ((ordConnected_Ioo.uIcc_subset hx₀ hx) (uIoc_subset_uIcc htin))
  have hQd (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x := by
    have hclass : HasDerivAt (fun y => cQ + intervalWeakPrimitive x₀ Hc y) (Hc x) x := by
      exact (hasDerivAt_intervalWeakPrimitive hHccont hx₀ hx).const_add cQ
    apply hclass.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hQformula y hy
  exact ⟨d, U, Q, hud, hUcont, hQcont,
    (tail_ae_eq_iff_volume hp hpos).mpr huAE,
    (tail_ae_eq_iff_volume hp hpos).mpr hQae', hUd, hQd⟩

/-- The complete deep-tail hypotheses supply the positive regular density
needed to recover a classical resolvent representative. -/
theorem exists_tailResolvent_classical_rep {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hI : TailFormIdentification T T.endpoint)
    {u f : DeepTailL2 T} {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Ioo T.entrance T.endpoint))
    (hf : (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ)
    (hgraph : TailFriedrichsGraph T T.endpoint u (f + T.Λ • u)) :
    ∃ d : DeepTailL2 T, ∃ U Q : ℝ → ℝ,
      (u, d) ∈ TailFormLift T T.endpoint ∧
      ContinuousOn U (Ioo T.entrance T.endpoint) ∧
      ContinuousOn Q (Ioo T.entrance T.endpoint) ∧
      (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U ∧
      (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] Q ∧
      (∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x) ∧
      (∀ x ∈ Ioo T.entrance T.endpoint,
        HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x) := by
  rcases hT with ⟨hab, _, _, _, _, _, _, hp, hpos, _, _⟩
  exact exists_tailResolvent_classical_rep_of_regular_density hab
    (hp.mono Ioo_subset_Ico_self) (fun x hx => hpos x (Ioo_subset_Ico_self hx))
    hI hψ hf hgraph

/-- The recovered function has the original form derivative and its
classical flux is the continuous representative furnished above. -/
theorem tail_classical_rep_derivative {T : DeepTailData} {d : DeepTailL2 T}
    {U Q : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hQ : (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] Q)
    (hU : ∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x) :
    (d : ℝ → ℝ) =ᵐ[deepTailMeasure T] deriv U ∧
      (∀ x ∈ Ioo T.entrance T.endpoint, T.p x * deriv U x = Q x) := by
  have hflux (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      T.p x * deriv U x = Q x := by
    rw [(hU x hx).deriv]
    exact mul_div_cancel₀ _ (hpos x hx).ne'
  refine ⟨(tail_ae_eq_iff_volume hp hpos).mpr ?_, hflux⟩
  filter_upwards [(tail_ae_eq_iff_volume hp hpos).mp hQ,
    ae_restrict_mem measurableSet_Ioo] with x hx hxin
  exact mul_left_cancel₀ (hpos x hxin).ne' (hx.trans (hflux x hxin).symm)

/-- The flux representative is the derivative of the actual classical
flux, so the first-order system is the original weighted equation. -/
theorem tail_classical_flux_hasDerivAt {T : DeepTailData} {U Q ψ : ℝ → ℝ}
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hU : ∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x)
    (hQ : ∀ x ∈ Ioo T.entrance T.endpoint,
      HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x)
    {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    HasDerivAt (fun y => T.p y * deriv U y) (-(T.p x * (ψ x + T.Λ * U x))) x := by
  apply (hQ x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  change T.p y * deriv U y = Q y
  rw [(hU y hy).deriv]
  exact mul_div_cancel₀ _ (hpos y hy).ne'

theorem tail_classical_rep_equation {T : DeepTailData} {U Q ψ : ℝ → ℝ}
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hU : ∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x)
    (hQ : ∀ x ∈ Ioo T.entrance T.endpoint,
      HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x)
    {x : ℝ} (hx : x ∈ Ioo T.entrance T.endpoint) :
    deriv (fun y => T.p y * deriv U y) x + T.Λ * T.p x * U x = -(T.p x * ψ x) := by
  rw [(tail_classical_flux_hasDerivAt hpos hU hQ hx).deriv]
  ring

end ContinuousFlexibility.Radial
