module

public import ContinuousFlexibility.Radial.OuterPhysicalRobinSolution
public import ContinuousFlexibility.Radial.MatchingGraphRestrictions

/-!
# The original Jacobi pairing of the weak Robin graph

The first-order weak flux equation is converted to the original
second-order Jacobi expression by integration by parts.  The final
identity uses the actual L² representative and the physical density,
for every smooth test compactly supported in the open outer interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem outer_flux_weak_jacobi_pairing
    {a b J : ℝ} {w ρ u q f : ℝ → ℝ} (hab : a < b)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hκ : ContinuousOn (fun x => J * deriv w x / x) (Ioo a b))
    (hf : LocallyIntegrableOn (fun x => ρ x * f x) (Ioo a b))
    (hq : ∀ x ∈ Ioo a b, q x = w x * deriv u x)
    (hweak : HasIntervalWeakDerivative a b q
      (fun x => J * deriv w x / x * u x - ρ x * f x))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, u x * radialJacobi J w ψ x) = -(∫ x, ρ x * f x * ψ x) := by
  have hdu : HasIntervalWeakDerivative a b u (deriv u) := by
    apply hasIntervalWeakDerivative_of_locallyAC_ae hab
    · intro l hl r hr
      exact (hu.mono (ordConnected_Ioo.uIcc_subset hl hr)).absolutelyContinuousOnInterval
    · intro l hl r hr
      exact Eventually.of_forall fun x hx =>
        ((hu.contDiffAt (isOpen_Ioo.mem_nhds
          (ordConnected_Ioo.uIcc_subset hl hr hx))).differentiableAt (by norm_num)).hasDerivAt
  let φ : ℝ → ℝ := fun x => w x * deriv ψ x
  have hφ : ContDiff ℝ ∞ φ := hw.mul (contDiff_infty_iff_deriv.mp hψ).2
  have hcφ : HasCompactSupport φ := hc.deriv.mul_left
  have hsφ : tsupport φ ⊆ Ioo a b :=
    tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hs)
  have hparts := hdu φ hφ hcφ hsφ
  have hflux : (∫ x, deriv u x * φ x) = ∫ x, q x * deriv ψ x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change deriv u x * φ x = q x * deriv ψ x
    by_cases hx : x ∈ Ioo a b
    · rw [hq x hx]
      dsimp only [φ]
      ring
    · have hz : deriv ψ x = 0 := deriv_of_notMem_tsupport (fun h => hx (hs h))
      simp only [φ, hz, mul_zero]
  rw [hflux, hweak ψ hψ hc hs, neg_neg] at hparts
  have hpot := interval_integrable_mul_test
    ((hκ.mul hu.continuousOn).locallyIntegrableOn measurableSet_Ioo) hψ.continuous hc hs
  have hsource := interval_integrable_mul_test hf hψ.continuous hc hs
  have hprincipal := interval_integrable_mul_test
    (hu.continuousOn.locallyIntegrableOn measurableSet_Ioo)
    (contDiff_infty_iff_deriv.mp hφ).2.continuous hcφ.deriv
    (tsupport_deriv_subset.trans hsφ)
  have hsplit :
      (∫ x, (J * deriv w x / x * u x - ρ x * f x) * ψ x) =
        (∫ x, (J * deriv w x / x * u x) * ψ x) - ∫ x, ρ x * f x * ψ x := by
    simp_rw [sub_mul]
    exact integral_sub hpot hsource
  calc
    _ = ∫ x, u x * deriv φ x - (J * deriv w x / x * u x) * ψ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [radialJacobi, φ]
        ring
    _ = (∫ x, u x * deriv φ x) - ∫ x, (J * deriv w x / x * u x) * ψ x :=
      integral_sub hprincipal hpot
    _ = _ := by rw [hparts, hsplit]; ring

/-- The graph equation is the original physical Jacobi equation paired
against compact interior tests.  The left side uses the actual Hilbert
space element, not an assumed classical source or a separate solution. -/
theorem OuterRobinWeakGraph.physical_jacobi_pairing
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {entry J lam : ℝ} (hentry : entry ∈ radialCore D)
    {v : ℝ × ℝ} {U f : OuterWholeL2 D right entry}
    (hgraph : OuterRobinWeakGraph (outerWholeMeasure D right entry)
      (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) J lam
      (outerTailOutwardWeight D right) (outerWholeDensity D right) v U f)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) :
    (∫ x in (outerOutwardRadius right entry)..
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
      U x * radialJacobi J (outerTailOutwardWeight D right) ψ x) =
      -(∫ x in (outerOutwardRadius right entry)..
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
          outerWholeDensity D right x * f x * ψ x) := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let w := outerTailOutwardWeight D right
  obtain ⟨u, q, hae, hu, _, hq, heq, _⟩ := hgraph
  have hab : a < b := outerWhole_interval hentry
  have hw : ContDiff ℝ ∞ w := outerWhole_weight_smooth (matchingProfileGeometry hD) right
  have hκ : ContinuousOn (fun x => J * deriv w x / x) (Ioo a b) :=
    (continuousOn_const.mul
      (contDiff_infty_iff_deriv.mp hw).2.continuous.continuousOn).div continuousOn_id
        (fun x hx => outerWhole_coordinate_ne_zero (matchingProfileGeometry hD)
          hentry (Ioo_subset_Ico_self hx))
  have hf : LocallyIntegrableOn (fun x => outerWholeDensity D right x * f x) (Ioo a b) := by
    have hsource : LocallyIntegrableOn
        (fun x => -(-(outerWholeDensity D right x * f x))) (Ioo a b) :=
      (outerWholeSource_integrable hD hentry f).neg.locallyIntegrableOn
    simpa only [neg_neg] using hsource
  have hqo : ∀ x ∈ Ioo a b, q x = w x * deriv u x := by
    intro x hx
    rw [hq x (Ioo_subset_Ico_self hx), derivWithin_of_mem_nhds
      (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Ico_self)]
  have hpair := outer_flux_weak_jacobi_pairing hab hw (hu.mono Ioo_subset_Ico_self)
    hκ hf hqo heq hψ hc hs
  have hsupport : Function.support (radialJacobi J w ψ) ⊆ Ioo a b := by
    intro x hx
    by_contra hn
    exact hx (matching_radialJacobi_eq_zero_of_notMem_tsupport (fun h => hn (hs h)) w J)
  have hsourceSupport : Function.support
      (fun x => outerWholeDensity D right x * f x * ψ x) ⊆ Ioc a b :=
    (Function.support_mul_subset_right _ ψ).trans
      ((subset_tsupport ψ).trans (hs.trans Ioo_subset_Ioc_self))
  calc
    (∫ x in a..b, U x * radialJacobi J w ψ x) =
        ∫ x in a..b, u x * radialJacobi J w ψ x := by
      simp only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [(outerWholeMeasure_ae_iff hD hentry).mp hae] with x hx
      rw [hx]
    _ = ∫ x, u x * radialJacobi J w ψ x :=
      intervalIntegral.integral_eq_integral_of_support_subset
        ((Function.support_mul_subset_right u _).trans (hsupport.trans Ioo_subset_Ioc_self))
    _ = -(∫ x, outerWholeDensity D right x * f x * ψ x) := hpair
    _ = _ := by rw [intervalIntegral.integral_eq_integral_of_support_subset hsourceSupport]

end ContinuousFlexibility.Radial
