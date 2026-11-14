import ContinuousFlexibility.Analysis.EquivariantOpenDomainStrip
import ContinuousFlexibility.Analysis.CanonicalSourceMeasure

/-!
# Source pairing on an actual open physical domain

The angular boundary line is null after intersection with any physical
set. The inverse-chart strip theorem identifies the actual image of one
angular period. The genuine Jacobian change of variables therefore gives
the same source pairing for curved physical pieces as for radial strips.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory

theorem openDomain_angular_Ioc_ae_eq_Ioo (Ω : Set PolarPoint) (a b : ℝ) :
    (Ω ∩ ((univ : Set ℝ) ×ˢ Ioc a b)) =ᵐ[volume]
      (Ω ∩ ((univ : Set ℝ) ×ˢ Ioo a b)) := by
  have hstrip : ((univ : Set ℝ) ×ˢ Ioc a b : Set PolarPoint) =ᵐ[volume]
      ((univ : Set ℝ) ×ˢ Ioo a b) :=
    Measure.set_prod_ae_eq Filter.EventuallyEq.rfl Ioo_ae_eq_Ioc.symm
  filter_upwards [hstrip] with p hp
  simp only [mem_inter_iff, hp]

/-- The exact height/Jacobian source factor preserves pairing on any
actual open domain with the indicated genuine equivariant inverse.
Integrability is not an extra premise: the totalized integral convention
is respected by the same actual change-of-variables theorem. -/
theorem integral_source_pairing_on_openDomain
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω)
    {a b P : ℝ} (hP : P ≠ 0)
    {F G : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    (hFmap : MapsTo F Ω (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGmap : MapsTo G (Ioo a b ×ˢ (univ : Set ℝ)) Ω)
    (hGF : ∀ p ∈ Ω, G (F p) = p)
    (hFG : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (G p) = p)
    (hGcont : ContinuousOn G (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGperiod : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (p + (0, P)) = G p + (0, P))
    (hGreflect : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ),
      G (p.1, -p.2) = ((G p).1, -(G p).2))
    (hFdiff : ∀ p ∈ Ω, DifferentiableAt ℝ F p)
    (hh : ∀ p ∈ Ω, h p ≠ 0) (hJ : ∀ p ∈ Ω, planeJacobian F p ≠ 0)
    (u f : PolarPoint → ℝ) :
    (∫ p in Ω ∩ (univ ×ˢ Ioc (0 : ℝ) P), u p * f p) =
      ∫ y in (Ioo a b ×ˢ (univ : Set ℝ)) ∩ (univ ×ˢ Ioc (0 : ℝ) P),
        (u (G y) / h (G y)) * (h (G y) * f (G y) / |planeJacobian F (G y)|) := by
  have himage := equivariantChart_image_openAngularStrip
    hP hFmap hGmap hGF hFG hGcont hGperiod hGreflect
  have hconv := integral_pairing_eq_canonical_of_image
    (hΩ.inter (isOpen_univ.prod isOpen_Ioo)).measurableSet
    (fun p hp => hFdiff p hp.1) (fun p hp => hGF p hp.1) himage
    (fun p hp => hh p hp.1) (fun p hp => hJ p hp.1) u f
  calc
    _ = ∫ p in Ω ∩ (univ ×ˢ Ioo (0 : ℝ) P), u p * f p :=
      setIntegral_congr_set (openDomain_angular_Ioc_ae_eq_Ioo Ω 0 P)
    _ = ∫ y in (Ioo a b ×ˢ (univ : Set ℝ)) ∩ (univ ×ˢ Ioo (0 : ℝ) P),
        (u (G y) / h (G y)) *
          (h (G y) * f (G y) / |planeJacobian F (G y)|) := hconv
    _ = _ := setIntegral_congr_set
      (openDomain_angular_Ioc_ae_eq_Ioo (Ioo a b ×ˢ (univ : Set ℝ)) 0 P).symm

end ContinuousFlexibility.Analysis
