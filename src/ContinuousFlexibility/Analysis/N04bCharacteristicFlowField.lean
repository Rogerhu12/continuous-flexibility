import ContinuousFlexibility.Analysis.N04bCharacteristicFlowOriginal
import ContinuousFlexibility.Analysis.N04bCharacteristicFlowInterior
import ContinuousFlexibility.Analysis.N04bActualCharacteristics
import ContinuousFlexibility.Analysis.N04bRootGermCollar
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# The actual corrected field supplies the stored-flow regularity hypotheses

Strict hyperbolicity gives smoothness in each open negative component.
At its two endpoints, the genuine N03 coefficient germs identify the
actual speed with the original N01 speed. The preceding angular-jet
lemmas therefore patch every angular jet continuously across the closed
component. Applying the actual ODE theorems proves regularity of the same
stored N03 flow; no forward regularity is added to N03.

`N04bFieldRegularity` remains an explicitly named construction obligation.
This file derives the flow consequences of that raw-field property and
does not assert its realization by an arbitrary N03 witness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- This is a certificate about the actual scalar speed, proved solely
from raw coefficient regularity and the existing N01--N03 data. -/
theorem n04b_actualMinusField_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    N04bScalarFieldRegularity (minusCharacteristicSpeed (L.coefficients z))
      (C.left m) (C.right m) Real.pi := by
  have hN01 : N01Properties D T S C base loss ε := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hab : C.left m < C.right m := (hcontrol.1 m).2.1
  have hI : Icc (C.left m) (C.right m) ⊆ Ioo D.a D.b :=
    fun r hr => ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  have hcore {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      p ∈ annularOpen D := ⟨hI hp, mem_univ _⟩
  let F := minusCharacteristicSpeed (L.coefficients z)
  have hinterior : ContDiffOn ℝ ∞ F
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    exact (n04b_corrected_characteristics_contDiffAt hN hfield hz hsector m hp).2.2.1.contDiffWithinAt
  have hrootMatch {p : PolarPoint} (hp : p ∈ annularOpen D)
      (hroot : deriv D.w p.1 = 0) :
      F =ᶠ[𝓝 p] minusCharacteristicSpeed (originalCoefficients D S C z) := by
    obtain ⟨δ, hδ, hc⟩ :=
      n04b_through03_root_coefficient_collar hS hN hfield hz hsector hp.1 hroot
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, |q.1 - p.1| < δ :=
      (continuous_fst.sub continuous_const).abs.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (by simpa only [Pi.sub_apply, sub_self, abs_zero] using hδ))
    filter_upwards [hnear] with q hq
    obtain ⟨_, ha, hb, hc⟩ := hc q.1 q.2 hq
    dsimp only [F, minusCharacteristicSpeed]
    rw [ha, hb, hc]
  have hrootAngle {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m))
      (hroot : deriv D.w r = 0) (θ : ℝ) :
      ContDiffAt ℝ ∞ (fun η => F (r, η)) θ := by
    have he := hrootMatch (p := (r, θ)) (hcore hr) hroot
    have hg := hN01.minusCharacteristicSpeed_angular_contDiff hS hT hz hsector (hI hr)
    apply hg.contDiffAt.congr_of_eventuallyEq
    exact (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually he
  have hs : ∀ r ∈ Icc (C.left m) (C.right m), ContDiff ℝ ∞ (fun θ => F (r, θ)) := by
    intro r hr
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    by_cases hleft : r = C.left m
    · exact hrootAngle hr (by simpa only [hleft] using (hcontrol.2.1 m).1) θ
    by_cases hright : r = C.right m
    · exact hrootAngle hr (by simpa only [hright] using (hcontrol.2.1 m).2.1) θ
    have hi : r ∈ Ioo (C.left m) (C.right m) :=
      ⟨lt_of_le_of_ne hr.1 (Ne.symm hleft), lt_of_le_of_ne hr.2 hright⟩
    have hp : (r, θ) ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨hi, mem_univ _⟩
    exact (hinterior.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).comp θ
      (contDiffAt_const.prodMk contDiffAt_id)
  have hrootJet {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m))
      (hroot : deriv D.w p.1 = 0) (n : ℕ) :
      ContinuousAt (fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2) p := by
    have he := hrootMatch (hcore hp) hroot
    exact (hN01.minusCharacteristicSpeed_angularJet_continuousAt hS hT hz hsector
      (hcore hp) n).congr_of_eventuallyEq (n04b_angularJet_eventuallyEq he n)
  have hj : ∀ n : ℕ,
      ContinuousOn (fun p : PolarPoint => iteratedDeriv n (fun θ => F (p.1, θ)) p.2)
        (Icc (C.left m) (C.right m) ×ˢ univ) := by
    intro n p hp
    by_cases hleft : p.1 = C.left m
    · exact (hrootJet hp.1
        (by simpa only [hleft] using (hcontrol.2.1 m).1) n).continuousWithinAt
    by_cases hright : p.1 = C.right m
    · exact (hrootJet hp.1
        (by simpa only [hright] using (hcontrol.2.1 m).2.1) n).continuousWithinAt
    have hi : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
      ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hleft), lt_of_le_of_ne hp.1.2 hright⟩, hp.2⟩
    have hc : ContinuousAt (mixedDerivative 0 n F) p :=
      ((contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hinterior 0 n).contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds hi)).continuousAt
    have he : mixedDerivative 0 n F =
        fun q : PolarPoint => iteratedDeriv n (fun θ => F (q.1, θ)) q.2 := by
      funext q
      simp only [mixedDerivative, iteratedDeriv_zero]
    rw [he] at hc
    exact hc.continuousWithinAt
  refine ⟨hab, Real.pi_pos, hinterior,
    n04b_angularRegular_closedStrip_of_jets hab.le hs hj, ?_⟩
  intro r hr θ
  obtain ⟨ha, hb, hc⟩ := hfield.periodic_coefficients z hz hsector r (hI hr)
  have hperiod := n04b_characteristic_periodic (L.coefficients z) r Real.pi ha hb hc
  change n04bCharacteristicDrift (L.coefficients z) (r, θ + Real.pi) -
      n04bCharacteristicHalfGap (L.coefficients z) (r, θ + Real.pi) =
    n04bCharacteristicDrift (L.coefficients z) (r, θ) -
      n04bCharacteristicHalfGap (L.coefficients z) (r, θ)
  exact congrArg₂ (fun a b : ℝ => a - b) (hperiod.1 θ) (hperiod.2 θ)

/-- The same N03 witness has the complete forward-flow regularity used
to construct its actual first integrals. The only additional property is
the explicitly named regularity of its raw corrected coefficients. -/
theorem n04b_actualMinusFlow_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) :
    N04bCircleFlowRegularity (fun p : PolarPoint => L.minusFlow z m p.1 p.2)
      (C.left m) (C.right m) Real.pi :=
  hN.2.minusFlow_regularity_of_scalarField hz hsector m
    (n04b_actualMinusField_regular hN hS hT hfield hz hsector m)

end ContinuousFlexibility.Statements
