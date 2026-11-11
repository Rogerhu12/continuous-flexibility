import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.TypeCorrection

/-!
# The actual corrected coefficients retain the fixed turning circles

The type correction makes the principal determinant proportional to the
profile derivative, with a strictly positive height denominator. The N01
profile germ and N03 coefficient germs therefore force the determinant to
vanish on every reference turning circle for every admitted state.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The height perturbation does not move a root where the actual profile
has the reference germ. Only the genuine scalar determinant identity is
used; the height is otherwise arbitrary. -/
theorem n06_polarCorrectedDeterminant_zero_of_profile_germ
    {w w₀ : ℝ → ℝ} (Z : PolarPoint → ℝ) {p : PolarPoint}
    (hw₀ : DifferentiableAt ℝ w₀ p.1)
    (hgerm : w =ᶠ[𝓝 p.1] w₀) (hroot : deriv w₀ p.1 = 0)
    (hr : p.1 ≠ 0) (hD : 0 < polarDiscriminant w Z p)
    (hQ : heightQ (profileEnergy w p) (heightRadial Z p)
      (angularPartial (heightAngular Z) p) ≠ 0) :
    polarLinearA w Z p * polarCorrectedC w Z p - polarLinearB w Z p ^ 2 = 0 := by
  have hw : DifferentiableAt ℝ w p.1 := hw₀.congr_of_eventuallyEq hgerm
  have hwzero : deriv w p.1 = 0 := hgerm.deriv_eq.trans hroot
  simpa only [hwzero, mul_zero, zero_div] using
    polar_corrected_determinant Z hw hr hD hQ

/-- Every fixed reference root is a zero of the determinant of the actual
N01 coefficient field. No new root-collar or state-regularity premise is
needed: the original N01 germ and numerical denominator bounds suffice. -/
theorem n06_originalCoefficients_determinant_zero_at_reference_root
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p -
      (originalCoefficients D S C z).b p ^ 2 = 0 := by
  have hprofile : RadialProfileGeometry D := hN01.1.1.choose_spec.1
  have hbounds := hN01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hgerm := hN01.2.2.2.2.2.2.2.2.2.2.1 z hz p.1 hp.1 hroot
  have hD : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hbounds.2.2.2.2.1
  have hQ : heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0 := by
    intro hzero
    have hlo := hbounds.2.2.1
    rw [hzero, zero_div] at hlo
    norm_num at hlo
  exact n06_polarCorrectedDeterminant_zero_of_profile_germ
    (stateHeight D S C z) (hprofile.2.2.1.1.differentiable (by simp) p.1)
    hgerm hroot (hprofile.1.trans hp.1.1).ne' hD hQ

/-- The actual N03 return correction retains this zero determinant at
every fixed reference turning circle, because its coefficient germs
there agree with the original type-corrected field. -/
theorem n06_correctedCoefficients_determinant_zero_at_reference_root
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    (L.coefficients z).a p * (L.coefficients z).c p -
      (L.coefficients z).b p ^ 2 = 0 := by
  have hbc := hN03.2.2.1 z hz hs p hp hroot
  rw [hN03.1 z hz hs p, hbc.1.eq_of_nhds, hbc.2.eq_of_nhds]
  exact n06_originalCoefficients_determinant_zero_at_reference_root hN01 hz hs hp hroot

end ContinuousFlexibility.Statements
