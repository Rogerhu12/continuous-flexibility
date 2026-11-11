import ContinuousFlexibility.Analysis.N04bPositiveRegularity

/-!
# Actual determinant germs at the physical roots

N03 agrees with the original coefficient germs at every true profile root.
The determinant is therefore the actual type-corrected determinant there.
The N01 profile germ fixes its zero, independently of the height state.
No regularity of an arbitrary stored corrected field is assumed in this
germ comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem n04b_original_determinant_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p -
        (originalCoefficients D S C z).b p ^ 2 =
      (stateProfile D S C z.1 p.1 * deriv (stateProfile D S C z.1) p.1 / p.1) /
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 := by
  obtain ⟨B, hB⟩ := hN.1.1
  have hgeom : RadialProfileGeometry D := hB.1
  have hr : p.1 ≠ 0 := ne_of_gt (hgeom.1.trans hp.1.1)
  have hw : 0 < stateProfile D S C z.1 p.1 :=
    mul_pos (hgeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) := by
    have hq := (le_div_iff₀ hw).mp hb.2.2.1
    nlinarith
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p := by
    linarith [hb.2.2.2.2.1]
  exact polar_corrected_determinant (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) p.1)
    hr hdisc hQ.ne'

/-- The actual corrected determinant agrees with the original determinant
on a full neighborhood of each physical root. -/
theorem n04b_through03_determinant_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    (fun q => (L.coefficients z).a q * (L.coefficients z).c q -
      (L.coefficients z).b q ^ 2) =ᶠ[𝓝 p]
      (fun q => (originalCoefficients D S C z).a q *
        (originalCoefficients D S C z).c q -
          (originalCoefficients D S C z).b q ^ 2) := by
  have hg := h03.2.2.2.1 z hz hs p hp hroot
  filter_upwards [hg.1, hg.2] with q hb hc
  rw [h03.2.1 z hz hs q, hb, hc]

/-- The current determinant vanishes at the original root circle. -/
theorem n04b_through03_determinant_eq_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    (L.coefficients z).a p * (L.coefficients z).c p -
      (L.coefficients z).b p ^ 2 = 0 := by
  have hN := h03.1.1
  have hprofile := hN.2.2.2.2.2.2.2.2.2.2.1 z hz p.1 hp.1 hroot
  have hd : deriv (stateProfile D S C z.1) p.1 = 0 := by
    rw [hprofile.deriv_eq, hroot]
  have heq : (L.coefficients z).a p * (L.coefficients z).c p -
      (L.coefficients z).b p ^ 2 =
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p -
          (originalCoefficients D S C z).b p ^ 2 :=
    (n04b_through03_determinant_germ h03 hz hs hp hroot).self_of_nhds
  rw [heq, n04b_original_determinant_eq hT hS hN hz hs hp, hd]
  simp only [mul_zero, zero_div]

/-- The two actual characteristic speeds have the same drift value at
a true physical root. -/
theorem n04b_through03_characteristics_at_root
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    minusCharacteristicSpeed (L.coefficients z) p =
        (L.coefficients z).b p / (L.coefficients z).a p ∧
      plusCharacteristicSpeed (L.coefficients z) p =
        (L.coefficients z).b p / (L.coefficients z).a p := by
  have hdet := n04b_through03_determinant_eq_zero hT hS h03 hz hs hp hroot
  have hzero : (L.coefficients z).b p ^ 2 -
      (L.coefficients z).a p * (L.coefficients z).c p = 0 := by
    linarith
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed, hzero,
    Real.sqrt_zero, zero_div, sub_zero, add_zero, and_self]

end ContinuousFlexibility.Analysis
