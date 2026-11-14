import ContinuousFlexibility.Analysis.N04bCanonicalPhysicalAction
import ContinuousFlexibility.Analysis.CanonicalCoefficientIdentities
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace

/-!
# The actual potential from the reciprocal pulled height

The physical operator annihilates the constant function. Its existing
canonical action therefore expresses the stored potential using only
the canonical principal coefficients and the reciprocal pulled height.
The same identity covers both canonical signs and every mixed spatial jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

private theorem potential_eq_of_constant_operator_action
    {σ h ρ V d : ℝ} (hσ : σ * σ = 1) (hh : h ≠ 0) (hρ : ρ ≠ 0)
    (hzero : 0 = ρ / h * (d + (σ * V) * h⁻¹)) :
    V = -σ * h * d := by
  have hinner : d + (σ * V) * h⁻¹ = 0 :=
    (mul_eq_zero.mp hzero.symm).resolve_left (div_ne_zero hρ hh)
  have hproduct := congrArg (fun x : ℝ => x * h) hinner
  simp only [add_mul, mul_assoc, inv_mul_cancel₀ hh, mul_one, zero_mul] at hproduct
  calc
    V = (σ * σ) * V := by rw [hσ, one_mul]
    _ = σ * (d * h + σ * V) - σ * h * d := by ring
    _ = -σ * h * d := by rw [hproduct, mul_zero]; ring

/-- Testing the actual physical action on one identifies the potential
without differentiating the corrected physical coefficients. -/
theorem n04Realization_canonicalPotential_eq_reciprocalHeight_divergence
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    K.potential z m p =
      -(if K.positive m then -1 else (1 : ℝ)) *
        K.height z m (K.inverseChart z m p) *
        divergenceOperator (K.coefficients z m)
          (fun q => (K.height z m (K.inverseChart z m q))⁻¹) p := by
  have hcharts := hA.charts z hz hs m
  have hx : K.inverseChart z m p ∈ physicalPieceOpen S K z m := hcharts.2.1 hp
  have hgeometry := hcharts.2.2.2.2.2.2.2 (K.inverseChart z m p) hx
  have hheight : canonicalHeight S K z m (fun _ : PolarPoint => (1 : ℝ)) =
      (fun q => (K.height z m (K.inverseChart z m q))⁻¹) := by
    funext q
    simp only [canonicalHeight, one_div]
  have htest := n04b_physicalOperator_of_parts hA hB hz hs m
    (u := fun _ : PolarPoint => (1 : ℝ)) contDiff_const hx
  simp only [divergenceOperator_const, hheight, hcharts.2.2.2.1 p hp, one_div] at htest
  have hsign : (if K.positive m then -1 else (1 : ℝ)) *
      (if K.positive m then -1 else (1 : ℝ)) = 1 := by
    cases K.positive m <;> norm_num
  exact potential_eq_of_constant_operator_action hsign hgeometry.1.ne'
    (abs_ne_zero.mpr hgeometry.2.1) htest

/-- The identity holds on the full canonical open piece, so it identifies
every mixed spatial derivative of the stored potential there. -/
theorem n04Realization_canonicalPotential_mixedDerivative_eq
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (a b : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative a b (K.potential z m) p =
      mixedDerivative a b
        (fun q => -(if K.positive m then -1 else (1 : ℝ)) *
          K.height z m (K.inverseChart z m q) *
          divergenceOperator (K.coefficients z m)
            (fun y => (K.height z m (K.inverseChart z m y))⁻¹) q) p :=
  mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => n04Realization_canonicalPotential_eq_reciprocalHeight_divergence
      hA hB hz hs m hq) a b hp

end ContinuousFlexibility.Analysis
