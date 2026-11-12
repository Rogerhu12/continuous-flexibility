import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields
import ContinuousFlexibility.Analysis.N01CoefficientDifferenceFlatExtension

/-!
# The actual positive principal difference in an identity collar

Identity germs of the constructed coordinate and gauge reduce the actual
principal density to the physical coefficients. On a true positive point,
the retained N03 germs identify those coefficients with the original N01
fields. Thus the actual positive numerator has the genuine germ of the
smooth flat N01 difference representative. No ambient value is identified.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem wholePositiveCanonicalCoefficient_identity_germ
    (A : SymmetricCoefficients) {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {p : PolarPoint}
    (hτ : τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hσ : σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hQ : Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) (i : Fin 3) :
    canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q) =ᶠ[𝓝 p]
      canonicalCoefficientComponent i A := by
  have hD : fderiv ℝ σ =ᶠ[𝓝 p] fderiv ℝ (id : PolarPoint → PolarPoint) :=
    hσ.fderiv (𝕜 := ℝ)
  have hh : wholePositiveChartHeight σ Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [hσ, hQ] with q hsq hQq
    simp only [wholePositiveChartHeight, hsq, id_eq, hQq, inv_one]
  filter_upwards [hτ, hD, hh] with q ht hd hheight
  calc
    canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q) q =
        canonicalCoefficientComponent i
          (inverseChartPrincipalCoefficients A id id (fun _ => 1)) q := by
      unfold canonicalCoefficientComponent
      split_ifs <;> simp only [wholePositiveCanonicalCoefficients,
        inverseChartPrincipalCoefficients, coordinatePrincipalDensity,
        coefficientQuadratic, planeJacobian, ht, id_eq, hd, hheight]
    _ = canonicalCoefficientComponent i A q := by
      rw [inverseChartPrincipalCoefficients_id_one]

theorem n03CoefficientComponent_positive_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hN : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hpos : 0 < deriv D.w p.1) (i : Fin 3) :
    canonicalCoefficientComponent i (L.coefficients z) =ᶠ[𝓝 p]
      canonicalCoefficientComponent i (originalCoefficients D S C z) := by
  have hbc := hN.2.1 z hz hs p hp hpos
  unfold canonicalCoefficientComponent
  split_ifs
  · exact Filter.Eventually.of_forall (hN.1 z hz hs)
  · exact hbc.1
  · exact hbc.2

theorem n03PositivePrincipalDifference_flat_representative_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hpos : 0 < deriv D.w p.1) {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ}
    (hτ : τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hσ : σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hQ : Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) (i : Fin 3) :
    (fun q => canonicalCoefficientComponent i
        (wholePositiveCanonicalCoefficients (L.coefficients z) τ σ Q) q -
      canonicalCoefficientComponent i (L.coefficients (C.referenceState, 0)) q) =ᶠ[𝓝 p]
      n01OriginalCoefficientDifferenceExtension D S C z i := by
  have href := reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hrefS := hN.1.1.2.2.1.stateSector
  have hcurrent := (wholePositiveCanonicalCoefficient_identity_germ (L.coefficients z)
    hτ hσ hQ i).trans (n03CoefficientComponent_positive_germ hN.2 hz hs hp hpos i)
  have hreference := n03CoefficientComponent_positive_germ hN.2 href hrefS hp hpos i
  exact (hcurrent.sub hreference).trans
    (n01OriginalCoefficientDifferenceExtension_germ D S C z i hp).symm

end ContinuousFlexibility.Analysis
