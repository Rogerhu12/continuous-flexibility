import ContinuousFlexibility.Analysis.N04PrincipalPositiveGeometry
import ContinuousFlexibility.Analysis.AdjugateInversePrincipalField

/-!
# The principal field in inverse-chart variables

The current-jet interface controls the physical coefficients at the inverse
point and the inverse chart itself.  Applying the proved adjugate identity
with the inverse map as the forward map expresses the stored principal
field in precisely those variables.  No derivative of a physical field
at a different point is introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff Topology

/-- The usual forward density, pulled to canonical coordinates, is the
adjugate expression of the inverse map and the reciprocal pulled height. -/
theorem n04PrincipalPositive_inversePrincipal_eq_adjugate
    (A : SymmetricCoefficients) {F G : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {p : PolarPoint}
    (hG : DifferentiableAt ℝ G p) (hF : DifferentiableAt ℝ F (G p))
    (hinverse : F ∘ G =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint))
    (hh : h (G p) ≠ 0) :
    (inverseChartPrincipalCoefficients A F G h).a p =
        (adjugateCoordinatePrincipalCoefficients A G (fun q => (h (G q))⁻¹)).a p ∧
      (inverseChartPrincipalCoefficients A F G h).b p =
        (adjugateCoordinatePrincipalCoefficients A G (fun q => (h (G q))⁻¹)).b p ∧
      (inverseChartPrincipalCoefficients A F G h).c p =
        (adjugateCoordinatePrincipalCoefficients A G (fun q => (h (G q))⁻¹)).c p := by
  have hFG : F (G p) = p := hinverse.self_of_nhds
  have hr := reverseCoordinatePrincipalCoefficients_eq_adjugate A
    (h := fun q => (h (G q))⁻¹) hG hF hinverse
    (inv_ne_zero hh : (h (G p))⁻¹ ≠ 0)
  have he (i : Fin 3) :
      canonicalCoefficientComponent i
          (reverseCoordinatePrincipalCoefficients A G F (fun q => (h (G q))⁻¹)) p =
        canonicalCoefficientComponent i (inverseChartPrincipalCoefficients A F G h) p := by
    fin_cases i <;>
      simp only [canonicalCoefficientComponent, Fin.isValue, ↓reduceIte,
        reverseCoordinatePrincipalCoefficients, inverseChartPrincipalCoefficients,
        coordinatePrincipalDensity, hFG, one_div, inv_inv]
  refine ⟨?_, ?_, ?_⟩
  · exact (he 0).symm.trans hr.1
  · exact (he 1).symm.trans hr.2.1
  · exact (he 2).symm.trans hr.2.2

/-- Expansion of the inverse-map adjugate formula.  The nine scalar inputs
are the three pulled physical coefficients, the pulled height, the inverse
Jacobian factor and the four first derivatives of the inverse map. -/
theorem n04PrincipalPositive_adjugate_inverseHeight_formula
    (A : SymmetricCoefficients) (G : PolarPoint → PolarPoint)
    (H : PolarPoint → ℝ) (p : PolarPoint) :
    let B := adjugateCoordinatePrincipalCoefficients A G (fun q => (H q)⁻¹)
    let M := fderiv ℝ G p
    let scale := H p ^ 2 / |planeJacobian G p|
    B.a p = scale *
        (A.a (G p) * (M (0, 1)).2 ^ 2 -
          2 * A.b (G p) * (M (0, 1)).2 * (M (0, 1)).1 +
          A.c (G p) * (M (0, 1)).1 ^ 2) ∧
      B.b p = scale *
        (-(A.a (G p) * (M (0, 1)).2 * (M (1, 0)).2) +
          A.b (G p) * ((M (0, 1)).2 * (M (1, 0)).1 +
            (M (0, 1)).1 * (M (1, 0)).2) -
          A.c (G p) * (M (0, 1)).1 * (M (1, 0)).1) ∧
      B.c p = scale *
        (A.a (G p) * (M (1, 0)).2 ^ 2 -
          2 * A.b (G p) * (M (1, 0)).2 * (M (1, 0)).1 +
          A.c (G p) * (M (1, 0)).1 ^ 2) := by
  dsimp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic]
  have hscale : 1 / ((H p)⁻¹ ^ 2 * |planeJacobian G p|) =
      H p ^ 2 / |planeJacobian G p| := by
    simp only [one_div, mul_inv_rev, inv_pow, inv_inv, div_eq_mul_inv, mul_comm, mul_one]
  rw [hscale]
  constructor
  · ring
  constructor <;> ring

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Every stored principal field is the inverse-only expression on its
actual canonical open piece.  Both signs use the same argument. -/
theorem n04PrincipalPositive_principal_eq_adjugate {b : ℕ} {ε : ℝ}
    (h : G.Admissible b ε) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : AnnularState (G.S η) × ℝ}
    (hz : z ∈ stateNeighborhood (G.S η) (G.C η) b ε)
    (hs : stateSector (G.S η) z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ canonicalOpen (G.S η) (G.V η) m) :
    let B := adjugateCoordinatePrincipalCoefficients ((G.L η).coefficients z)
      ((G.V η).inverseChart z m)
      (fun q => ((G.V η).height z m ((G.V η).inverseChart z m q))⁻¹)
    ((G.V η).coefficients z m).a p = B.a p ∧
      ((G.V η).coefficients z m).b p = B.b p ∧
      ((G.V η).coefficients z m).c p = B.c p := by
  have hA := (G.n04PrincipalPositive_admissible_parts h η).1
  have hc := hA.charts z hz hs m
  have hΩ : IsOpen (physicalPieceOpen (G.S η) (G.V η) z m) :=
    (hA.domains z hz hs m).1
  have hU : IsOpen (canonicalOpen (G.S η) (G.V η) m) :=
    isOpen_Ioo.prod isOpen_univ
  have hx := hc.2.1 hp
  have hF : DifferentiableAt ℝ ((G.V η).chart z m)
      ((G.V η).inverseChart z m p) :=
    ((hc.2.2.2.2.1 _ hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ ((G.V η).inverseChart z m) p :=
    ((hc.2.2.2.2.2.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hi : (G.V η).chart z m ∘ (G.V η).inverseChart z m =ᶠ[𝓝 p]
      (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hc.2.2.2.1 q hq
  have hh : (G.V η).height z m ((G.V η).inverseChart z m p) ≠ 0 :=
    (hc.2.2.2.2.2.2.2 _ hx).1.ne'
  rw [(G.n04PrincipalPositive_operatorFields η z m).1]
  exact n04PrincipalPositive_inversePrincipal_eq_adjugate
    ((G.L η).coefficients z) hG hF hi hh

end N04RealizationGauge

end ContinuousFlexibility.Analysis
