import ContinuousFlexibility.Analysis.NegativeCanonicalEffectiveOperator

/-!
# Determinants of actual coordinate principal densities

A two-dimensional divergence density acquires the fourth power of the
height in its determinant; the actual Jacobian factors cancel. Reversing
the coordinate change therefore gives det B = det A / h^4. The negative
Airy field has determinant -ξ, so the frozen open-piece chart supplies the
exact physical identity without any regularity hypothesis on stored L.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem principal_density_det_scalar (a b c p q r s k : ℝ) :
    (k * (a * p ^ 2 + 2 * b * p * q + c * q ^ 2)) *
        (k * (a * r ^ 2 + 2 * b * r * s + c * s ^ 2)) -
      (k * (a * p * r + b * (p * s + q * r) + c * q * s)) ^ 2 =
      k ^ 2 * (p * s - r * q) ^ 2 * (a * c - b ^ 2) := by
  ring

/-- This identity is algebraic in the actual first derivative. Smoothness
is not needed beyond the stated nonzero actual Jacobian. -/
theorem coordinatePrincipalDensity_determinant
    (A : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint) (hJ : planeJacobian F x ≠ 0) :
    (coordinatePrincipalDensity A F h).a x * (coordinatePrincipalDensity A F h).c x -
        (coordinatePrincipalDensity A F h).b x ^ 2 =
      h x ^ 4 * (A.a x * A.c x - A.b x ^ 2) := by
  dsimp only [coordinatePrincipalDensity, coefficientQuadratic]
  rw [principal_density_det_scalar]
  change (h x ^ 2 / |planeJacobian F x|) ^ 2 * planeJacobian F x ^ 2 *
      (A.a x * A.c x - A.b x ^ 2) =
    h x ^ 4 * (A.a x * A.c x - A.b x ^ 2)
  have hs : (h x ^ 2 / |planeJacobian F x|) ^ 2 *
      planeJacobian F x ^ 2 = h x ^ 4 := by
    rw [div_pow, sq_abs]
    field_simp [hJ]
    <;> ring
  rw [hs]

/-- The determinant of the reversed field is an exact physical formula. -/
theorem reverseCoordinatePrincipalCoefficients_determinant
    (A : SymmetricCoefficients) (F G : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJG : planeJacobian G (F x) ≠ 0) (hGF : G (F x) = x) :
    (reverseCoordinatePrincipalCoefficients A F G h).a x *
          (reverseCoordinatePrincipalCoefficients A F G h).c x -
        (reverseCoordinatePrincipalCoefficients A F G h).b x ^ 2 =
      (A.a (F x) * A.c (F x) - A.b (F x) ^ 2) / h x ^ 4 := by
  change (coordinatePrincipalDensity A G (fun y => 1 / h (G y))).a (F x) *
          (coordinatePrincipalDensity A G (fun y => 1 / h (G y))).c (F x) -
        (coordinatePrincipalDensity A G (fun y => 1 / h (G y))).b (F x) ^ 2 = _
  rw [coordinatePrincipalDensity_determinant A G (fun y => 1 / h (G y)) (F x) hJG]
  simp only [hGF, div_pow, one_pow]
  ring

/-- A genuine local inverse has reciprocal actual Jacobian determinants. -/
theorem planeJacobian_inverse_mul_of_germ
    {F G : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x))
    (hinverse : G ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint)) :
    planeJacobian G (F x) * planeJacobian F x = 1 := by
  have hid : planeJacobian (G ∘ F) x = 1 := by
    unfold planeJacobian
    rw [hinverse.fderiv_eq]
    simp only [fderiv_id, ContinuousLinearMap.id_apply, one_mul, zero_mul, sub_zero]
  exact (planeJacobian_comp hF hG).symm.trans hid

/-- PartA's actual open inverse suffices for the determinant of the
effective Airy field. In combination with the negative PartB identity,
this is the determinant of the smooth field having the physical action. -/
theorem negativeCanonicalEffectiveCoefficients_determinant
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z m) :
    (negativeCanonicalEffectiveCoefficients S K z m).a p *
          (negativeCanonicalEffectiveCoefficients S K z m).c p -
        (negativeCanonicalEffectiveCoefficients S K z m).b p ^ 2 =
      -(K.chart z m p).1 / K.height z m p ^ 4 := by
  have hU : IsOpen (physicalPieceOpen S K z m) := (hA.domains z hz hsector m).1
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  rcases hA.charts z hz hsector m with
    ⟨hFV, hGU, hGF, hFG, hF, hG, hh, hpoint⟩
  have hFp : K.chart z m p ∈ canonicalOpen S K m := hFV hp
  have hinverse : K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 p]
      (id : PolarPoint → PolarPoint) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hGF q hq
  have hprod' : planeJacobian (K.inverseChart z m) (K.chart z m p) *
      planeJacobian (K.chart z m) p = 1 :=
    planeJacobian_inverse_mul_of_germ
      (((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      (((hG (K.chart z m p) hFp).contDiffAt (hV.mem_nhds hFp)).differentiableAt
        (by simp)) hinverse
  have hJG : planeJacobian (K.inverseChart z m) (K.chart z m p) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hprod'
    exact zero_ne_one hprod'
  have he := reverseCoordinatePrincipalCoefficients_determinant
    canonicalAiryPrincipalCoefficients (K.chart z m) (K.inverseChart z m)
    (K.height z m) p hJG (hGF p hp)
  simpa only [negativeCanonicalEffectiveCoefficients, canonicalAiryPrincipalCoefficients,
    one_mul, zero_pow two_ne_zero, sub_zero] using he

end ContinuousFlexibility.Analysis
