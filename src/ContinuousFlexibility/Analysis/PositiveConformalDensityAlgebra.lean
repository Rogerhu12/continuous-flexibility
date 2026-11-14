module

public import ContinuousFlexibility.Analysis.PrincipalCoefficientPullback
public import ContinuousFlexibility.Analysis.PositiveConformalBoundaryJets

/-!
# The actual positive principal density and its conformal residual

For a positive coefficient matrix, d = sqrt(det A)/a and e = -b/a.
The height is the reciprocal fourth root of det A. The discrepancy of
the transformed density from the identity is a smooth linear
combination of the two actual first-order conformal residuals. This is
an algebraic identity for the actual differential, not an assumed
coordinate transformation law or an equation on a collar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def positiveConformalSpeed (A : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  Real.sqrt (A.a p * A.c p - A.b p ^ 2) / A.a p

def positiveConformalShear (A : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  -A.b p / A.a p

def positiveConformalHeight (A : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  (Real.sqrt (Real.sqrt (A.a p * A.c p - A.b p ^ 2)))⁻¹

theorem positiveConformal_values
    {A : SymmetricCoefficients} {p : PolarPoint}
    (ha : 0 < A.a p) (hdet : 0 < A.a p * A.c p - A.b p ^ 2) :
    0 < positiveConformalSpeed A p ∧ 0 < positiveConformalHeight A p ∧
      A.b p = -A.a p * positiveConformalShear A p ∧
      A.c p = A.a p * (positiveConformalSpeed A p ^ 2 + positiveConformalShear A p ^ 2) ∧
      positiveConformalHeight A p ^ 2 * A.a p * positiveConformalSpeed A p = 1 := by
  have hs : 0 < Real.sqrt (A.a p * A.c p - A.b p ^ 2) := Real.sqrt_pos.mpr hdet
  refine ⟨div_pos hs ha, inv_pos.mpr (Real.sqrt_pos.mpr hs), ?_, ?_, ?_⟩
  · unfold positiveConformalShear
    field_simp [ha.ne'] <;> ring
  · unfold positiveConformalSpeed positiveConformalShear
    have hsquare := Real.sq_sqrt hdet.le
    field_simp [ha.ne']
    simp only [mul_comm (A.c p) (A.a p)]
    nlinarith [hsquare]
  · rw [positiveConformalHeight, inv_pow, Real.sq_sqrt hs.le]
    unfold positiveConformalSpeed
    field_simp [ha.ne', hs.ne'] <;> ring

theorem contDiffAt_positiveConformalFields
    {A : SymmetricCoefficients} {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p) (hb : ContDiffAt ℝ ∞ A.b p)
    (hc : ContDiffAt ℝ ∞ A.c p)
    (ha0 : 0 < A.a p) (hdet : 0 < A.a p * A.c p - A.b p ^ 2) :
    ContDiffAt ℝ ∞ (positiveConformalSpeed A) p ∧
      ContDiffAt ℝ ∞ (positiveConformalShear A) p ∧
      ContDiffAt ℝ ∞ (positiveConformalHeight A) p := by
  have hD : ContDiffAt ℝ ∞ (fun q => A.a q * A.c q - A.b q ^ 2) p :=
    (ha.mul hc).sub (hb.pow 2)
  have hS : ContDiffAt ℝ ∞
      (fun q => Real.sqrt (A.a q * A.c q - A.b q ^ 2)) p := by
    simpa only [Real.sqrt_eq_rpow] using
      hD.rpow_const_of_ne (p := (1 / 2 : ℝ)) hdet.ne'
  have hs : 0 < Real.sqrt (A.a p * A.c p - A.b p ^ 2) := Real.sqrt_pos.mpr hdet
  have hSS : ContDiffAt ℝ ∞
      (fun q => Real.sqrt (Real.sqrt (A.a q * A.c q - A.b q ^ 2))) p := by
    simpa only [Real.sqrt_eq_rpow] using
      hS.rpow_const_of_ne (p := (1 / 2 : ℝ)) hs.ne'
  exact ⟨hS.fun_div ha ha0.ne', hb.neg.fun_div ha ha0.ne',
    hSS.fun_inv (Real.sqrt_pos.mpr hs).ne'⟩

def positiveConformalResidual (d e : PolarPoint → ℝ)
    (X : Bool → PolarPoint → ℝ) (side : Bool) (p : PolarPoint) : ℝ :=
  radialPartial (X side) p -
    (e p * angularPartial (X side) p +
      (if side then -d p else d p) * angularPartial (X (!side)) p)

private theorem scalar_positiveConformal_density_remainder
    {a d h : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) (hh : h ^ 2 * a * d = 1)
    (e xr yr u v : ℝ) (hJ : xr * v - yr * u ≠ 0) :
    let J := xr * v - yr * u
    let s := xr - (e * u + d * v)
    let t := yr - (e * v - d * u)
    h ^ 2 / J * (a * xr ^ 2 + 2 * (-a * e) * xr * u +
        a * (d ^ 2 + e ^ 2) * u ^ 2) - 1 =
        ((v + s / d) / J) * s + (u / J) * t ∧
      h ^ 2 / J * (a * xr * yr + (-a * e) * (xr * v + u * yr) +
        a * (d ^ 2 + e ^ 2) * u * v) =
        ((-u + t / d) / J) * s + (v / J) * t ∧
      h ^ 2 / J * (a * yr ^ 2 + 2 * (-a * e) * yr * v +
        a * (d ^ 2 + e ^ 2) * v ^ 2) - 1 =
        (-v / J) * s + ((-u + t / d) / J) * t := by
  have hh' : h ^ 2 = 1 / (a * d) :=
    (eq_div_iff (mul_ne_zero ha hd)).2 (by simpa only [mul_assoc] using hh)
  dsimp only
  rw [hh']
  refine ⟨?_, ?_, ?_⟩ <;> field_simp [ha, hd, hJ] <;> ring

/-- Every principal-density discrepancy contains an actual conformal
residual as a factor. Positivity of J is only used to remove its absolute
value, and will be proved from the first boundary jets of the polynomial. -/
theorem positiveConformalDensity_remainder
    {A : SymmetricCoefficients} {X : Bool → PolarPoint → ℝ} {p : PolarPoint}
    (hX : ∀ side, DifferentiableAt ℝ (X side) p)
    (ha : 0 < A.a p) (hdet : 0 < A.a p * A.c p - A.b p ^ 2)
    (hJ : 0 < planeJacobian (fun q => (X false q, X true q)) p) :
    let F := fun q => (X false q, X true q)
    let J := planeJacobian F p
    let d := positiveConformalSpeed A p
    let s := positiveConformalResidual (positiveConformalSpeed A) (positiveConformalShear A) X false p
    let t := positiveConformalResidual (positiveConformalSpeed A) (positiveConformalShear A) X true p
    let u := angularPartial (X false) p
    let v := angularPartial (X true) p
    (coordinatePrincipalDensity A F (positiveConformalHeight A)).a p - 1 =
        ((v + s / d) / J) * s + (u / J) * t ∧
      (coordinatePrincipalDensity A F (positiveConformalHeight A)).b p =
        ((-u + t / d) / J) * s + (v / J) * t ∧
      (coordinatePrincipalDensity A F (positiveConformalHeight A)).c p - 1 =
        (-v / J) * s + ((-u + t / d) / J) * t := by
  have hv := positiveConformal_values ha hdet
  have hDF : fderiv ℝ (fun q => (X false q, X true q)) p =
      (fderiv ℝ (X false) p).prod (fderiv ℝ (X true) p) :=
    ((hX false).hasFDerivAt.prodMk (hX true).hasFDerivAt).fderiv
  have hJ' : radialPartial (X false) p * angularPartial (X true) p -
      radialPartial (X true) p * angularPartial (X false) p ≠ 0 := by
    simpa only [planeJacobian, hDF, ContinuousLinearMap.prod_apply,
      radialPartial, angularPartial] using hJ.ne'
  have he := scalar_positiveConformal_density_remainder ha.ne' hv.1.ne' hv.2.2.2.2
    (positiveConformalShear A p) (radialPartial (X false) p)
    (radialPartial (X true) p) (angularPartial (X false) p) (angularPartial (X true) p) hJ'
  dsimp only
  simp only [coordinatePrincipalDensity, coefficientQuadratic]
  rw [show |planeJacobian (fun q => (X false q, X true q)) p| =
      planeJacobian (fun q => (X false q, X true q)) p from abs_of_pos hJ]
  simpa only [coordinatePrincipalDensity, coefficientQuadratic, planeJacobian, hDF,
    ContinuousLinearMap.prod_apply, radialPartial, angularPartial,
    positiveConformalResidual, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hv.2.2.1, hv.2.2.2.1, sub_eq_add_neg, neg_mul] using he

end ContinuousFlexibility.Analysis
