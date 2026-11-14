module

public import ContinuousFlexibility.Analysis.AdjugatePrincipalField
public import Mathlib.Tactic.LinearCombination

/-!
# The forward adjugate field equals the actual reverse field

Four basis evaluations of the genuine inverse derivative identity give
the inverse matrix entries. Their substitution identifies the explicit
forward-only principal field with the reverse coordinate density on an
open inverse chart. No boundary value of the prescribed inverse is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem inverse_entries_scalar
    {a b c d p q r s : ℝ} (hJ : a * d - c * b ≠ 0)
    (h1 : a * p + c * q = 1) (h2 : b * p + d * q = 0)
    (h3 : a * r + c * s = 0) (h4 : b * r + d * s = 1) :
    p = d / (a * d - c * b) ∧ q = -b / (a * d - c * b) ∧
      r = -c / (a * d - c * b) ∧ s = a / (a * d - c * b) := by
  refine ⟨(eq_div_iff hJ).mpr ?_, (eq_div_iff hJ).mpr ?_,
    (eq_div_iff hJ).mpr ?_, (eq_div_iff hJ).mpr ?_⟩
  · linear_combination d * h1 - c * h2
  · linear_combination a * h2 - b * h1
  · linear_combination d * h3 - c * h4
  · linear_combination a * h4 - b * h3

/-- The entries of the actual derivative of a genuine local inverse. -/
theorem fderiv_inverse_entries_of_germ
    {F G : PolarPoint → PolarPoint} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x))
    (hinverse : G ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint)) :
    (fderiv ℝ G (F x) (1, 0)).1 =
        (fderiv ℝ F x (0, 1)).2 / planeJacobian F x ∧
      (fderiv ℝ G (F x) (0, 1)).1 =
        -(fderiv ℝ F x (0, 1)).1 / planeJacobian F x ∧
      (fderiv ℝ G (F x) (1, 0)).2 =
        -(fderiv ℝ F x (1, 0)).2 / planeJacobian F x ∧
      (fderiv ℝ G (F x) (0, 1)).2 =
        (fderiv ℝ F x (1, 0)).1 / planeJacobian F x := by
  let M : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ F x
  let N : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ G (F x)
  have hcomp : N.comp M = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = fderiv ℝ (G ∘ F) x := (fderiv_comp x hG hF).symm
      _ = fderiv ℝ (id : PolarPoint → PolarPoint) x := hinverse.fderiv_eq
      _ = _ := by rw [fderiv_id]
  have hleft (v : PolarPoint) : N (M v) = v :=
    congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L v) hcomp
  have h1 := hleft (1, 0)
  have h2 := hleft (0, 1)
  rw [planeCLM_apply_decompose N (M (1, 0))] at h1
  rw [planeCLM_apply_decompose N (M (0, 1))] at h2
  have h11 : (M (1, 0)).1 * (N (1, 0)).1 +
      (M (1, 0)).2 * (N (0, 1)).1 = 1 := congrArg Prod.fst h1
  have h12 : (M (0, 1)).1 * (N (1, 0)).1 +
      (M (0, 1)).2 * (N (0, 1)).1 = 0 := congrArg Prod.fst h2
  have h21 : (M (1, 0)).1 * (N (1, 0)).2 +
      (M (1, 0)).2 * (N (0, 1)).2 = 0 := congrArg Prod.snd h1
  have h22 : (M (0, 1)).1 * (N (1, 0)).2 +
      (M (0, 1)).2 * (N (0, 1)).2 = 1 := congrArg Prod.snd h2
  have hprod := planeJacobian_inverse_mul_of_germ hF hG hinverse
  have hJF : planeJacobian F x ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hprod
    exact zero_ne_one hprod
  have hMdet : (M (1, 0)).1 * (M (0, 1)).2 -
      (M (1, 0)).2 * (M (0, 1)).1 ≠ 0 := hJF
  simpa only [M, N, planeJacobian] using
    inverse_entries_scalar hMdet h11 h12 h21 h22

private theorem inverse_density_scale {h J : ℝ} (hh : h ≠ 0) (hJ : J ≠ 0) :
    ((1 / h) ^ 2 / |1 / J|) / J ^ 2 = 1 / (h ^ 2 * |J|) := by
  have hAbs : |J| ≠ 0 := abs_ne_zero.mpr hJ
  calc
    _ = |J| / (h ^ 2 * J ^ 2) := by
      rw [abs_div, abs_one]
      field_simp [hh, hJ, hAbs]
      <;> ring
    _ = |J| / (h ^ 2 * |J| ^ 2) := by rw [sq_abs]
    _ = _ := by
      field_simp [hh, hAbs]
      <;> ring

private theorem inverse_density_quadratic {h J : ℝ} (hh : h ≠ 0) (hJ : J ≠ 0)
    (a b c u v : ℝ) :
    ((1 / h) ^ 2 / |1 / J|) *
        (a * (u / J) ^ 2 + 2 * b * (u / J) * (v / J) + c * (v / J) ^ 2) =
      (1 / (h ^ 2 * |J|)) * (a * u ^ 2 + 2 * b * u * v + c * v ^ 2) := by
  have hq :
      a * (u / J) ^ 2 + 2 * b * (u / J) * (v / J) + c * (v / J) ^ 2 =
        (a * u ^ 2 + 2 * b * u * v + c * v ^ 2) / J ^ 2 := by
    field_simp [hJ]
    <;> ring
  rw [hq]
  calc
    _ = (((1 / h) ^ 2 / |1 / J|) / J ^ 2) *
        (a * u ^ 2 + 2 * b * u * v + c * v ^ 2) := by ring
    _ = _ := by rw [inverse_density_scale hh hJ]

private theorem inverse_density_bilinear {h J : ℝ} (hh : h ≠ 0) (hJ : J ≠ 0)
    (a b c u v w z : ℝ) :
    ((1 / h) ^ 2 / |1 / J|) *
        (a * (u / J) * (w / J) +
          b * ((u / J) * (z / J) + (v / J) * (w / J)) + c * (v / J) * (z / J)) =
      (1 / (h ^ 2 * |J|)) * (a * u * w + b * (u * z + v * w) + c * v * z) := by
  have hq :
      a * (u / J) * (w / J) +
          b * ((u / J) * (z / J) + (v / J) * (w / J)) + c * (v / J) * (z / J) =
        (a * u * w + b * (u * z + v * w) + c * v * z) / J ^ 2 := by
    field_simp [hJ]
    <;> ring
  rw [hq]
  calc
    _ = (((1 / h) ^ 2 / |1 / J|) / J ^ 2) *
        (a * u * w + b * (u * z + v * w) + c * v * z) := by ring
    _ = _ := by rw [inverse_density_scale hh hJ]

/-- The two explicit principal fields agree at every genuine interior
inverse point, by the actual derivative chain rule. -/
theorem reverseCoordinatePrincipalCoefficients_eq_adjugate
    (A : SymmetricCoefficients) {F G : PolarPoint → PolarPoint}
    {h : PolarPoint → ℝ} {x : PolarPoint}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x))
    (hinverse : G ∘ F =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint))
    (hh : h x ≠ 0) :
    (reverseCoordinatePrincipalCoefficients A F G h).a x =
        (adjugateCoordinatePrincipalCoefficients A F h).a x ∧
      (reverseCoordinatePrincipalCoefficients A F G h).b x =
        (adjugateCoordinatePrincipalCoefficients A F h).b x ∧
      (reverseCoordinatePrincipalCoefficients A F G h).c x =
        (adjugateCoordinatePrincipalCoefficients A F h).c x := by
  have hGF : G (F x) = x := hinverse.self_of_nhds
  have hprod := planeJacobian_inverse_mul_of_germ hF hG hinverse
  have hJF : planeJacobian F x ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hprod
    exact zero_ne_one hprod
  have hJG : planeJacobian G (F x) = 1 / planeJacobian F x :=
    (eq_div_iff hJF).mpr hprod
  rcases fderiv_inverse_entries_of_germ hF hG hinverse with ⟨h11, h12, h21, h22⟩
  dsimp only [reverseCoordinatePrincipalCoefficients, inverseChartPrincipalCoefficients,
    coordinatePrincipalDensity, adjugateCoordinatePrincipalCoefficients, coefficientQuadratic]
  simp only [hGF, hJG, h11, h12, h21, h22]
  exact ⟨inverse_density_quadratic hh hJF _ _ _ _ _,
    inverse_density_bilinear hh hJF _ _ _ _ _ _ _,
    inverse_density_quadratic hh hJF _ _ _ _ _⟩

end ContinuousFlexibility.Analysis
