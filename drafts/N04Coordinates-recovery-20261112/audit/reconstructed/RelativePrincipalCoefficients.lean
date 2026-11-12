import ContinuousFlexibility.Analysis.AdjugateInversePrincipalField

/-!
# Relative principal fields of two genuine coordinate changes

The first two lemmas are the two-dimensional matrix identities for the
actual principal density.  The last lemma compares two physical fields
whose actual charts have the same canonical density.  It assumes neither
the desired relative coefficient identity nor a full operator identity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology

private theorem principal_adjugate_cancel_scalar
    (a b c p q r s k t : ℝ) :
    t * ((k * (a * p ^ 2 + 2 * b * p * q + c * q ^ 2)) * s ^ 2 +
      2 * (k * (a * p * r + b * (p * s + q * r) + c * q * s)) * s * (-q) +
      (k * (a * r ^ 2 + 2 * b * r * s + c * s ^ 2)) * (-q) ^ 2) =
        (t * k * (p * s - r * q) ^ 2) * a ∧
    t * ((k * (a * p ^ 2 + 2 * b * p * q + c * q ^ 2)) * s * (-r) +
      (k * (a * p * r + b * (p * s + q * r) + c * q * s)) *
        (s * p + (-q) * (-r)) +
      (k * (a * r ^ 2 + 2 * b * r * s + c * s ^ 2)) * (-q) * p) =
        (t * k * (p * s - r * q) ^ 2) * b ∧
    t * ((k * (a * p ^ 2 + 2 * b * p * q + c * q ^ 2)) * (-r) ^ 2 +
      2 * (k * (a * p * r + b * (p * s + q * r) + c * q * s)) * (-r) * p +
      (k * (a * r ^ 2 + 2 * b * r * s + c * s ^ 2)) * p ^ 2) =
        (t * k * (p * s - r * q) ^ 2) * c := by
  constructor
  · ring
  constructor <;> ring

/-- Pulling the actual principal density back through its own first
derivative recovers the physical coefficients. -/
theorem adjugateCoordinatePrincipalCoefficients_eq_of_density
    (A B : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (hJ : planeJacobian F x ≠ 0) (hh : h x ≠ 0)
    (ha : B.a (F x) = (coordinatePrincipalDensity A F h).a x)
    (hb : B.b (F x) = (coordinatePrincipalDensity A F h).b x)
    (hc : B.c (F x) = (coordinatePrincipalDensity A F h).c x) :
    (adjugateCoordinatePrincipalCoefficients B F h).a x = A.a x ∧
      (adjugateCoordinatePrincipalCoefficients B F h).b x = A.b x ∧
      (adjugateCoordinatePrincipalCoefficients B F h).c x = A.c x := by
  have hfactor : (1 / (h x ^ 2 * |planeJacobian F x|)) *
      (h x ^ 2 / |planeJacobian F x|) * planeJacobian F x ^ 2 = 1 := by
    calc
      _ = h x ^ 2 * planeJacobian F x ^ 2 /
          (h x ^ 2 * |planeJacobian F x| ^ 2) := by
        simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
        ring
      _ = 1 := by
        rw [sq_abs]
        field_simp [hh, hJ]
  have hscalar := principal_adjugate_cancel_scalar
    (A.a x) (A.b x) (A.c x)
    (fderiv ℝ F x (1, 0)).1 (fderiv ℝ F x (0, 1)).1
    (fderiv ℝ F x (1, 0)).2 (fderiv ℝ F x (0, 1)).2
    (h x ^ 2 / |planeJacobian F x|) (1 / (h x ^ 2 * |planeJacobian F x|))
  have hfactor' : (1 / (h x ^ 2 * |planeJacobian F x|)) *
      (h x ^ 2 / |planeJacobian F x|) *
      ((fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
        (fderiv ℝ F x (1, 0)).2 * (fderiv ℝ F x (0, 1)).1) ^ 2 = 1 := hfactor
  simp only [hfactor', one_mul] at hscalar
  simpa only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
    ha, hb, hc, coordinatePrincipalDensity] using hscalar

/-- The adjugate pullback composes with the product of the two actual
height factors.  No regularity of the coefficient functions is needed. -/
theorem adjugateCoordinatePrincipalCoefficients_comp
    (A : SymmetricCoefficients) (F G : PolarPoint → PolarPoint)
    (f g : PolarPoint → ℝ) (x : PolarPoint)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G (F x)) :
    (adjugateCoordinatePrincipalCoefficients
      (adjugateCoordinatePrincipalCoefficients A G g) F f).a x =
        (adjugateCoordinatePrincipalCoefficients A (G ∘ F)
          (fun y => f y * g (F y))).a x ∧
    (adjugateCoordinatePrincipalCoefficients
      (adjugateCoordinatePrincipalCoefficients A G g) F f).b x =
        (adjugateCoordinatePrincipalCoefficients A (G ∘ F)
          (fun y => f y * g (F y))).b x ∧
    (adjugateCoordinatePrincipalCoefficients
      (adjugateCoordinatePrincipalCoefficients A G g) F f).c x =
        (adjugateCoordinatePrincipalCoefficients A (G ∘ F)
          (fun y => f y * g (F y))).c x := by
  have hd (v : PolarPoint) : fderiv ℝ (G ∘ F) x v =
      ((fderiv ℝ F x v).1 * (fderiv ℝ G (F x) (1, 0)).1 +
          (fderiv ℝ F x v).2 * (fderiv ℝ G (F x) (0, 1)).1,
       (fderiv ℝ F x v).1 * (fderiv ℝ G (F x) (1, 0)).2 +
          (fderiv ℝ F x v).2 * (fderiv ℝ G (F x) (0, 1)).2) := by
    rw [fderiv_comp x hG hF, ContinuousLinearMap.comp_apply]
    exact planeCLM_apply_decompose _ _
  have hJ := planeJacobian_comp hF hG
  constructor
  · simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
      hJ, hd, Function.comp_apply, abs_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  constructor <;>
    simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
      hJ, hd, Function.comp_apply, abs_mul, mul_pow, div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem adjugate_principal_congr_at
    (A B : SymmetricCoefficients) (F : PolarPoint → PolarPoint)
    (h : PolarPoint → ℝ) (x : PolarPoint)
    (ha : A.a (F x) = B.a (F x)) (hb : A.b (F x) = B.b (F x))
    (hc : A.c (F x) = B.c (F x)) :
    (adjugateCoordinatePrincipalCoefficients A F h).a x =
        (adjugateCoordinatePrincipalCoefficients B F h).a x ∧
      (adjugateCoordinatePrincipalCoefficients A F h).b x =
        (adjugateCoordinatePrincipalCoefficients B F h).b x ∧
      (adjugateCoordinatePrincipalCoefficients A F h).c x =
        (adjugateCoordinatePrincipalCoefficients B F h).c x := by
  constructor
  · simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic, ha, hb, hc]
  constructor <;>
    simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic, ha, hb, hc]

/-- Equal canonical principal fields give the true reference physical
field under the relative map and the ratio of the actual heights. -/
theorem reverseCoordinatePrincipalCoefficients_eq_of_common_density
    (A₀ A₁ B : SymmetricCoefficients)
    (F₀ F₁ τ σ : PolarPoint → PolarPoint) (h₀ h₁ : PolarPoint → ℝ)
    (x : PolarPoint)
    (hτ : DifferentiableAt ℝ τ x) (hσ : DifferentiableAt ℝ σ (τ x))
    (hF₁ : DifferentiableAt ℝ F₁ (τ x))
    (hinverse : σ ∘ τ =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint))
    (hchart : F₁ ∘ τ =ᶠ[𝓝 x] F₀)
    (hJ₀ : planeJacobian F₀ x ≠ 0) (hJ₁ : planeJacobian F₁ (τ x) ≠ 0)
    (hh₀ : h₀ x ≠ 0) (hh₁ : h₁ (τ x) ≠ 0)
    (hA₀ : B.a (F₀ x) = (coordinatePrincipalDensity A₀ F₀ h₀).a x ∧
      B.b (F₀ x) = (coordinatePrincipalDensity A₀ F₀ h₀).b x ∧
      B.c (F₀ x) = (coordinatePrincipalDensity A₀ F₀ h₀).c x)
    (hA₁ : B.a (F₁ (τ x)) = (coordinatePrincipalDensity A₁ F₁ h₁).a (τ x) ∧
      B.b (F₁ (τ x)) = (coordinatePrincipalDensity A₁ F₁ h₁).b (τ x) ∧
      B.c (F₁ (τ x)) = (coordinatePrincipalDensity A₁ F₁ h₁).c (τ x)) :
    (reverseCoordinatePrincipalCoefficients A₁ τ σ
      (fun y => h₀ y / h₁ (τ y))).a x = A₀.a x ∧
    (reverseCoordinatePrincipalCoefficients A₁ τ σ
      (fun y => h₀ y / h₁ (τ y))).b x = A₀.b x ∧
    (reverseCoordinatePrincipalCoefficients A₁ τ σ
      (fun y => h₀ y / h₁ (τ y))).c x = A₀.c x := by
  let q : PolarPoint → ℝ := fun y => h₀ y / h₁ (τ y)
  have hrec₀ := adjugateCoordinatePrincipalCoefficients_eq_of_density A₀ B F₀ h₀ x
    hJ₀ hh₀ hA₀.1 hA₀.2.1 hA₀.2.2
  have hrec₁ := adjugateCoordinatePrincipalCoefficients_eq_of_density A₁ B F₁ h₁ (τ x)
    hJ₁ hh₁ hA₁.1 hA₁.2.1 hA₁.2.2
  have hrev := reverseCoordinatePrincipalCoefficients_eq_adjugate A₁
    (F := τ) (G := σ) (h := q) (x := x) hτ hσ
    hinverse (show q x ≠ 0 from div_ne_zero hh₀ hh₁)
  have hc := adjugateCoordinatePrincipalCoefficients_comp B τ F₁ q h₁ x hτ hF₁
  have hq : q x * h₁ (τ x) = h₀ x := div_mul_cancel₀ _ hh₁
  have hd := hchart.fderiv_eq
  have hv := hchart.self_of_nhds
  have hJ : planeJacobian (F₁ ∘ τ) x = planeJacobian F₀ x := by
    simp only [planeJacobian, hd]
  have hvalues := adjugate_principal_congr_at
    (adjugateCoordinatePrincipalCoefficients B F₁ h₁) A₁ τ q x
    hrec₁.1 hrec₁.2.1 hrec₁.2.2
  have hmatch :
      (adjugateCoordinatePrincipalCoefficients B (F₁ ∘ τ)
        (fun y => q y * h₁ (τ y))).a x =
        (adjugateCoordinatePrincipalCoefficients B F₀ h₀).a x ∧
      (adjugateCoordinatePrincipalCoefficients B (F₁ ∘ τ)
        (fun y => q y * h₁ (τ y))).b x =
        (adjugateCoordinatePrincipalCoefficients B F₀ h₀).b x ∧
      (adjugateCoordinatePrincipalCoefficients B (F₁ ∘ τ)
        (fun y => q y * h₁ (τ y))).c x =
        (adjugateCoordinatePrincipalCoefficients B F₀ h₀).c x := by
    constructor
    · simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
        hd, hv, hJ, hq]
    constructor <;>
      simp only [adjugateCoordinatePrincipalCoefficients, coefficientQuadratic,
        hd, hv, hJ, hq]
  exact ⟨hrev.1.trans (hvalues.1.symm.trans (hc.1.trans (hmatch.1.trans hrec₀.1))),
    hrev.2.1.trans (hvalues.2.1.symm.trans (hc.2.1.trans (hmatch.2.1.trans hrec₀.2.1))),
    hrev.2.2.trans (hvalues.2.2.symm.trans (hc.2.2.trans (hmatch.2.2.trans hrec₀.2.2)))⟩

end ContinuousFlexibility.Analysis
