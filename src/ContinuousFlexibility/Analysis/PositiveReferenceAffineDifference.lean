module

public import ContinuousFlexibility.Analysis.PositiveReferenceIdentity
public import ContinuousFlexibility.Analysis.RadialPrimitiveJetBounds

/-!
# The actual radial interpolation is affine in its endpoint slopes

The normalizing denominator depends only on the already selected interval
and collar. Subtracting the unit reference removes the constant mass term.
Thus the actual displacement is the radial primitive of a linear endpoint
correction, with no new choice of width or normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

def positiveReferenceSlopeDeviation (l r δ : ℝ)
    (A : Bool → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  positiveEndpointCutoff l δ p.1 * (A false p - 1) +
    positiveEndpointCutoff r δ p.1 * (A true p - 1)

def balancedPositiveReferenceSlope (l r δ : ℝ) (F : PolarPoint → ℝ)
    (p : PolarPoint) : ℝ :=
  F p - ((∫ t in l..r, F (t, p.2)) / positiveReferenceMiddleMass l r δ) *
    (1 - positiveEndpointCutoff l δ p.1 - positiveEndpointCutoff r δ p.1)

theorem contDiff_positiveReferenceSlopeDeviation
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    (l r δ : ℝ) : ContDiff ℝ ∞ (positiveReferenceSlopeDeviation l r δ A) :=
  (((contDiff_positiveEndpointCutoff l δ).comp contDiff_fst).mul
    ((hA false).sub contDiff_const)).add
    (((contDiff_positiveEndpointCutoff r δ).comp contDiff_fst).mul
      ((hA true).sub contDiff_const))

theorem contDiff_balancedPositiveReferenceSlope
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (l r δ : ℝ) :
    ContDiff ℝ ∞ (balancedPositiveReferenceSlope l r δ F) := by
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hI : ContDiff ℝ ∞ (fun θ : ℝ => ∫ t in l..r, F (t, θ)) :=
    contDiff_parametric_intervalIntegral (hF.comp hswap) l r
  exact hF.sub (((hI.div_const (positiveReferenceMiddleMass l r δ)).comp contDiff_snd).mul
    ((contDiff_const.sub ((contDiff_positiveEndpointCutoff l δ).comp contDiff_fst)).sub
      ((contDiff_positiveEndpointCutoff r δ).comp contDiff_fst)))

private theorem positiveReferenceEndMass_div_input
    (l r δ m : ℝ) (V : Bool → PolarPoint → ℝ) (θ : ℝ) :
    positiveReferenceEndMass l r δ (fun x => V false (x, θ) / m)
      (fun x => V true (x, θ) / m) =
        (∫ x in l..r,
          positiveEndpointCutoff l δ x * V false (x, θ) +
            positiveEndpointCutoff r δ x * V true (x, θ)) / m := by
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- This is an equality of the existing displayed coordinate on the
whole plane, including the exterior portions of the interpolation. -/
theorem parameterizedPositiveReferenceCoordinate_sub_fst
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) :
    (fun p => parameterizedPositiveReferenceCoordinate l r δ l (r - l) A p - p.1) =
      radialIntervalPrimitive l
        (balancedPositiveReferenceSlope l r δ (positiveReferenceSlopeDeviation l r δ A)) := by
  have hm : 0 < r - l := by linarith
  have hI : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hgap
  let P : ℝ → ℝ → ℝ := fun θ x =>
    positiveEndpointCutoff l δ x * A false (x, θ) +
      positiveEndpointCutoff r δ x * A true (x, θ)
  let P₀ : ℝ → ℝ := fun x => positiveEndpointCutoff l δ x + positiveEndpointCutoff r δ x
  have hP (θ : ℝ) : Continuous (P θ) :=
    ((contDiff_positiveEndpointCutoff l δ).continuous.mul
      ((hA false).continuous.comp (continuous_id.prodMk continuous_const))).add
      ((contDiff_positiveEndpointCutoff r δ).continuous.mul
        ((hA true).continuous.comp (continuous_id.prodMk continuous_const)))
  have hP₀ : Continuous P₀ := (contDiff_positiveEndpointCutoff l δ).continuous.add
    (contDiff_positiveEndpointCutoff r δ).continuous
  have hmass (θ : ℝ) :
      (∫ x in l..r, positiveReferenceSlopeDeviation l r δ A (x, θ)) =
        (∫ x in l..r, P θ x) - ∫ x in l..r, P₀ x := by
    rw [← intervalIntegral.integral_sub
      ((hP θ).intervalIntegrable (μ := MeasureTheory.volume) l r)
      (hP₀.intervalIntegrable (μ := MeasureTheory.volume) l r)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [positiveReferenceSlopeDeviation, P, P₀]
    ring
  have hslope (x θ : ℝ) :
      (r - l) * positiveReferenceSlope l r δ
          (fun t => A false (t, θ) / (r - l))
          (fun t => A true (t, θ) / (r - l)) x -
        (r - l) * positiveReferenceSlope l r δ
          (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) x =
      balancedPositiveReferenceSlope l r δ
        (positiveReferenceSlopeDeviation l r δ A) (x, θ) := by
    have hAdiv := positiveReferenceEndMass_div_input l r δ (r - l) A θ
    have hOneDiv := positiveReferenceEndMass_div_input l r δ (r - l)
      (fun _ _ => (1 : ℝ)) θ
    simp only [mul_one] at hOneDiv
    simp only [positiveReferenceSlope, positiveReferenceScale, hAdiv, hOneDiv,
      balancedPositiveReferenceSlope, hmass]
    dsimp only [positiveReferenceSlopeDeviation, P, P₀]
    field_simp [hm.ne', hI.ne'] <;> ring
  have href := parameterizedPositiveReferenceCoordinate_one_eq_fst hδ hgap
  funext p
  have hSA : Continuous (fun x => positiveReferenceSlope l r δ
      (fun t => A false (t, p.2) / (r - l))
      (fun t => A true (t, p.2) / (r - l)) x) :=
    (contDiff_positiveReferenceSlope hδ
      (fun x _ => (((hA false).comp (contDiff_id.prodMk contDiff_const)).div_const
        (r - l)).contDiffAt)
      (fun x _ => (((hA true).comp (contDiff_id.prodMk contDiff_const)).div_const
        (r - l)).contDiffAt)).continuous
  have hS₀ : Continuous (positiveReferenceSlope l r δ
      (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l))) :=
    (contDiff_positiveReferenceSlope hδ
      (fun _ _ => contDiffAt_const) (fun _ _ => contDiffAt_const)).continuous
  calc
    _ = parameterizedPositiveReferenceCoordinate l r δ l (r - l) A p -
        parameterizedPositiveReferenceCoordinate l r δ l (r - l) (fun _ _ => 1) p := by
      rw [href]
    _ = (r - l) * (∫ x in l..p.1, positiveReferenceSlope l r δ
        (fun t => A false (t, p.2) / (r - l))
        (fun t => A true (t, p.2) / (r - l)) x) -
      (r - l) * (∫ x in l..p.1, positiveReferenceSlope l r δ
        (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) x) := by
      simp only [parameterizedPositiveReferenceCoordinate, positiveReferenceCoordinate]
      ring
    _ = ∫ x in l..p.1,
        ((r - l) * positiveReferenceSlope l r δ
            (fun t => A false (t, p.2) / (r - l))
            (fun t => A true (t, p.2) / (r - l)) x -
          (r - l) * positiveReferenceSlope l r δ
            (fun _ => 1 / (r - l)) (fun _ => 1 / (r - l)) x) := by
      rw [intervalIntegral.integral_sub
        ((continuous_const.fun_mul hSA).intervalIntegrable (μ := MeasureTheory.volume) l p.1)
        ((continuous_const.fun_mul hS₀).intervalIntegrable (μ := MeasureTheory.volume) l p.1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hslope x p.2

/-- The mass denominator costs only the already fixed interval width. -/
theorem positiveReferenceMiddleMass_inv_le
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 4 * δ ≤ r - l) :
    (positiveReferenceMiddleMass l r δ)⁻¹ ≤ 2 / (r - l) := by
  have hw : 0 < r - l := by linarith
  have hlow := integral_positiveEndpointCutoff_complement_lower (l := l) (r := r) hδ
  have hhalf : (r - l) / 2 ≤ positiveReferenceMiddleMass l r δ := by
    change r - l - 2 * δ ≤ positiveReferenceMiddleMass l r δ at hlow
    linarith only [hgap, hlow]
  calc
    _ ≤ ((r - l) / 2)⁻¹ := inv_anti₀ (by positivity) hhalf
    _ = _ := by field_simp [hw.ne']

end ContinuousFlexibility.Analysis
