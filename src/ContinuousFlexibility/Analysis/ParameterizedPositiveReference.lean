module

public import ContinuousFlexibility.Analysis.PositiveReferenceCoordinate
public import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral

/-!
# Smooth positive radial interpolation with an angular parameter

The scalar slope and primitive are the existing explicit constructions,
applied at each angular parameter with the same fixed collars. Compact
parameter integration proves genuine joint smoothness. The prescribed
mass is any fixed positive number, so this may be used inside a reference
collar whose exit value is fixed before the varying state is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def parameterizedPositiveReferenceSlope (l r δ : ℝ)
    (A : Bool → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  positiveReferenceSlope l r δ (fun x => A false (x, p.2))
    (fun x => A true (x, p.2)) p.1

theorem contDiff_parameterizedPositiveReferenceSlope
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    (l r δ : ℝ) :
    ContDiff ℝ ∞ (parameterizedPositiveReferenceSlope l r δ A) := by
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hIntegrand : ContDiff ℝ ∞ (fun q : PolarPoint =>
      positiveEndpointCutoff l δ q.2 * A false (q.2, q.1) +
        positiveEndpointCutoff r δ q.2 * A true (q.2, q.1)) :=
    (((contDiff_positiveEndpointCutoff l δ).comp contDiff_snd).mul
      ((hA false).comp hswap)).add
      (((contDiff_positiveEndpointCutoff r δ).comp contDiff_snd).mul
        ((hA true).comp hswap))
  have hMass : ContDiff ℝ ∞ (fun θ : ℝ =>
      positiveReferenceEndMass l r δ (fun x => A false (x, θ))
        (fun x => A true (x, θ))) :=
    contDiff_parametric_intervalIntegral hIntegrand l r
  have hScale : ContDiff ℝ ∞ (fun θ : ℝ =>
      positiveReferenceScale l r δ (fun x => A false (x, θ))
        (fun x => A true (x, θ))) :=
    (contDiff_const.sub hMass).div_const (positiveReferenceMiddleMass l r δ)
  have hL := (contDiff_positiveEndpointCutoff l δ).comp
    (contDiff_fst : ContDiff ℝ ∞ (fun p : PolarPoint => p.1))
  have hR := (contDiff_positiveEndpointCutoff r δ).comp
    (contDiff_fst : ContDiff ℝ ∞ (fun p : PolarPoint => p.1))
  exact ((hL.mul (hA false)).add (hR.mul (hA true))).add
    ((hScale.comp contDiff_snd).mul ((contDiff_const.sub hL).sub hR))

/-- Dividing the input slopes by m and multiplying the primitive by m
sets its total mass to m while retaining the original endpoint slopes. -/
def parameterizedPositiveReferenceCoordinate (l r δ v m : ℝ)
    (A : Bool → PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  v + m * positiveReferenceCoordinate l r δ
    (fun x => A false (x, p.2) / m) (fun x => A true (x, p.2) / m) p.1

theorem contDiff_parameterizedPositiveReferenceCoordinate
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    (l r δ v m : ℝ) :
    ContDiff ℝ ∞ (parameterizedPositiveReferenceCoordinate l r δ v m A) := by
  let B : Bool → PolarPoint → ℝ := fun side p => A side p / m
  have hB : ∀ side, ContDiff ℝ ∞ (B side) := fun side => (hA side).div_const m
  have hS := contDiff_parameterizedPositiveReferenceSlope hB l r δ
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hPrimitive := (contDiff_parametric_primitive (hS.comp hswap) l).comp hswap
  exact contDiff_const.add (contDiff_const.mul hPrimitive)

theorem hasDerivAt_parameterizedPositiveReferenceCoordinate
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    {l r δ : ℝ} (hδ : 0 < δ) (v m x θ : ℝ) :
    HasDerivAt
      (fun t => parameterizedPositiveReferenceCoordinate l r δ v m A (t, θ))
      (m * positiveReferenceSlope l r δ
        (fun t => A false (t, θ) / m) (fun t => A true (t, θ) / m) x) x := by
  have hSlice (side : Bool) : ContDiff ℝ ∞ (fun t => A side (t, θ) / m) :=
    ((hA side).comp (contDiff_id.prodMk contDiff_const)).div_const m
  exact ((hasDerivAt_positiveReferenceCoordinate hδ
    (fun t _ => (hSlice false).contDiffAt)
    (fun t _ => (hSlice true).contDiffAt) x).const_mul m).const_add v

theorem parameterizedPositiveReferenceCoordinate_left
    (l r δ v m θ : ℝ) (A : Bool → PolarPoint → ℝ) :
    parameterizedPositiveReferenceCoordinate l r δ v m A (l, θ) = v := by
  simp only [parameterizedPositiveReferenceCoordinate,
    positiveReferenceCoordinate_left, mul_zero, add_zero]

theorem parameterizedPositiveReferenceCoordinate_right
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (v m θ : ℝ) :
    parameterizedPositiveReferenceCoordinate l r δ v m A (r, θ) = v + m := by
  have hSlice (side : Bool) : ContDiff ℝ ∞ (fun t => A side (t, θ) / m) :=
    ((hA side).comp (contDiff_id.prodMk contDiff_const)).div_const m
  have he := positiveReferenceCoordinate_right hδ hgap
    (fun t _ => (hSlice false).contDiffAt)
    (fun t _ => (hSlice true).contDiffAt)
  change v + m * positiveReferenceCoordinate l r δ
    (fun t => A false (t, θ) / m) (fun t => A true (t, θ) / m) r = v + m
  rw [he, mul_one]

/-- Uniform bounds on the given slopes supply a positive lower bound
for the actual derivative, independent of the angular parameter.
This is not a Jacobian hypothesis on the constructed coordinate. -/
theorem parameterizedPositiveReferenceCoordinate_uniform_lower
    {A : Bool → PolarPoint → ℝ} (hA : ∀ side, ContDiff ℝ ∞ (A side))
    {l r δ m L M : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l)
    (hm : 0 < m) (hL : 0 < L) (hM : 0 ≤ M)
    (hLow : ∀ side x, x ∈ Metric.ball (if side then r else l) δ →
      ∀ θ, L ≤ A side (x, θ))
    (hBound : ∀ side x, x ∈ Metric.ball (if side then r else l) δ →
      ∀ θ, |A side (x, θ)| ≤ M)
    (hsmall : 2 * M * δ ≤ m / 2) (v : ℝ) :
    let B : ℝ := m * min (L / m) ((1 / 2) / positiveReferenceMiddleMass l r δ);
    0 < B ∧ ∀ x θ, B ≤
      deriv (fun t => parameterizedPositiveReferenceCoordinate l r δ v m A (t, θ)) x := by
  have hMiddle : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ hgap
  have hscaled : 2 * (M / m) * δ ≤ (1 / 2 : ℝ) := by
    have hh : (2 * M * δ) / m ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hm).mpr (by linarith)
    calc
      _ = (2 * M * δ) / m := by ring
      _ ≤ _ := hh
  refine ⟨mul_pos hm (lt_min (div_pos hL hm) (div_pos (by norm_num) hMiddle)), ?_⟩
  intro x θ
  have hSlice (side : Bool) : ContDiff ℝ ∞ (fun t => A side (t, θ) / m) :=
    ((hA side).comp (contDiff_id.prodMk contDiff_const)).div_const m
  have hb (side : Bool) (t : ℝ) (ht : t ∈ Metric.ball (if side then r else l) δ) :
      |A side (t, θ) / m| ≤ M / m := by
    rw [abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right (hBound side t ht θ) hm.le
  have hEnd : positiveReferenceEndMass l r δ
      (fun t => A false (t, θ) / m) (fun t => A true (t, θ) / m) ≤ 1 / 2 :=
    (positiveReferenceEndMass_le hδ (div_nonneg hM hm.le)
      (fun t _ => (hSlice false).contDiffAt)
      (fun t _ => (hSlice true).contDiffAt) (hb false) (hb true)).trans hscaled
  have hScale : (1 / 2) / positiveReferenceMiddleMass l r δ ≤
      positiveReferenceScale l r δ
        (fun t => A false (t, θ) / m) (fun t => A true (t, θ) / m) :=
    div_le_div_of_nonneg_right (by linarith only [hEnd]) hMiddle.le
  have hSlope := positiveReferenceSlope_lower hδ hgap.le
    (fun t ht => div_le_div_of_nonneg_right (hLow false t ht θ) hm.le)
    (fun t ht => div_le_div_of_nonneg_right (hLow true t ht θ) hm.le) x
  rw [(hasDerivAt_parameterizedPositiveReferenceCoordinate hA hδ v m x θ).deriv]
  exact mul_le_mul_of_nonneg_left
    ((min_le_min le_rfl hScale).trans hSlope) hm.le

end ContinuousFlexibility.Analysis

