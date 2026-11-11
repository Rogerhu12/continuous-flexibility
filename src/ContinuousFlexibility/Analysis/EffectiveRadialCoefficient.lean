import ContinuousFlexibility.Analysis.NegativeCanonicalClosedEffective
import ContinuousFlexibility.Scalar.HeightDerivatives

/-!
# Recovering the radial coefficient from the actual operator action

A radial quadratic centered at the evaluation radius has angular flux
identically zero on that vertical line. Its actual directional derivative
there is zero. The radial flux only differentiates the radial coefficient,
which N03 identifies with the original smooth coefficient.

Thus equality of the actual operators determines their radial coefficient
without assuming regularity of the stored mixed or angular coefficient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A function constant on the angular line has zero actual angular
partial there. The full-derivative convention agrees with that true
one-dimensional derivative even when the full derivative does not exist. -/
theorem angularPartial_eq_zero_of_constant_slice
    {f : PolarPoint → ℝ} {r θ c : ℝ}
    (hslice : ∀ η : ℝ, f (r, η) = c) :
    angularPartial f (r, θ) = 0 := by
  by_cases hf : DifferentiableAt ℝ f (r, θ)
  · have hline : HasDerivAt (fun η : ℝ => (r, η)) (0, 1) θ :=
      (hasDerivAt_const θ r).prodMk (hasDerivAt_id' θ)
    have hd := hf.hasFDerivAt.comp_hasDerivAt θ hline
    have he : f ∘ (fun η : ℝ => (r, η)) = (fun _ : ℝ => c) := by
      funext η
      exact hslice η
    rw [he] at hd
    exact hd.unique (hasDerivAt_const θ c)
  · simp only [angularPartial, fderiv_zero_of_not_differentiableAt hf,
      ContinuousLinearMap.zero_apply]

def radialCenteredSquare (r : ℝ) (p : PolarPoint) : ℝ := (p.1 - r) ^ 2

theorem contDiff_radialCenteredSquare (r : ℝ) :
    ContDiff ℝ ∞ (radialCenteredSquare r) :=
  (contDiff_fst.sub contDiff_const).pow 2

theorem radialCenteredSquare_partials (r : ℝ) (p : PolarPoint) :
    radialPartial (radialCenteredSquare r) p = 2 * (p.1 - r) ∧
      angularPartial (radialCenteredSquare r) p = 0 := by
  have hd : DifferentiableAt ℝ (fun q : PolarPoint => q.1 - r) p :=
    differentiableAt_fst.sub (differentiableAt_const r)
  constructor
  · rw [radialCenteredSquare, radialPartial_sq hd,
      radialPartial_sub differentiableAt_fst (differentiableAt_const r)]
    simp only [radialPartial_fst, radialPartial_const, sub_zero, mul_one]
  · rw [radialCenteredSquare, angularPartial_sq hd,
      angularPartial_sub differentiableAt_fst (differentiableAt_const r)]
    simp only [angularPartial_fst, angularPartial_const, sub_zero, mul_zero]

/-- The radial critical square identifies the actual radial coefficient.
The other two coefficient functions have no regularity assumptions. -/
theorem divergenceOperator_radialCenteredSquare
    {L : SymmetricCoefficients} {p : PolarPoint}
    (ha : DifferentiableAt ℝ L.a p) :
    divergenceOperator L (radialCenteredSquare p.1) p = 2 * L.a p := by
  have hrad : radialPartial (radialCenteredSquare p.1) =
      (fun q : PolarPoint => 2 * (q.1 - p.1)) :=
    funext fun q => (radialCenteredSquare_partials p.1 q).1
  have hang : angularPartial (radialCenteredSquare p.1) = (fun _ : PolarPoint => 0) :=
    funext fun q => (radialCenteredSquare_partials p.1 q).2
  have hzero : angularPartial
      (fun q : PolarPoint => L.b q * (2 * (q.1 - p.1))) p = 0 := by
    apply angularPartial_eq_zero_of_constant_slice (c := 0)
    intro η
    simp only [sub_self, mul_zero]
  have hlin : DifferentiableAt ℝ (fun q : PolarPoint => q.1 - p.1) p :=
    differentiableAt_fst.sub (differentiableAt_const p.1)
  have htwo : DifferentiableAt ℝ (fun q : PolarPoint => 2 * (q.1 - p.1)) p :=
    (differentiableAt_const (2 : ℝ)).mul hlin
  have hdr : radialPartial (fun q : PolarPoint => 2 * (q.1 - p.1)) p = 2 := by
    rw [radialPartial_mul (differentiableAt_const (2 : ℝ)) hlin,
      radialPartial_sub differentiableAt_fst (differentiableAt_const p.1)]
    simp only [radialPartial_const, radialPartial_fst, sub_zero, zero_mul,
      mul_one, zero_add]
  simp only [divergenceOperator, hrad, hang, mul_zero, add_zero]
  rw [hzero, add_zero, radialPartial_mul ha htwo, hdr]
  simp only [sub_self, mul_zero, zero_add]
  ring

/-- Equality on the single true quadratic probe suffices once the two
radial coefficients are differentiable at the point. -/
theorem radialCoefficient_eq_of_operator_action
    {L B : SymmetricCoefficients} {p : PolarPoint}
    (hLa : DifferentiableAt ℝ L.a p) (hBa : DifferentiableAt ℝ B.a p)
    (hop : divergenceOperator L (radialCenteredSquare p.1) p =
      divergenceOperator B (radialCenteredSquare p.1) p) :
    B.a p = L.a p := by
  rw [divergenceOperator_radialCenteredSquare hLa,
    divergenceOperator_radialCenteredSquare hBa] at hop
  linarith only [hop]

/-- On a negative canonical piece the actual smooth effective radial
coefficient is the original N03-preserved radial coefficient. Only the
original coefficient's actual first regularity is needed here. -/
theorem negativeCanonicalClosedCoefficients_radial_eq_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (hm : K.positive m = false)
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m)
    (hOriginal : DifferentiableAt ℝ (originalCoefficients D S C z).a p) :
    (negativeCanonicalClosedCoefficients S K z m).a p =
      (originalCoefficients D S C z).a p := by
  have hLaeq : (L.coefficients z).a = (originalCoefficients D S C z).a :=
    funext (hN03.1 z hz hsector)
  have hLa : DifferentiableAt ℝ (L.coefficients z).a p := by
    rw [hLaeq]
    exact hOriginal
  have hBa : DifferentiableAt ℝ (negativeCanonicalClosedCoefficients S K z m).a p :=
    (negativeCanonicalClosedCoefficients_contDiffAt hA hz hsector m
      (Ioo_subset_Icc_self hp.1)).1.differentiableAt (by simp)
  have hop := negativeCanonicalClosedOperator_of_parts hA hB hz hsector m hm
    (radialCenteredSquare p.1) (contDiff_radialCenteredSquare p.1).contDiffOn hp
  exact (radialCoefficient_eq_of_operator_action hLa hBa hop).trans
    (hN03.1 z hz hsector p)

end ContinuousFlexibility.Analysis
