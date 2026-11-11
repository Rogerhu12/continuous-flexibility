import ContinuousFlexibility.Analysis.ParameterizedPositiveReference
import ContinuousFlexibility.Analysis.CylinderSobolev

/-!
# Genuine endpoint germs for the parameterized positive primitive

The cutoff identities hold on one radial neighborhood before the angle
is selected. Equality of actual radial derivatives and the prescribed
endpoint values then gives equality on that whole neighborhood times
the angular line. The result is a genuine planar germ, which is enough
to glue the exit to the fixed reference coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Both endpoint fields are handled by the same argument. The mass and
base value are fixed, while the fields may depend smoothly on the angle. -/
theorem parameterizedPositiveReferenceCoordinate_endpoint_germ
    {F : Bool → PolarPoint → ℝ} (hF : ∀ side, ContDiff ℝ ∞ (F side))
    {l r δ v m : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (hm : m ≠ 0)
    (hvalue : ∀ side η, F side (if side then r else l, η) =
      if side then v + m else v) (side : Bool) (θ : ℝ) :
    parameterizedPositiveReferenceCoordinate l r δ v m
      (fun side => radialPartial (F side)) =ᶠ[𝓝 (if side then r else l, θ)]
      F side := by
  let A : Bool → PolarPoint → ℝ := fun side => radialPartial (F side)
  let Y := parameterizedPositiveReferenceCoordinate l r δ v m A
  let c : ℝ := if side then r else l
  let d : ℝ := if side then l else r
  have hA : ∀ side, ContDiff ℝ ∞ (A side) :=
    fun side => contDiff_cylinder_radialPartial (hF side)
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_parameterizedPositiveReferenceCoordinate hA l r δ v m
  have hsep : 0 ≤ r - l := by linarith
  have hcd : δ ≤ |c - d| := by
    cases side with
    | false =>
        change δ ≤ |l - r|
        rw [abs_sub_comm, abs_of_nonneg hsep]
        linarith
    | true =>
        change δ ≤ |r - l|
        rw [abs_of_nonneg hsep]
        linarith
  have hone : ∀ᶠ x in 𝓝 c, positiveEndpointCutoff c δ x = 1 :=
    positiveEndpointCutoff_one_germ c δ
  have hzero : ∀ᶠ x in 𝓝 c, positiveEndpointCutoff d δ x = 0 :=
    positiveEndpointCutoff_zero_germ_of_separation hδ hcd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hone.and hzero)
  have hv (η : ℝ) : Y (c, η) = F side (c, η) := by
    cases side with
    | false =>
        exact (parameterizedPositiveReferenceCoordinate_left l r δ v m η A).trans
          (hvalue false η).symm
    | true =>
        exact (parameterizedPositiveReferenceCoordinate_right hA hδ hgap v m η).trans
          (hvalue true η).symm
  have hder (η x : ℝ) (hx : x ∈ Metric.ball c ε) :
      deriv (fun t => Y (t, η)) x = deriv (fun t => F side (t, η)) x := by
    have hxone : positiveEndpointCutoff c δ x = 1 := (hball hx).1
    have hxzero : positiveEndpointCutoff d δ x = 0 := (hball hx).2
    rw [(hasDerivAt_parameterizedPositiveReferenceCoordinate hA hδ v m x η).deriv,
      deriv_cylinder_radial_slice ((hF side).differentiable (by simp)) x η]
    cases side <;>
      simp only [c, d, Bool.false_eq_true, ite_false, ite_true] at hxone hxzero ⊢
    <;> simp only [positiveReferenceSlope, hxone, hxzero, one_mul, zero_mul,
      zero_add, add_zero, sub_self, sub_zero, mul_zero, A]
    <;> field_simp [hm]
    <;> ring
  have heq (η : ℝ) : EqOn (fun x => Y (x, η)) (fun x => F side (x, η))
      (Metric.ball c ε) := by
    have hYs : Differentiable ℝ (fun x => Y (x, η)) :=
      (hY.comp (contDiff_id.prodMk (contDiff_const (c := η)))).differentiable (by simp)
    have hFs : Differentiable ℝ (fun x => F side (x, η)) :=
      ((hF side).comp (contDiff_id.prodMk (contDiff_const (c := η)))).differentiable (by simp)
    exact Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball c ε).isPreconnected
      hYs.differentiableOn hFs.differentiableOn (fun x hx => hder η x hx)
      (Metric.mem_ball_self hε) (hv η)
  have hf : Tendsto (fun p : PolarPoint => p.1) (𝓝 (c, θ)) (𝓝 c) :=
    continuous_fst.tendsto (c, θ)
  filter_upwards [hf.eventually (Metric.ball_mem_nhds c hε)] with p hp
  exact heq p.2 hp

/-- All finite radial jets are actual derivatives of the constructed
primitive. They follow from the planar germ, without jet axioms. -/
theorem iteratedDeriv_parameterizedPositiveReferenceCoordinate_endpoint
    {F : Bool → PolarPoint → ℝ} (hF : ∀ side, ContDiff ℝ ∞ (F side))
    {l r δ v m : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (hm : m ≠ 0)
    (hvalue : ∀ side η, F side (if side then r else l, η) =
      if side then v + m else v) (side : Bool) (θ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => parameterizedPositiveReferenceCoordinate l r δ v m
      (fun side => radialPartial (F side)) (x, θ)) (if side then r else l) =
      iteratedDeriv k (fun x => F side (x, θ)) (if side then r else l) := by
  have h := parameterizedPositiveReferenceCoordinate_endpoint_germ
    hF hδ hgap hm hvalue side θ
  have hline : Tendsto (fun x : ℝ => (x, θ)) (𝓝 (if side then r else l))
      (𝓝 (if side then r else l, θ)) :=
    (continuous_id.prodMk continuous_const).tendsto _
  exact ((h.comp_tendsto hline).iteratedDeriv k).eq_of_nhds

end ContinuousFlexibility.Analysis

