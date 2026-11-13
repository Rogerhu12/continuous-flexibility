import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory

/-!
# A fixed exit neighborhood for every finite radial collar

The cutoff neighborhood is chosen before the endpoint data. The actual
primitive has the reference endpoint value and the reference derivative
throughout that neighborhood, so its equality with the fixed radial
coordinate is uniform in every later state and angle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n04Realization_positiveCollar_uniform_exit
    (n : ℕ) {l r δ : ℝ} (hδ : 0 < δ) (hgap : 2 * δ < r - l) (root : Bool) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ A : ℕ → ℝ → ℝ,
        (∀ j ≤ n + 1, ContDiff ℝ ∞ (A j)) →
      ∀ x ∈ Metric.ball (if root then l else r) ε, ∀ θ,
        positiveReferenceCollarCoordinate n l r δ l (r - l) root
          A Prod.fst (x, θ) = x := by
  let c : ℝ := if root then l else r
  let d : ℝ := if root then r else l
  have hlr : l < r := by linarith
  have hm : r - l ≠ 0 := (sub_pos.mpr hlr).ne'
  have hsep : δ ≤ |c - d| := by
    cases root with
    | false =>
        change δ ≤ |r - l|
        rw [abs_of_pos (sub_pos.mpr hlr)]
        linarith
    | true =>
        change δ ≤ |l - r|
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlr)]
        linarith
  have hone : ∀ᶠ x in 𝓝 c, positiveEndpointCutoff c δ x = 1 :=
    positiveEndpointCutoff_one_germ c δ
  have hzero : ∀ᶠ x in 𝓝 c, positiveEndpointCutoff d δ x = 0 :=
    positiveEndpointCutoff_zero_germ_of_separation hδ hsep
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hone.and hzero)
  refine ⟨ε, hε, ?_⟩
  intro A hA
  let P : Bool → PolarPoint → ℝ :=
    positiveReferenceCollarField n l r root A Prod.fst
  have hP (side : Bool) : ContDiff ℝ ∞ (P side) := by
    by_cases hs : side = root
    · simpa only [P, positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [P, positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  let B : Bool → PolarPoint → ℝ := fun side => radialPartial (P side)
  have hB (side : Bool) : ContDiff ℝ ∞ (B side) :=
    contDiff_cylinder_radialPartial (hP side)
  let Y : PolarPoint → ℝ :=
    positiveReferenceCollarCoordinate n l r δ l (r - l) root A Prod.fst
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_parameterizedPositiveReferenceCoordinate hB l r δ l (r - l)
  have hnot : (!root) ≠ root := by cases root <;> decide
  have hExitField : P (!root) = Prod.fst := by
    simp only [P, positiveReferenceCollarField, if_neg hnot]
  have hExit (t θ : ℝ) : B (!root) (t, θ) = 1 := by
    change radialPartial (P (!root)) (t, θ) = 1
    rw [hExitField]
    exact radialPartial_fst
  have hv (θ : ℝ) : Y (c, θ) = c := by
    cases root with
    | false =>
        change parameterizedPositiveReferenceCoordinate l r δ l (r - l) B (r, θ) = r
        exact (parameterizedPositiveReferenceCoordinate_right hB hδ hgap l
          (r - l) θ).trans (by ring)
    | true =>
        exact parameterizedPositiveReferenceCoordinate_left l r δ l (r - l) θ B
  have hder (θ t : ℝ) (ht : t ∈ Metric.ball c ε) :
      deriv (fun u => Y (u, θ)) t = 1 := by
    have hxone : positiveEndpointCutoff c δ t = 1 := (hball ht).1
    have hxzero : positiveEndpointCutoff d δ t = 0 := (hball ht).2
    have hexit := hExit t θ
    change deriv (fun u => parameterizedPositiveReferenceCoordinate l r δ l
      (r - l) B (u, θ)) t = 1
    rw [(hasDerivAt_parameterizedPositiveReferenceCoordinate hB hδ
      l (r - l) t θ).deriv]
    cases root <;>
      simp only [c, d, Bool.false_eq_true, ite_false, ite_true,
        Bool.not_false, Bool.not_true] at hxone hxzero hexit
    <;> simp only [positiveReferenceSlope, hxone, hxzero, one_mul, zero_mul,
      zero_add, add_zero, sub_self, sub_zero, mul_zero]
    <;> rw [hexit]
    <;> field_simp [hm]
  intro x hx θ
  have hYs : Differentiable ℝ (fun t => Y (t, θ)) :=
    (hY.comp (contDiff_id.prodMk (contDiff_const (c := θ)))).differentiable (by simp)
  have heq : EqOn (fun t => Y (t, θ)) (fun t : ℝ => t) (Metric.ball c ε) :=
    Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball c ε).isPreconnected
      hYs.differentiableOn differentiable_id.differentiableOn
      (fun t ht => (hder θ t ht).trans (hasDerivAt_id t).deriv.symm)
      (Metric.mem_ball_self hε) (hv θ)
  exact heq hx

end ContinuousFlexibility.Analysis
