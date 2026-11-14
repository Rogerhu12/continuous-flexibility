import ContinuousFlexibility.Analysis.ReturnCorrectionPatching
import ContinuousFlexibility.Analysis.N01ActualRootGeometry

/-!
# A state-independent uncorrected band at each actual root

The selected cutoff is constant on a genuine neighborhood of each
endpoint. A smaller closed radial band therefore has zero cutoff
derivative. Disjointness of the actual negative components makes the
global corrected coefficients equal to the original coefficients on
this same band for every state and every angle. The band is selected
before either of those variables, and can be required to lie below any
previously selected positive root scale.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

/-- A constant germ contains a closed band on which both the value and
the actual ordinary derivative are fixed. No smoothness hypothesis is
needed outside this band. -/
theorem exists_closed_constant_band_of_eventuallyEq_const
    {f : ℝ → ℝ} {r c R : ℝ}
    (hf : f =ᶠ[𝓝 r] (fun _ => c)) (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ∀ t ∈ Icc (-ρ) ρ,
      f (r + t) = c ∧ deriv f (r + t) = 0 := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hf
  let ρ := min (R / 2) (η / 2)
  have hρ : 0 < ρ := lt_min (half_pos hR) (half_pos hη)
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρη : ρ < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro t ht
  have hy : r + t ∈ Metric.ball r η := by
    rw [Metric.mem_ball, Real.dist_eq]
    have he : r + t - r = t := by ring
    rw [he]
    exact (abs_le.mpr ht).trans_lt hρη
  have he : f =ᶠ[𝓝 (r + t)] (fun _ => c) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with y hy
    exact hball hy
  exact ⟨hball hy, by simpa only [deriv_const] using he.deriv_eq⟩

/-- The actual cutoff produces one closed inward band, uniformly in
all states and angles. The two endpoint orientations use the same
construction. The reference root itself belongs to no open negative
component, so the global patch is also inactive at that endpoint. -/
theorem n01_exists_fixedCutoff_root_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (χ : ℕ → ℝ → ℝ)
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (m : ℕ) (rightEnd : Bool) {R : ℝ} (hR : 0 < R) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ρ < C.right m - C.left m ∧
      (∀ x ∈ Icc (0 : ℝ) ρ,
        χ m (r + σ * x) = (if rightEnd then 1 else 0) ∧
        deriv (χ m) (r + σ * x) = 0) ∧
      ∀ (z : AnnularState S × ℝ) (θ : ℝ) (x : ℝ), x ∈ Icc (0 : ℝ) ρ →
        (returnCorrectedCoefficients D S C χ z).a (r + σ * x, θ) =
            (originalCoefficients D S C z).a (r + σ * x, θ) ∧
        (returnCorrectedCoefficients D S C χ z).b (r + σ * x, θ) =
            (originalCoefficients D S C z).b (r + σ * x, θ) ∧
        (returnCorrectedCoefficients D S C χ z).c (r + σ * x, θ) =
            (originalCoefficients D S C z).c (r + σ * x, θ) := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hw : 0 < C.right m - C.left m := sub_pos.mpr (hC.1 m).2.1
  have hconst : χ m =ᶠ[𝓝 r] (fun _ => if rightEnd then (1 : ℝ) else 0) := by
    cases rightEnd
    · exact (hend m).1
    · exact (hend m).2
  obtain ⟨ρ, hρ, hρmin, hband⟩ :=
    exists_closed_constant_band_of_eventuallyEq_const hconst (lt_min hR hw)
  have hρR : ρ < R := hρmin.trans_le (min_le_left _ _)
  have hρw : ρ < C.right m - C.left m := hρmin.trans_le (min_le_right _ _)
  have hcut (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ρ) :
      χ m (r + σ * x) = (if rightEnd then 1 else 0) ∧
      deriv (χ m) (r + σ * x) = 0 := by
    apply hband
    cases rightEnd <;>
      simp only [σ, n01ComponentRootOrientation, Bool.false_eq_true,
        ite_false, ite_true, one_mul, neg_one_mul] <;>
      constructor <;> linarith only [hx.1, hx.2, hρ]
  refine ⟨ρ, hρ, hρR, hρw, hcut, ?_⟩
  intro z θ x hx
  refine ⟨rfl, ?_⟩
  by_cases hxzero : x = 0
  · subst x
    simp only [mul_zero, add_zero]
    apply returnCorrectedCoefficients_eq_original_at_of_inactive
    rintro ⟨j, hj, _⟩
    have hroot : deriv D.w r = 0 := (n01_component_root_data hN m rightEnd).2.1
    have hneg := hC.2.2.2.1 j r hj
    linarith only [hroot, hneg]
  · have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
    have hxw : x < C.right m - C.left m := hx.2.trans_lt hρw
    have hp : r + σ * x ∈ Ioo (C.left m) (C.right m) := by
      cases rightEnd <;>
        simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
          Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
        constructor <;> linarith only [hxp, hxw]
    exact returnCorrectedCoefficients_eq_original_at_of_deriv_zero
      (D := D) hC.2.2.1 χ z m (r + σ * x, θ) hp (hcut x hx).2

end ContinuousFlexibility.Analysis
