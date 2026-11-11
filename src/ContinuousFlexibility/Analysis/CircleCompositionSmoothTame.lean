import ContinuousFlexibility.Analysis.CircleCompositionLocalTame

/-!
# Joint smooth tame chart composition in the actual circle space

The genuine projective directional tower and its uniform homogeneous
bounds are already constructed. A unit low-seminorm ball around each
point gives the frozen local estimate, with a loss fixed before the
output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleCompositionSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem smoothTameOn_of_uniform_jet_bounds
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [ContinuousConstSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {f : E → F} (J : SmoothDirections univ f)
    (hbound : ∀ k : ℕ, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K →
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, p base x ≤ K →
        ∀ v : Fin k → E,
          q s (J.D k x v) ≤ C * tameJetSize p k s loss base x v) :
    SmoothTameOn p q univ f := by
  refine ⟨J, ?_⟩
  intro k x₀ hx₀
  obtain ⟨base, loss, hb⟩ := hbound k
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hc⟩ := hb (1 + p base x₀)
    (add_nonneg zero_le_one (apply_nonneg _ _)) s
  refine ⟨C, hC, ?_⟩
  intro x hx hnear v
  have hxbound : p base x ≤ 1 + p base x₀ := by
    calc
      p base x = p base ((x - x₀) + x₀) :=
        congrArg (p base) (sub_add_cancel x x₀).symm
      _ ≤ p base (x - x₀) + p base x₀ :=
        map_add_le_add (p base) (x - x₀) x₀
      _ ≤ 1 + p base x₀ := add_le_add_right hnear.le _
  exact hc x hxbound v

theorem smoothTameOn_circleChartComposition
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) := by
  classical
  let h := exists_circleChartComposition_uniform_oneHigh
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  let J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) :=
    h.choose
  exact smoothTameOn_of_uniform_jet_bounds
    (pairGrading S.grading S.grading) S.grading J h.choose_spec.2

theorem smoothTameOn_circleShiftedChartComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeLinear hS hT hD hγ travel x.1 x.2) := by
  apply smoothTameOn_congr (smoothTameOn_circleChartComposition hS hT hD hγ hinterp travel)
  intro x hx
  exact circleShiftedChartComposeContinuousLinear_apply hS hT hD hγ travel x.1 x.2

end ContinuousFlexibility.Statements
