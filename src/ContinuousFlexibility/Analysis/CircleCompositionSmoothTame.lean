import ContinuousFlexibility.Analysis.CircleCompositionLocalTame

/-!
# Joint smooth tame chart composition in the actual circle space

The genuine projective directional tower and its uniform one-high bounds
are already constructed. On a unit low-seminorm ball about a fixed point,
the low seminorm is bounded by one plus its value at the center. Applying
this elementary conversion on abstract spaces preserves the fixed loss
without unfolding the concrete projective circle model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleCompositionSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

private theorem smoothTameOn_of_uniform_oneHigh_exists
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) {f : E → F}
    (P : SmoothDirections univ f → Prop)
    (h : ∃ J : SmoothDirections univ f, P J ∧
      ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, p base x ≤ K → ∀ v : Fin n → E,
          q s (J.D n x v) ≤ C * tameJetSize p n s loss base x v) :
    SmoothTameOn p q univ f := by
  obtain ⟨J, _, hbound⟩ := h
  refine ⟨J, ?_⟩
  intro n x₀ hx₀
  obtain ⟨base, loss, hb⟩ := hbound n
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hb (1 + p base x₀)
    (add_nonneg zero_le_one (apply_nonneg (p base) x₀)) s
  refine ⟨C, hC, ?_⟩
  intro x hx hnear v
  have hbase : p base x ≤ 1 + p base x₀ := by
    calc
      p base x = p base ((x - x₀) + x₀) := by rw [sub_add_cancel]
      _ ≤ p base (x - x₀) + p base x₀ := map_add_le_add (p base) _ _
      _ ≤ 1 + p base x₀ := add_le_add hnear.le le_rfl
  exact hCs x hbase v

theorem smoothTameOn_circleChartComposition
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) := by
  exact smoothTameOn_of_uniform_oneHigh_exists
    (E := S.Space × S.Space) (F := S.Space)
    (pairGrading S.grading S.grading) S.grading
    (f := fun x : S.Space × S.Space =>
      circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2)
    (fun J => ∀ n x (v : Fin n → S.Space × S.Space),
      S.decode (J.D n x v) = circleChartCompositionJets hS travel n x v)
    (exists_circleChartComposition_uniform_oneHigh
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel)

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
