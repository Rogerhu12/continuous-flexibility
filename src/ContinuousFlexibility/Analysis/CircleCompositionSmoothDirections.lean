import ContinuousFlexibility.Analysis.CircleCompositionJetNormBounds
import ContinuousFlexibility.Analysis.CircleCompositionSecondEnvelopes
import ContinuousFlexibility.Analysis.SmoothDirectionsGluing

/-!
# Genuine smooth directional towers for joint circle composition

The local towers are realized in the original circle projective limit,
using actual scalar derivatives and a summable Taylor envelope. Open
low-seminorm boxes cover the full parameter space, and uniqueness of
directional derivatives glues their towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleCompositionSmoothDirectionsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem exists_circleChartComposition_smoothDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2),
      ∀ n x (v : Fin n → S.Space × S.Space),
        S.decode (J.D n x v) = circleChartCompositionJets hS travel n x v := by
  classical
  let p := pairGrading S.grading S.grading
  let f : S.Space × S.Space → S.Space := fun x =>
    circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2
  have htop := withSeminorms_pairGrading
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
  obtain ⟨base, hbounds⟩ := circleChartCompositionJets_uniform_normBounds
    hS hT hD hγ hinterp travel
  let V : (S.Space × S.Space) → Set (S.Space × S.Space) :=
    fun x₀ => {x | p base x < 1 + p base x₀}
  have hVopen (x₀ : S.Space × S.Space) : IsOpen (V x₀) :=
    isOpen_lt (htop.continuous_seminorm base) continuous_const
  have hVconvex (x₀ : S.Space × S.Space) : Convex ℝ (V x₀) := by
    simpa only [Seminorm.ball_zero_eq] using
      (p base).convex_ball (0 : S.Space × S.Space) (1 + p base x₀)
  have hlocal (x₀ : S.Space × S.Space) :
      ∃ J : SmoothDirections (V x₀) f, ∀ n x, x ∈ V x₀ → ∀ v : Fin n → S.Space × S.Space,
        S.decode (J.D n x v) = circleChartCompositionJets hS travel n x v := by
    apply exists_circle_smoothDirections_of_scalar_jets hS
      (fun m => ((material_circle_sample_weights_pos hT hD).1 m).le)
      (fun m => ((material_circle_sample_weights_pos hT hD).2 m).le)
      (hVopen x₀) (hVconvex x₀) f (circleChartCompositionJets hS travel)
    · intro n x hx v
      exact circleChartCompositionJets_member hS hT hD hγ travel n x v
    · exact hbounds (1 + p base x₀) (by positivity)
    · intro x hx
      rw [circleChartCompositionJets_zero]
      funext m θ
      rw [show f x = circleShiftedChartComposeLinear hS hT hD hγ travel x.1 x.2 from
        circleShiftedChartComposeContinuousLinear_apply hS hT hD hγ travel x.1 x.2,
        circleShiftedChartComposeLinear_decode]
      rfl
    · intro n x w v t ht m b θ
      exact circleChartCompositionJets_angular_line_hasDerivAt hS travel n x w v t m b θ
    · exact circleChartCompositionJets_secondEnvelopes hS hT hD hγ travel (hVopen x₀)
  choose J hJ using hlocal
  have hself (x : S.Space × S.Space) : x ∈ V x := by
    change p base x < 1 + p base x
    linarith
  obtain ⟨K, hK⟩ := exists_smoothDirections_of_open_cover
    (U := (univ : Set (S.Space × S.Space))) isOpen_univ V J
    (fun i x hx => mem_univ x) (fun x hx => ⟨x, hself x⟩)
  refine ⟨K, ?_⟩
  intro n x v
  rw [hK x n x (hself x)]
  exact hJ x n x (hself x) v

end ContinuousFlexibility.Statements
