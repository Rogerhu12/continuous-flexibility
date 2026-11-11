import ContinuousFlexibility.Radial.ModeOuterPoisson
import ContinuousFlexibility.Radial.MatchingTraceCalculus
import ContinuousFlexibility.Radial.SelectedBoundaryMargin
import ContinuousFlexibility.Radial.R07CapPullback

/-!
# The actual normalized exterior Poisson pair

The same natural solution is divided by its full value/flux state length
and by the square root of the physical matching scale. Its chosen closed
outer half-line supplies the representative; the other side and the open
inner interval are zero. Both frozen traces are proved for every cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def outerPoissonNormalized (lam : ℝ) (w u : ℝ → ℝ) (c x : ℝ) : ℝ :=
  u x / (sqrt ((outerFluxState lam w u c).1 ^ 2 +
    (outerFluxState lam w u c).2 ^ 2) * sqrt lam)

theorem contDiff_outerPoissonNormalized (lam : ℝ) (w : ℝ → ℝ) (c : ℝ)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (outerPoissonNormalized lam w u c) := hu.div_const _

theorem outerPoissonNormalized_traces {lam c : ℝ} {w u : ℝ → ℝ}
    (hlam : 0 < lam) (hstate : outerFluxState lam w u c ≠ 0) :
    let AB := outerUnitState (outerFluxState lam w u c)
    outerPoissonNormalized lam w u c c = AB.1 / sqrt lam ∧
      w c * deriv (outerPoissonNormalized lam w u c) c / sqrt lam = AB.2 := by
  let L := sqrt ((outerFluxState lam w u c).1 ^ 2 + (outerFluxState lam w u c).2 ^ 2)
  have hL : L ≠ 0 := (sqrt_pos.mpr (outerState_sq_pos hstate)).ne'
  have hs : sqrt lam ≠ 0 := (sqrt_pos.mpr hlam).ne'
  constructor
  · change u c / (L * sqrt lam) = (u c / L) / sqrt lam
    exact (div_div _ _ _).symm
  · change w c * deriv (fun x => u x / (L * sqrt lam)) c / sqrt lam =
      (w c * deriv u c / lam) / L
    rw [deriv_div_const]
    calc
      w c * (deriv u c / (L * sqrt lam)) / sqrt lam =
          (w c * deriv u c) / (L * (sqrt lam * sqrt lam)) := by
        field_simp [hL, hs] <;> ring
      _ = (w c * deriv u c) / (L * lam) := by
        rw [← pow_two, sq_sqrt hlam.le]
      _ = (w c * deriv u c / lam) / L := by
        rw [div_div, mul_comm L lam]

/-- Exact values and the actual within-derivative fluxes of a one-sided
representative. The equality at the other cut includes its zero flux. -/
theorem modeOuterSideFunction_matching_traces {D : ReferenceData}
    {M : RadialMatchingData D} (ha : D.a < M.innerLeft)
    (hm : M.innerLeft < M.innerRight) (hb : M.innerRight < D.b)
    (right : Bool) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (k : Fin 2) :
    let i : Fin 2 := if right then 1 else 0
    let p := modeOuterSideFunction M.innerLeft M.innerRight right u
    p (matchingCut D M k) = (if k = i then u (matchingCut D M k) else 0) ∧
      matchingOuterFlux D M p k =
        (if k = i then bufferSign k * D.w (matchingCut D M k) *
          deriv u (matchingCut D M k) / sqrt (M.boundaryScale k) else 0) := by
  let W := modeOuterSideLift M.innerLeft M.innerRight right u
  have hW : ContDiff ℝ ∞ W := contDiff_modeOuterSideLift _ _ right hu
  have hleft := modeOuterSideLift_left_germ hm le_rfl right u
  have hright := modeOuterSideLift_right_germ hm le_rfl right u
  have hvL := hleft.eq_of_nhds
  have hvR := hright.eq_of_nhds
  have hdL := hleft.deriv_eq
  have hdR := hright.deriv_eq
  have hrep : EqOn (modeOuterSideFunction M.innerLeft M.innerRight right u) W
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
    rw [modeOuterSideFunction_eq_extension hm right u]
    exact modeOuterExtension_eqOn_oneSided W
  have hv := hrep (matchingCut_mem_outerOneSided ha hb k)
  have hf : matchingOuterFlux D M
      (modeOuterSideFunction M.innerLeft M.innerRight right u) k =
      bufferSign k * D.w (matchingCut D M k) * deriv W (matchingCut D M k) /
        sqrt (M.boundaryScale k) := by
    rw [matchingOuterFlux_congr ha hm hb hrep]
    unfold matchingOuterFlux
    rw [(hW.differentiable (by simp) _).derivWithin
      (matchingOuter_uniqueDiffWithinAt ha hb k)]
  constructor
  · change modeOuterSideFunction M.innerLeft M.innerRight right u
      (matchingCut D M k) = _
    rw [hv]
    change modeOuterSideLift M.innerLeft M.innerRight right u (matchingCut D M k) = _
    fin_cases k <;> cases right <;>
      first | simpa [matchingCut] using hvL | simpa [matchingCut] using hvR
  · change matchingOuterFlux D M
      (modeOuterSideFunction M.innerLeft M.innerRight right u) k = _
    rw [hf]
    change bufferSign k * D.w (matchingCut D M k) *
      deriv (modeOuterSideLift M.innerLeft M.innerRight right u) (matchingCut D M k) /
        sqrt (M.boundaryScale k) = _
    fin_cases k <;> cases right <;> simp [matchingCut, hdL, hdR]

/-- Construct the actual L2 Poisson pair from the same selected natural
solution. The only scale identification is the physical `j^2 w(c)/c`.
The conclusion supplies the exterior half of every Poisson realization
clause, with no assumed matching realization or local inverse. -/
theorem exists_selectedOuterPoisson {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (M : RadialMatchingData D)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (right : Bool) {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v)
    (hN : RadialNaturalTail D right M.frequency
      (matchingCut D M (if right then 1 else 0)) v)
    (hlam : 0 < M.boundaryScale (if right then 1 else 0))
    (hscale : M.boundaryScale (if right then 1 else 0) =
      standInBoundaryScale ((M.frequency : ℝ) ^ 2)
        (D.w (matchingCut D M (if right then 1 else 0)))
        (matchingCut D M (if right then 1 else 0)))
    (hstate : selectedBoundaryState D M.frequency
      (bufferSign (if right then 1 else 0))
      (matchingCut D M (if right then 1 else 0)) v ≠ 0) :
    let i : Fin 2 := if right then 1 else 0
    let c := matchingCut D M i
    let lam := M.boundaryScale i
    let state := selectedBoundaryState D M.frequency (bufferSign i) c v
    let AB := outerUnitState state
    ∃ P : RadialModePair D, ∃ p : ℝ → ℝ,
      p = modeOuterSideFunction M.innerLeft M.innerRight right
        (fun r => v r / (sqrt (state.1 ^ 2 + state.2 ^ 2) * sqrt lam)) ∧
      ((P.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] p) ∧
      ((P.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
        (Ioo M.innerLeft M.innerRight)] fun _ => 0) ∧
      (∀ r ∈ Ioo M.innerLeft M.innerRight, p r = 0) ∧
      ContDiffOn ℝ 2 p (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) ∧
      P.2 = 0 ∧ ModeLocalEquation D M.frequency (matchingOuterRegion D M) P 0 ∧
      AB.1 ^ 2 + AB.2 ^ 2 = 1 ∧
      ∀ k, p (matchingCut D M k) = (if k = i then AB.1 else 0) /
          sqrt (M.boundaryScale k) ∧
        matchingOuterFlux D M p k = (if k = i then AB.2 else 0) := by
  let i : Fin 2 := if right then 1 else 0
  let c := matchingCut D M i
  let lam := M.boundaryScale i
  let w : ℝ → ℝ := fun r => bufferSign i * D.w r
  have hstate_eq : outerFluxState lam w v c =
      selectedBoundaryState D M.frequency (bufferSign i) c v := by
    change outerFluxState (M.boundaryScale i) w v c = _
    rw [hscale]
    rfl
  have hne : outerFluxState lam w v c ≠ 0 := by
    rw [hstate_eq]
    exact hstate
  let u := outerPoissonNormalized lam w v c
  have hu : ContDiff ℝ ∞ u := contDiff_outerPoissonNormalized lam w c hv
  let P := modeOuterPoissonVector D hD M.innerLeft M.innerRight right u hu
  let p := modeOuterSideFunction M.innerLeft M.innerRight right u
  have hc : c = if right then M.innerRight else M.innerLeft := by
    cases right <;> norm_num [c, i, matchingCut]
  have hODE : RadialHomogeneousOn D M.frequency
      (radialTailInterval D right (if right then M.innerRight else M.innerLeft)) u := by
    refine ⟨hu.contDiffOn, ?_⟩
    intro r hr
    have hvODE : radialJacobi ((M.frequency : ℝ) ^ 2) D.w v r = 0 := by
      apply hN.2.1.2
      change r ∈ radialTailInterval D right c
      rwa [hc]
    let d := sqrt ((outerFluxState lam w v c).1 ^ 2 +
      (outerFluxState lam w v c).2 ^ 2) * sqrt lam
    have he : u = fun x => d⁻¹ * v x := by
      funext x
      change v x / d = d⁻¹ * v x
      rw [div_eq_mul_inv, mul_comm]
    rw [he, radialJacobi_const_mul, hvODE, mul_zero]
  refine ⟨P, p, ?_, modeOuterPoissonVector_coe hD hm right u hu,
    modeOuterPoissonVector_zero_inside hD _ _ right u hu,
    (fun r hr => modeOuterSideFunction_zero_inside right u hr),
    modeOuterSideFunction_contDiffOn hm right hu, rfl,
    modeOuterPoissonVector_weak hD hm right hu hODE,
    outerUnitState_unit hstate, ?_⟩
  · exact congrArg (modeOuterSideFunction M.innerLeft M.innerRight right)
      (funext (fun r => congrArg
        (fun state : ℝ × ℝ => v r /
          (sqrt (state.1 ^ 2 + state.2 ^ 2) * sqrt lam)) hstate_eq))
  · intro k
    change p (matchingCut D M k) =
        (if k = i then (outerUnitState
          (selectedBoundaryState D M.frequency (bufferSign i) c v)).1 else 0) /
          sqrt (M.boundaryScale k) ∧
      matchingOuterFlux D M p k =
        (if k = i then (outerUnitState
          (selectedBoundaryState D M.frequency (bufferSign i) c v)).2 else 0)
    have ht : p (matchingCut D M k) =
        (if k = i then u (matchingCut D M k) else 0) ∧
        matchingOuterFlux D M p k =
          (if k = i then bufferSign k * D.w (matchingCut D M k) *
            deriv u (matchingCut D M k) / sqrt (M.boundaryScale k) else 0) :=
      modeOuterSideFunction_matching_traces ha hm hb right hu k
    have hn := outerPoissonNormalized_traces hlam hne
    rw [hstate_eq] at hn
    by_cases hk : k = i
    · subst k
      simp only [if_pos rfl] at ht ⊢
      exact ⟨ht.1.trans hn.1, ht.2.trans hn.2⟩
    · simpa only [if_neg hk, zero_div] using ht

end ContinuousFlexibility.Radial
