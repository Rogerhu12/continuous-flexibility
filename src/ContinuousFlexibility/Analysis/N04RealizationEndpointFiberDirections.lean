import ContinuousFlexibility.Analysis.N04RealizationPositiveCollarDirections
import ContinuousFlexibility.Analysis.N04RealizationPositiveCollarExit
import ContinuousFlexibility.Analysis.N04RealizationRadialGlueDirections
import ContinuousFlexibility.Analysis.EndpointFiberInterpolation

/-!
# The actual whole radial fiber interpolation with state parameters

Both finite collars use the supplied coefficients and prescribed widths.
Their reference exits agree on radial intervals fixed before the state.
The two actual glues therefore have genuine joint towers on the original
state neighborhood times the whole physical plane.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

def n04Realization_endpointFiberInterpolation_jointDirections
    (hU : IsOpen U) (n : ℕ) (l r c d : ℝ) (hcd : c < d)
    (η : Bool → ℝ) (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l))
    (A : E → Bool → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (A x side j))
    (J : ∀ side (j : Fin (n + 2)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => A p.1 side j p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => endpointFiberInterpolation n l r c d η (A p.1) p.2) := by
  let a : Bool → ℝ := fun side => if side then d else l
  let b : Bool → ℝ := fun side => if side then r else c
  let Y : Bool → E → PolarPoint → ℝ := fun side x =>
    endpointFiberCollar n l r c d η (A x) side
  let JY : ∀ side, SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => Y side p.1 p.2) := fun side =>
    n04Realization_positiveCollar_jointDirections hU n (a side) (b side)
      (η side) (a side) (b side - a side) side (fun x => A x side)
      (fun x hx => hA x hx side) (J side)
  have hexit (side : Bool) := n04Realization_positiveCollar_uniform_exit n
    (l := a side) (r := b side) (hη side) (hgap side) side
  let ε : Bool → ℝ := fun side => (hexit side).choose
  have hε (side : Bool) : 0 < ε side := (hexit side).choose_spec.1
  have hcenter (side : Bool) :
      (if side then a side else b side) = (if side then d else c) := by
    cases side <;> rfl
  have hmatch (side : Bool) (x : E) (hx : x ∈ U) (t : ℝ)
      (ht : t ∈ Metric.ball (if side then d else c) (ε side)) (θ : ℝ) :
      Y side x (t, θ) = t :=
    (hexit side).choose_spec.2 (A x side) (hA x hx side) t
      (by simpa only [hcenter side] using ht) θ
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R (hU.prod isOpen_univ)).congrOn (fun _ _ => by
      simp only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let inner : E → PolarPoint → ℝ := fun x =>
    radialGermGlue d Prod.fst (Y true x)
  let Jinner : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => inner p.1 p.2) :=
    n04Realization_radialGlue_jointDirections hU d (fun _ => Prod.fst) (Y true)
      JR (JY true) (hε true)
      (fun x hx t ht θ => (hmatch true x hx t ht θ).symm)
  let ε₀ : ℝ := min (ε false) ((d - c) / 2)
  have hε₀ : 0 < ε₀ := lt_min (hε false) (half_pos (sub_pos.mpr hcd))
  have hleft (x : E) (hx : x ∈ U) (t : ℝ)
      (ht : t ∈ Metric.ball c ε₀) (θ : ℝ) :
      Y false x (t, θ) = inner x (t, θ) := by
    have ht' : t ∈ Metric.ball c (ε false) :=
      Metric.ball_subset_ball (min_le_left _ _) ht
    have hu : t - c < ε₀ :=
      (abs_lt.mp (show |t - c| < ε₀ by
        simpa only [Metric.mem_ball, Real.dist_eq] using ht)).2
    have hsmall : ε₀ ≤ (d - c) / 2 := min_le_right _ _
    have htd : t < d := by linarith
    simp only [inner, radialGermGlue, if_pos htd]
    exact hmatch false x hx t ht' θ
  exact n04Realization_radialGlue_jointDirections hU c (Y false) inner
    (JY false) Jinner hε₀ hleft

end ContinuousFlexibility.Analysis
