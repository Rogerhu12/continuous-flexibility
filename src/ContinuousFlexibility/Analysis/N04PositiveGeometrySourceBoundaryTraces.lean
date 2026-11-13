import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceAngleDefect
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceSamplePrefix
import ContinuousFlexibility.Analysis.OneSidedBoundaryTaylorRepresentative

/-!
# Actual radial endpoint traces of the retained source

Positive orders are fixed unit-vector evaluations of the original full
source jets. At order zero the radial trace is the fixed endpoint and
the angular trace is the actual inverse-label displacement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_radialBoundaryJet_postcompCLM
    (L : PolarPoint →L[ℝ] ℝ) {f : PolarPoint → PolarPoint} {c θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (n : ℕ) :
    radialBoundaryJet (fun p => L (f p)) c n θ =
      L (iteratedFDeriv ℝ n f (c, θ) (fun _ => (1, 0))) := by
  rw [n06_radialBoundaryJet_eq_frechet n (L.contDiff.contDiffAt.comp (c, θ) hf)]
  exact congrArg (fun A : PolarPoint [×n]→L[ℝ] ℝ => A (fun _ => (1, 0)))
    (L.iteratedFDeriv_comp_left hf (by simp : (n : ℕ∞ω) ≤ ∞))

section Projection

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E × ℝ → PolarPoint → PolarPoint} {c : ℝ} {n : ℕ}

def n04PositiveGeometry_boundaryRadialProjection_directions
    (J : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ n (f y) (c, y.2)))
    (hf : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2))
    (L : PolarPoint →L[ℝ] ℝ) :
    SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (fun p => L (f y p)) c n y.2) :=
  (smoothDirections_postcompCLM
    (n04PositiveGeometry_boundaryFixedEvaluation_directions J (fun _ => (1, 0))) L).congr
      (fun y hy => (n04PositiveGeometry_radialBoundaryJet_postcompCLM L (hf y hy) n).symm)

theorem N04BoundaryWordBounds.radialProjection
    {J : SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ n (f y) (c, y.2))}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hb : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hf : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2))
    (L : PolarPoint →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (hx : x ∈ U)
    (Q : SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (fun p => L (f y p)) c n y.2)) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  have h := (hb.fixedEvaluation (fun _ => (1, 0)) (fun _ => by simp)).postcompCLM L hL
  exact h.congr hx
    (fun y hy => (n04PositiveGeometry_radialBoundaryJet_postcompCLM L (hf y hy) n).symm)

end Projection

variable {W : N04RealizationStart} {X : N04RealizationChoice W}
  {base : ℕ} {ε : ℝ}

theorem n04PositiveGeometry_source_root_smooth
    (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (y : (StateDirections W.S × ℝ) × ℝ)
    (hy : y ∈ sectorNeighborhood W.S base ε ε ×ˢ univ) :
    ContDiffAt ℝ ∞ (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
      (liftSectorParameter W.S W.C y.1)) (n04PositiveEndpoint i side, y.2) :=
  (n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03 W.field
    X.e₀ (X.src i side)
    (liftSectorParameter_mem_stateNeighborhood (C := W.C)
      (sectorNeighborhood_mono W.S hb hεW hεW hy.1) le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector y.1)).root_smooth y.2

theorem n04PositiveGeometry_sourceAngleTrace_contDiff
    (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : ℕ)
    {z : StateDirections W.S × ℝ} (hz : z ∈ sectorNeighborhood W.S base ε ε) :
    ContDiff ℝ ∞ (fun θ => n04PositiveGeometry_sourceAngleTrace W X i side j (z, θ)) := by
  have h := contDiff_radialBoundaryJet_of_contDiffAt (n04PositiveEndpoint i side)
    (fun θ => (n04PositiveGeometry_source_root_smooth (X := X) hb hεW i side
      (z, θ) ⟨hz, mem_univ θ⟩).snd) j
  apply h.sub
  by_cases hj : j = 0
  · simpa only [if_pos hj] using (contDiff_id : ContDiff ℝ ∞ (fun θ : ℝ => θ))
  · simpa only [if_neg hj] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

theorem n04PositiveGeometry_sourceAngleTrace_period
    (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : ℕ)
    {z : StateDirections W.S × ℝ} (hz : z ∈ sectorNeighborhood W.S base ε ε) :
    Function.Periodic (fun θ => n04PositiveGeometry_sourceAngleTrace W X i side j (z, θ))
      Real.pi := by
  let hd := n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03
    W.field X.e₀ (X.src i side)
    (liftSectorParameter_mem_stateNeighborhood (C := W.C)
      (sectorNeighborhood_mono W.S hb hεW hεW hz) le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z)
  intro θ
  have he := radialBoundaryJet_angleAffine_on_closedStrip (α := 1) (β := Real.pi)
    (τ := fun t : ℝ => t + Real.pi) hd.interval hd.endpoint
    (fun η => (hd.root_smooth η).snd) (contDiff_id.add contDiff_const)
    (fun r hr η => by
      simpa only [Prod.mk_add_mk, add_zero, Prod.snd_add, one_mul, add_comm]
        using congrArg Prod.snd (hd.period_add (r, η) ⟨hr, mem_univ η⟩)) j θ
  change radialBoundaryJet _ _ j (θ + Real.pi) - (if j = 0 then θ + Real.pi else 0) =
    radialBoundaryJet _ _ j θ - (if j = 0 then θ else 0)
  rw [he]
  by_cases hj : j = 0 <;> simp only [hj, if_pos, if_neg, one_mul] <;> ring

def n04PositiveGeometry_sourceProjectedTrace_joint
    (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (L : PolarPoint →L[ℝ] ℝ) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y => radialBoundaryJet (fun p => L
        (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
          (liftSectorParameter W.S W.C y.1) p)) (n04PositiveEndpoint i side) j y.2) :=
  n04PositiveGeometry_boundaryRadialProjection_directions
    (n04PositiveGeometry_sourceJet_joint W X hb hε hεW hεone hflow i side m hm hctx j hj hj4)
    (n04PositiveGeometry_source_root_smooth (X := X) hb hεW i side) L

def n04PositiveGeometry_sourceAngleTrace_joint
    (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (j : ℕ) (hj4 : j ≤ 4) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceAngleTrace W X i side j) := by
  by_cases hj : j = 0
  · subst j
    exact n04PositiveGeometry_sourceAngleTrace_zero_joint W X hb hεW i side
  · exact (n04PositiveGeometry_sourceProjectedTrace_joint hb hε hεW hεone hflow
      i side m hm hctx j (by omega) hj4 (ContinuousLinearMap.snd ℝ ℝ ℝ)).congr
        (fun _ _ => by simp only [n04PositiveGeometry_sourceAngleTrace, if_neg hj, sub_zero,
          ContinuousLinearMap.coe_snd'])

def n04PositiveGeometry_sourceRadialTrace
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : ℕ)
    (y : (StateDirections W.S × ℝ) × ℝ) : ℝ :=
  radialBoundaryJet (fun p =>
    (n04PositiveSourceMap (X.src i side) (W.A X.e₀) (liftSectorParameter W.S W.C y.1) p).1)
    (n04PositiveEndpoint i side) j y.2

theorem n04PositiveGeometry_sourceRadialTrace_zero_eq
    (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    {y : (StateDirections W.S × ℝ) × ℝ}
    (hy : y ∈ sectorNeighborhood W.S base ε ε ×ˢ univ) :
    n04PositiveGeometry_sourceRadialTrace W X i side 0 y = n04PositiveEndpoint i side := by
  have h := n04PositiveGeometry_source_endpoint_value W X i side m hm
    (liftSectorParameter_mem_stateNeighborhood (C := W.C)
      (sectorNeighborhood_mono W.S hb hεW hεW hy.1) le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector y.1) y.2
  exact congrArg Prod.fst h

def n04PositiveGeometry_sourceRadialTrace_joint
    (hb : W.base ≤ base) (hε : 0 < ε) (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool)
    (m : ℕ) (hm : (X.src i side).val = some m)
    (hctx : N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m (!side))
    (j : ℕ) (hj4 : j ≤ 4) :
    SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceRadialTrace W X i side j) := by
  by_cases hj : j = 0
  · subst j
    exact (smoothDirections_constant
      ((sectorNeighborhood_isOpen W.S base ε ε).prod isOpen_univ)
      (n04PositiveEndpoint i side)).congr
        (fun y hy => (n04PositiveGeometry_sourceRadialTrace_zero_eq hb hεW i side m hm hy).symm)
  · exact n04PositiveGeometry_sourceProjectedTrace_joint hb hε hεW hεone hflow
      i side m hm hctx j (by omega) hj4 (ContinuousLinearMap.fst ℝ ℝ ℝ)

end ContinuousFlexibility.Analysis
