module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryPlaneSavedComposition

/-!
# Transport bounds from four scalar factors

The two scalar compositions and their pairings are estimated on an
abstract parameter space. Only the displayed transport identities and
the two region-preserving graphs are required from the actual geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_scalarFactors_transport_saved_prefix (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
    ∀ (U : Set E), IsOpen U →
    ∀ (φ α Y ρ : E × PolarPoint → ℝ)
      (Jφ : SmoothDirections (U ×ˢ univ) φ)
      (Jα : SmoothDirections (U ×ˢ univ) α)
      (JY : SmoothDirections (U ×ˢ univ) Y)
      (Jρ : SmoothDirections (U ×ˢ univ) ρ)
      (τ σ : E × PolarPoint → PolarPoint)
      (Jτ : SmoothDirections (U ×ˢ univ) τ)
      (Jσ : SmoothDirections (U ×ˢ univ) σ),
      EqOn τ (fun z => (Y (z.1, (z.2.1, φ z)), φ z)) (U ×ˢ univ) →
      EqOn σ (fun z => (ρ z, α (z.1, (ρ z, z.2.2)))) (U ×ˢ univ) →
    ∀ x ∈ U, ∀ Ω : Set PolarPoint,
      MapsTo (fun y => (y.1, φ (x, y))) Ω Ω →
      MapsTo (fun y => (ρ (x, y), y.2)) Ω Ω →
    ∀ (p q : Seminorm ℝ E) (R M H t : ℝ),
      0 ≤ R → 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t →
    ∀ K C : ℕ, 1 ≤ C →
      N04PlaneSavedWordBounds Jφ N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds Jα N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds JY N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds Jρ N K C x Ω p q R M H t →
      N04PlaneSavedWordBounds Jτ N K C x Ω p q R (max M (A * M ^ degree)) H t ∧
      N04PlaneSavedWordBounds Jσ N K C x Ω p q R (max M (A * M ^ degree)) H t := by
  let compositionData := n04PositiveGeometry_movingPoint_saved_prefix (E := E) (F := ℝ) N
  let A : ℝ := compositionData.choose
  have hA : 1 ≤ A := compositionData.choose_spec.1
  let degree : ℕ := compositionData.choose_spec.2.choose
  let hcomp := compositionData.choose_spec.2.choose_spec
  refine ⟨A, hA, degree, ?_⟩
  intro U hU φ α Y ρ Jφ Jα JY Jρ τ σ Jτ Jσ hτ hσ x hx Ω hφmap hρmap
    p q R M H t hR hM hH hHM ht K C hC hφ hα hY hρ
  let Jr : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => z.2.1) :=
    n04PositiveGeometry_spatialLinearDirections hU (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let Jθ : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => z.2.2) :=
    n04PositiveGeometry_spatialLinearDirections hU (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hr : N04PlaneSavedWordBounds Jr N K C x Ω p q R M H t :=
    N04PlaneSavedWordBounds.spatialLinear hU _ Jr hx hM
      ((ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ).trans hM) hH ht
  have hθ : N04PlaneSavedWordBounds Jθ N K C x Ω p q R M H t :=
    N04PlaneSavedWordBounds.spatialLinear hU _ Jθ hx hM
      ((ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ).trans hM) hH ht
  let Jφgraph : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (z.2.1, φ z)) := smoothDirectionsProd Jr Jφ
  let Jρgraph : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (ρ z, z.2.2)) := smoothDirectionsProd Jρ Jθ
  have hφgraph : N04PlaneSavedWordBounds Jφgraph N K C x Ω p q R M H t :=
    hr.pair Jφ Jφgraph hx hφ
  have hρgraph : N04PlaneSavedWordBounds Jρgraph N K C x Ω p q R M H t :=
    hρ.pair Jθ Jρgraph hx hθ
  let Jτr : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => Y (z.1, (z.2.1, φ z))) :=
    (smoothDirections_postcompCLM Jτ (ContinuousLinearMap.fst ℝ ℝ ℝ)).congr
      (fun z hz => congrArg Prod.fst (hτ hz))
  let Jσα : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => α (z.1, (ρ z, z.2.2))) :=
    (smoothDirections_postcompCLM Jσ (ContinuousLinearMap.snd ℝ ℝ ℝ)).congr
      (fun z hz => congrArg Prod.snd (hσ hz))
  have hτr : N04PlaneSavedWordBounds Jτr N K C x Ω p q R (A * M ^ degree) H t :=
    hcomp U Y (fun z => (z.2.1, φ z)) JY Jφgraph Jτr x hx Ω hφmap
      p q R M H t hR hM hH hHM ht K C hC hY hφgraph
  have hσα : N04PlaneSavedWordBounds Jσα N K C x Ω p q R (A * M ^ degree) H t :=
    hcomp U α (fun z => (ρ z, z.2.2)) Jα Jρgraph Jσα x hx Ω hρmap
      p q R M H t hR hM hH hHM ht K C hC hα hρgraph
  let Jτpair : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (Y (z.1, (z.2.1, φ z)), φ z)) :=
    smoothDirectionsProd Jτr Jφ
  let Jσpair : SmoothDirections (U ×ˢ univ)
      (fun z : E × PolarPoint => (ρ z, α (z.1, (ρ z, z.2.2)))) :=
    smoothDirectionsProd Jρ Jσα
  have hτpair := (hτr.enlarge hH ht (le_max_right M (A * M ^ degree))).pair
    Jφ Jτpair hx (hφ.enlarge hH ht (le_max_left M (A * M ^ degree)))
  have hσpair := (hρ.enlarge hH ht (le_max_left M (A * M ^ degree))).pair
    Jσα Jσpair hx (hσα.enlarge hH ht (le_max_right M (A * M ^ degree)))
  exact ⟨hτpair.congr hx Jτ (fun _ hz => (hτ hz).symm),
    hσpair.congr hx Jσ (fun _ hz => (hσ hz).symm)⟩

end ContinuousFlexibility.Analysis
