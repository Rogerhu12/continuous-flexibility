import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryComposition
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryTraceOperations

/-!
# Actual radial traces of a boundary composition

Positive radial orders use the finite spatial chain rule. The zeroth
order uses the true outer value at the source point, so no bound on the
unwrapped source angle and no normalization of that value is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def n04PositiveGeometry_boundaryRadialComposition_directions
    {U : Set E} (hU : IsOpen U) (c : ℝ) (n : ℕ)
    (f : E × ℝ → PolarPoint → ℝ) (g : E × ℝ → PolarPoint → PolarPoint)
    (hf : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (g y (c, y.2)))
    (hg : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2))
    (JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => iteratedFDeriv ℝ j (f y) (g y (c, y.2))))
    (JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
      SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (g y) (c, y.2) v)) :
    SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (f y ∘ g y) c n y.2) := by
  by_cases hn : 0 < n
  · exact (n04PositiveGeometry_boundaryComposition_directions n hn hU f g
      (fun y => (c, y.2)) hf hg (fun j _ hj => JF j hj) JG (fun _ => (1, 0))).congr
        (fun y hy => (n06_radialBoundaryJet_eq_frechet n
          ((hf y hy).comp _ (hg y hy))).symm)
  · have hn0 : n = 0 := by omega
    subst n
    exact (n04PositiveGeometry_boundaryFixedEvaluation_directions (JF 0 le_rfl) Fin.elim0).congr
      (fun y _ => by simp only [iteratedFDeriv_zero_apply, radialBoundaryJet,
        iteratedDeriv_zero, Function.comp_apply])

theorem n04PositiveGeometry_boundaryRadialComposition_bound (n N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U : Set E}, IsOpen U → ∀ c : ℝ,
      ∀ (f : E × ℝ → PolarPoint → ℝ) (g : E × ℝ → PolarPoint → PolarPoint),
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (g y (c, y.2))) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2)) →
      ∀ JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => iteratedFDeriv ℝ j (f y) (g y (c, y.2))),
      ∀ JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → PolarPoint,
        SmoothDirections (U ×ˢ univ)
          (fun y => iteratedFDeriv ℝ j (g y) (c, y.2) v),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (f y ∘ g y) c n y.2),
      ∀ K s d, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      (∀ j hj, N04BoundaryWordBounds (JF j hj) K s d x θ P M H t shift) →
      (∀ j hj hjn v, (∀ a, ‖v a‖ ≤ 1) →
        N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ (n + 1 + 2 * N)) H t shift := by
  by_cases hn : 0 < n
  · obtain ⟨C, hC, hc⟩ := n04PositiveGeometry_boundaryComposition_bound
      (X := E) (E := PolarPoint) (F := ℝ) (G := PolarPoint) N n hn
    refine ⟨C, hC, ?_⟩
    intro U hU c f g hf hg JF JG Q K s d hN x hx θ P M H t hM hH hHM ht shift hF hG
    let J := n04PositiveGeometry_boundaryComposition_directions n hn hU f g
      (fun y => (c, y.2)) hf hg (fun j _ hj => JF j hj) JG (fun _ => (1, 0))
    have hb := hc hU f g (fun y => (c, y.2)) hf hg (fun j _ hj => JF j hj) JG
      K s d hN x hx θ P M H t hM hH hHM ht shift
      (fun j _ hj => hF j hj) hG (fun _ => (1, 0))
      (fun _ => by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one]) J
    exact hb.congr hx (fun y hy => (n06_radialBoundaryJet_eq_frechet n
      ((hf y hy).comp _ (hg y hy))).symm)
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨1, le_rfl, ?_⟩
    intro U hU c f g hf hg JF JG Q K s d hN x hx θ P M H t hM hH hHM ht shift hF hG
    have hb := (hF 0 le_rfl).fixedEvaluation Fin.elim0 (fun i => i.elim0)
    have hcost : M ≤ (1 : ℝ) * M ^ (0 + 1 + 2 * N) := by
      simpa only [one_mul, pow_one] using
        pow_le_pow_right₀ hM (show 1 ≤ 0 + 1 + 2 * N by omega)
    exact (hb.enlarge hH (zero_le_one.trans ht) hcost).congr hx
      (fun y _ => by simp only [iteratedFDeriv_zero_apply, radialBoundaryJet,
        iteratedDeriv_zero, Function.comp_apply])

end ContinuousFlexibility.Analysis
