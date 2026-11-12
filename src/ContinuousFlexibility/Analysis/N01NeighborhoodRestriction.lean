import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.MaterialSampleCofinite
import ContinuousFlexibility.Analysis.N01cStateSeminorms
import ContinuousFlexibility.Analysis.N01cBoundsRestriction

/-!
# Restricting the common N01 neighborhood

Increasing the controlled seminorm order and decreasing the radius
preserve the same geometric data and all N01 towers.  The directional
derivatives themselves are retained; only their open domain is restricted.
This permits a later uniform geometric smallness estimate to choose its
neighborhood without replacing any of the actual returns.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01NeighborhoodRestrictionStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

theorem stateNeighborhood_isOpen (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  have hc : Continuous (fun z : AnnularState S × ℝ =>
      stateGrading S base (z.1 - C.referenceState)) :=
    ((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
      (continuous_fst.sub continuous_const)
  exact (isOpen_lt hc continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

/-- Restriction preserves a one-high-factor bound in the same tower.
The target measurement may include a fixed spatial weight. -/
theorem smoothDirections_restrict_oneHigh_bound
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {U V : Set E} {f : E → F} {q : ℕ → Seminorm ℝ E}
    {k base base' high : ℕ} {K : ℝ} (measure : F → ℝ) (x₀ : E)
    (hV : IsOpen V) (hVU : V ⊆ U) (hq : Monotone q)
    (hb : base ≤ base') (hK : 0 ≤ K)
    (hbound : ∃ J : SmoothDirections U f, ∀ x ∈ U, ∀ v : Fin k → E,
      measure (J.D k x v) ≤ K * oneHighVariationWeight q base high (x - x₀) v) :
    ∃ J : SmoothDirections V f, ∀ x ∈ V, ∀ v : Fin k → E,
      measure (J.D k x v) ≤ K * oneHighVariationWeight q base' high (x - x₀) v := by
  obtain ⟨J, hJ⟩ := hbound
  refine ⟨J.restrict hV hVU, fun x hx v => ?_⟩
  exact (hJ x (hVU hx) v).trans (mul_le_mul_of_nonneg_left
    (oneHighVariationWeight_mono hq hb le_rfl (x - x₀) v) hK)

theorem stateNeighborhood_mono (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) {base base' : ℕ} {ε ε' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨((solve_stateGrading_monotone S hb (z.1 - C.referenceState)).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hε⟩

theorem N01Properties.restrict_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss : ℕ} {ε ε' : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss ε' := by
  exact ContinuousFlexibility.Blueprint.n01Properties_mono
    (base := base) (base' := base') (loss := loss) (loss' := loss)
    (ε := ε) (ε' := ε') hT hN hb le_rfl hε hε'

end ContinuousFlexibility.Statements
