import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.MaterialSampleCofinite
import ContinuousFlexibility.Analysis.N01cStateSeminorms

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

/-- Keep the existential flow bound opaque while restricting its tower. -/
private theorem ordinaryFlowFamilyTameBounds_restrict_neighborhood
    {T : MaterialData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss : ℕ} {ε ε' : ℝ}
    (hbound : OrdinaryFlowFamilyTameBounds T S C base loss ε)
    (hopen : IsOpen (stateNeighborhood S C base' ε'))
    (hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε)
    (hp : Monotone (pairGrading (stateGrading S) realGrading))
    (hb : base ≤ base')
    (hH : ∀ m, 0 < T.H (T.sample m))
    (hE : ∀ m, 0 < T.E0 (T.sample m)) :
    OrdinaryFlowFamilyTameBounds T S C base' loss ε' := by
  intro k
  obtain ⟨parameterLoss, horder⟩ := hbound k
  refine ⟨parameterLoss, ?_⟩
  intro s
  let hdata := horder s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  have hpoint : ∀ m a b p, a + b ≤ s → p.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (stateNeighborhood S C base' ε')
        (ordinaryFlowFamily S C m a b p),
        ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin k → (AnnularState S × ℝ),
          min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
            B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
              oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
                base' (s + loss + parameterLoss) (z - (C.referenceState, 0)) v := by
    intro m a b p hab hpm
    have hC : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B :=
      mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hH (C.cell m)).le _))
        (Real.rpow_nonneg (hE (C.cell m)).le _)
    exact smoothDirections_restrict_oneHigh_bound
      (fun y : ℝ => min (p.1 - C.left m) (C.right m - p.1) ^ a * |y|)
      (C.referenceState, (0 : ℝ)) hopen hsub hp hb hC
        (hdata.choose_spec.2 m a b p hab hpm)
  exact Exists.intro B (And.intro hB hpoint)

theorem N01Properties.restrict_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss : ℕ} {ε ε' : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  have hopen := stateNeighborhood_isOpen S C base' ε'
  have hsamples := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsamples m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsamples m)).2.2.1
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  refine ⟨hN.1, hε', hN.2.2.1, hN.2.2.2.1, hN.2.2.2.2.1, hN.2.2.2.2.2.1,
    (fun z hz => hN.2.2.2.2.2.2.1 z (hsub hz)),
    (fun z hz => hN.2.2.2.2.2.2.2.1 z (hsub hz)),
    (fun z hz => hN.2.2.2.2.2.2.2.2.1 z (hsub hz)),
    (fun z hz => hN.2.2.2.2.2.2.2.2.2.1 z (hsub hz)),
    (fun z hz => hN.2.2.2.2.2.2.2.2.2.2.1 z (hsub hz)), ?_, ?_⟩
  · intro k s
    let hdata := hN.2.2.2.2.2.2.2.2.2.2.2.1 k s
    let B : ℝ := hdata.choose
    have hB : 0 < B := hdata.choose_spec.1
    have hpoint : ∀ m i a b p, a + b ≤ s → p.1 ∈ D.cells m →
        ∃ J : SmoothDirections (stateNeighborhood S C base' ε')
          (coefficientFamily D S C i a b p),
          ∀ z ∈ stateNeighborhood S C base' ε', ∀ v : Fin k → (AnnularState S × ℝ),
            |J.D k z v| ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
              oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
                base' (s + loss) (z - (C.referenceState, 0)) v := by
      intro m i a b p hab hpm
      have hC : 0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B :=
        mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hH m).le _))
          (Real.rpow_nonneg (hE m).le _)
      exact smoothDirections_restrict_oneHigh_bound (fun y : ℝ => |y|)
        (C.referenceState, (0 : ℝ)) hopen hsub hp hb hC
          (hdata.choose_spec.2 m i a b p hab hpm)
    exact Exists.intro B (And.intro hB hpoint)
  · have hflow : OrdinaryFlowFamilyTameBounds T S C base loss ε :=
      hN.2.2.2.2.2.2.2.2.2.2.2.2
    exact ordinaryFlowFamilyTameBounds_restrict_neighborhood hflow hopen hsub hp hb hH hE

end ContinuousFlexibility.Statements
