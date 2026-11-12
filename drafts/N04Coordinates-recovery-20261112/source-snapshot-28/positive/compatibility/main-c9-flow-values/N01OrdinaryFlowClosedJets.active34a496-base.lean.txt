import ContinuousFlexibility.Analysis.N01OrdinaryFlowAngularRegularity
import ContinuousFlexibility.Analysis.CanonicalVariationBounds
import ContinuousFlexibility.Analysis.SolveReturnEquations
import Mathlib.Topology.Order.DenselyOrdered

/-!
# The actual N01 angular bounds at closed return endpoints

Genuine closed-time angular regularity makes the actual angular difference
jets continuous. The existing interior first-variation estimate therefore
passes to both endpoints with exactly the same material constant, grading,
base, and loss. No endpoint estimate is supplied as an additional input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem abs_le_on_Icc_of_continuousOn_open_bound
    {f : ℝ → ℝ} {l u M : ℝ} (hlu : l < u)
    (hf : ContinuousOn f (Icc l u))
    (hbound : ∀ r ∈ Ioo l u, |f r| ≤ M)
    {r : ℝ} (hr : r ∈ Icc l u) : |f r| ≤ M := by
  have hclosure : r ∈ closure (Ioo l u) := by
    rw [closure_Ioo hlu.ne]
    exact hr
  have : NeBot (𝓝[Ioo l u] r) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hlim : Tendsto (fun t => |f t|) (𝓝[Ioo l u] r) (𝓝 |f r|) :=
    ((hf r hr).mono Ioo_subset_Icc_self).abs
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hbound t ht

/-- The true angular difference jets, not prescribed auxiliary jets, are
continuous on the whole closed physical component. -/
theorem ordinaryFlowFamily_angular_continuousOn_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m b : ℕ) :
    ContinuousOn (fun p => ordinaryFlowFamily S C m 0 b p z)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) := by
  have hcurrent := n01_ordinaryFlow_angularRegularity hS hT hN hz hsector m
  have hreference := n01_ordinaryFlow_angularRegularity hS hT hN
    (reference_mem_stateNeighborhood S C base hN.2.1) hN.2.2.1.stateSector m
  apply ((hcurrent.2 b).sub (hreference.2 b)).congr
  intro p hp
  change iteratedDeriv b
      (fun θ => C.minusFlow z m p.1 θ -
        C.minusFlow (C.referenceState, 0) m p.1 θ) p.2 = _
  exact iteratedDeriv_fun_sub (n := b)
    ((hcurrent.1 p.1 hp.1).contDiffAt.of_le (by simp))
    ((hreference.1 p.1 hp.1).contDiffAt.of_le (by simp))

/-- The same body as the interior linear-high estimate, with closed radial
membership and the sector needed for actual denominator admissibility. -/
def N01ClosedFlowLinearHighBoundAtOrder
    (T : MaterialData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ m b p, b ≤ s → p.1 ∈ Icc (C.left m) (C.right m) →
    ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      |ordinaryFlowFamily S C m 0 b p z| ≤
        B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B *
          (2 + 2 * ε) * pairGrading (stateGrading S) realGrading
            (max base (s + loss)) (z - (C.referenceState, 0))

private theorem n01_closedFlow_bound_of_open_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss s : ℕ} {ε B : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hbound : N01FlowLinearHighBoundAtOrder T S C base loss ε s B) :
    N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε s B := by
  intro m b p hb hp z hz hsector
  have hc := ordinaryFlowFamily_angular_continuousOn_of_n01 hS hT hN hz hsector m b
  have hslice : ContinuousOn
      (fun r => ordinaryFlowFamily S C m 0 b (r, p.2) z)
      (Icc (C.left m) (C.right m)) :=
    hc.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨hr, mem_univ p.2⟩)
  exact abs_le_on_Icc_of_continuousOn_open_bound (hN.2.2.2.1.1 m).2.1 hslice
    (fun r hr => hbound m b (r, p.2) hb hr z hz) hp

/-- N01's actual angular variation bound reaches both radial endpoints
without changing its fixed loss or its state-independent constant. -/
theorem ordinaryFlowFamily_le_linear_high_on_closed_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01ClosedFlowLinearHighBoundAtOrder T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := ordinaryFlowFamily_le_linear_high_of_n01 hT hN s
  exact ⟨B, hB, n01_closedFlow_bound_of_open_bound hS hT hN hbound⟩

end ContinuousFlexibility.Analysis
