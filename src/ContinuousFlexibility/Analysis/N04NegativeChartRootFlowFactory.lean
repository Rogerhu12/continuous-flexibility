import ContinuousFlexibility.Analysis.N04NegativeChartFinitePlotFields
import ContinuousFlexibility.Analysis.N04FlowTimeReversal
import ContinuousFlexibility.Analysis.RootRescaledStoredFlow

/-!
# The actual forward and reversed root flows on a finite state plot

One pair of genuine coefficient representatives produces both flows.
Their closed-time equations identify the stored physical trajectories;
a smooth time change supplies global equations for the state variation
argument. The endpoint is unchanged and the two endpoint maps are exact
inverses. No derivative estimate on an artificial extension is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- The two independent root coordinates remain external parameters. -/
def negativeChartRootPlotField (d c : P × PolarPoint → ℝ) (δ : ℝ) :
    (P × (ℝ × ℝ)) × PolarPoint → ℝ := fun q =>
  rootRescaledField (fun p => d (q.1.1, p)) (fun p => c (q.1.1, p)) δ
    (q.2.1, (q.1.2, q.2.2))

def negativeChartRootPlotReverseField (d c : P × PolarPoint → ℝ) (δ : ℝ) :
    (P × (ℝ × ℝ)) × PolarPoint → ℝ := fun q =>
  -negativeChartRootPlotField d c δ (q.1, (1 - q.2.1, q.2.2))

/-- The scalar time change preserves times zero and one. -/
def negativeChartRootPlotTimeChange
    (Θ : P → (ℝ × ℝ) → ℝ → ℝ → ℝ) :
    (P × (ℝ × ℝ)) × PolarPoint → ℝ := fun q =>
  Θ q.1.1 q.1.2 (compactScalarFlowTime 0 1 q.2.1) q.2.2

theorem negativeChartRootPlotField_contDiff {d c : P × PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c) (δ : ℝ) :
    ContDiff ℝ ∞ (negativeChartRootPlotField d c δ) := by
  have ht : ContDiff ℝ ∞ (fun q : (P × (ℝ × ℝ)) × PolarPoint => q.2.1) :=
    contDiff_snd.fst
  have hx : ContDiff ℝ ∞ (fun q : (P × (ℝ × ℝ)) × PolarPoint => δ * q.1.2.1) :=
    contDiff_const.mul contDiff_fst.snd.fst
  have hz : ContDiff ℝ ∞ (fun q : (P × (ℝ × ℝ)) × PolarPoint => δ * q.1.2.2) :=
    contDiff_const.mul contDiff_fst.snd.snd
  have harg : ContDiff ℝ ∞ (fun q : (P × (ℝ × ℝ)) × PolarPoint =>
      (q.1.1, (δ * q.1.2.1 * q.2.1 ^ 2, q.2.2))) :=
    contDiff_fst.fst.prodMk ((hx.mul (ht.pow 2)).prodMk contDiff_snd.snd)
  exact (((contDiff_const.mul hx).mul ht).mul (hd.comp harg)).add
    (((contDiff_const.mul hz).mul (ht.pow 2)).mul (hc.comp harg))

private theorem compactFlow_timeChange
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : E × PolarPoint → ℝ} {Θ : E → ℝ → ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (hi : ∀ q α, Θ q 0 α = α)
    (hf : ∀ q α t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ q r α) (G (q, (t, Θ q t α))) (Icc (0 : ℝ) 1) t)
    (hc : ContinuousOn (fun z : (E × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ Icc (0 : ℝ) 1)) :
    ContDiff ℝ ∞ (fun z : E × PolarPoint =>
      Θ z.1 (compactScalarFlowTime 0 1 z.2.1) z.2.2) ∧
    ∀ q t α, HasDerivAt (fun r => Θ q (compactScalarFlowTime 0 1 r) α)
      (scalarFieldTimeChange G 0 1
        (q, (t, Θ q (compactScalarFlowTime 0 1 t) α))) t := by
  let F : (E × ℝ) × PolarPoint → ℝ := fun z => G (z.1.1, z.2)
  have hF : ContDiff ℝ ∞ F := hG.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hc' : ContinuousOn (fun z : (E × ℝ) × ℝ => Θ z.1.1 z.2 z.1.2)
      (univ ×ˢ uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hc
  have hf' (q : E × ℝ) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivWithinAt (fun r => Θ q.1 r q.2)
        (F (q, (t, Θ q.1 t q.2))) (uIcc (0 : ℝ) 1) t := by
    simpa only [uIcc_of_le zero_le_one] using hf q.1 q.2 t
      (show t ∈ Icc (0 : ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
  have hs := contDiff_scalarFlow_timeChange hF contDiff_snd hc'
    (fun q => hi q.1 q.2) hf'
  refine ⟨hs.comp ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst), ?_⟩
  intro q t α
  exact scalarFlowTimeChange_hasDerivAt hf' (q, α) t

/-- All functions in this package are the same actual ODE solutions.
The smooth time-changed functions are used only to differentiate them. -/
structure NegativeChartRootFlowData (d c : P × PolarPoint → ℝ) (δ : ℝ) where
  flow : P → (ℝ × ℝ) → ℝ → ℝ → ℝ
  inverse : P → (ℝ × ℝ) → ℝ → ℝ → ℝ
  flow_equations : ∀ y, N04FlowEquations
    (rootRescaledField (fun p => d (y, p)) (fun p => c (y, p)) δ) (flow y)
  inverse_equations : ∀ y, N04FlowEquations
    (n04FlowReverseField (rootRescaledField (fun p => d (y, p)) (fun p => c (y, p)) δ))
    (inverse y)
  flow_smooth : ContDiff ℝ ∞ (negativeChartRootPlotTimeChange flow)
  inverse_smooth : ContDiff ℝ ∞ (negativeChartRootPlotTimeChange inverse)
  flow_time : ∀ q t α,
    HasDerivAt (fun r => negativeChartRootPlotTimeChange flow (q, (r, α)))
      (scalarFieldTimeChange (negativeChartRootPlotField d c δ) 0 1
        (q, (t, negativeChartRootPlotTimeChange flow (q, (t, α))))) t
  inverse_time : ∀ q t α,
    HasDerivAt (fun r => negativeChartRootPlotTimeChange inverse (q, (r, α)))
      (scalarFieldTimeChange (negativeChartRootPlotReverseField d c δ) 0 1
        (q, (t, negativeChartRootPlotTimeChange inverse (q, (t, α))))) t
  endpoint_inverse : ∀ y v θ,
    flow y v 1 (inverse y v 1 θ) = θ ∧ inverse y v 1 (flow y v 1 θ) = θ

namespace NegativeChartRootFlowData

variable {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)

theorem flow_initial (q : P × (ℝ × ℝ)) (α : ℝ) :
    negativeChartRootPlotTimeChange A.flow (q, (0, α)) = α := by
  simpa only [negativeChartRootPlotTimeChange, compactScalarFlowTime_zero] using
    (A.flow_equations q.1).1 q.2 α

theorem inverse_initial (q : P × (ℝ × ℝ)) (α : ℝ) :
    negativeChartRootPlotTimeChange A.inverse (q, (0, α)) = α := by
  simpa only [negativeChartRootPlotTimeChange, compactScalarFlowTime_zero] using
    (A.inverse_equations q.1).1 q.2 α

theorem flow_endpoint (q : P × (ℝ × ℝ)) (α : ℝ) :
    negativeChartRootPlotTimeChange A.flow (q, (1, α)) = A.flow q.1 q.2 1 α := by
  simp only [negativeChartRootPlotTimeChange, compactScalarFlowTime_one]

theorem inverse_endpoint (q : P × (ℝ × ℝ)) (α : ℝ) :
    negativeChartRootPlotTimeChange A.inverse (q, (1, α)) = A.inverse q.1 q.2 1 α := by
  simp only [negativeChartRootPlotTimeChange, compactScalarFlowTime_one]

end NegativeChartRootFlowData

private theorem exists_rootPlotFlowData {d c : P × PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdper : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcper : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (δ : ℝ) : Nonempty (NegativeChartRootFlowData d c δ) := by
  let G := negativeChartRootPlotField d c δ
  have hG : ContDiff ℝ ∞ G := negativeChartRootPlotField_contDiff hd hc δ
  have hperiod (t : ℝ) (q : P × (ℝ × ℝ)) :
      Function.Periodic (fun θ => G (q, (t, θ))) Real.pi :=
    rootRescaledField_periodic (hdper q.1) (hcper q.1) δ t q.2
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ((P × (ℝ × ℝ)) × ℝ) =>
      G (z.2.1, (z.1, z.2.2))) :=
    hG.comp (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd))
  obtain ⟨Θ, hi, hf, _, hcont⟩ := exists_continuous_periodicScalarFlowFamily
    zero_le_one Real.pi_ne_zero hF (fun t _ q => hperiod t q)
  let R := negativeChartRootPlotReverseField d c δ
  have hR : ContDiff ℝ ∞ R :=
    (hG.comp (contDiff_fst.prodMk
      ((contDiff_const.sub contDiff_snd.fst).prodMk contDiff_snd.snd))).neg
  have hrper (t : ℝ) (q : P × (ℝ × ℝ)) :
      Function.Periodic (fun θ => R (q, (t, θ))) Real.pi := by
    intro θ
    exact congrArg Neg.neg (hperiod (1 - t) q θ)
  have hRF : ContDiff ℝ ∞ (fun z : ℝ × ((P × (ℝ × ℝ)) × ℝ) =>
      R (z.2.1, (z.1, z.2.2))) :=
    hR.comp (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd))
  obtain ⟨Ψ, hri, hrf, _, hrcont⟩ := exists_continuous_periodicScalarFlowFamily
    zero_le_one Real.pi_ne_zero hRF (fun t _ q => hrper t q)
  have hforward (y : P) : N04FlowEquations
      (rootRescaledField (fun p => d (y, p)) (fun p => c (y, p)) δ)
      (fun v => Θ (y, v)) := ⟨fun v => hi (y, v), fun v => hf (y, v)⟩
  have hreverse (y : P) : N04FlowEquations
      (n04FlowReverseField (rootRescaledField (fun p => d (y, p)) (fun p => c (y, p)) δ))
      (fun v => Ψ (y, v)) := ⟨fun v => hri (y, v), fun v => hrf (y, v)⟩
  have hs := compactFlow_timeChange hG hi hf hcont
  have hrs := compactFlow_timeChange hR hri hrf hrcont
  refine ⟨{
    flow := fun y v => Θ (y, v)
    inverse := fun y v => Ψ (y, v)
    flow_equations := hforward
    inverse_equations := hreverse
    flow_smooth := hs.1
    inverse_smooth := hrs.1
    flow_time := hs.2
    inverse_time := hrs.2
    endpoint_inverse := ?_ }⟩
  intro y v θ
  have hds : ContDiff ℝ ∞ (fun p => d (y, p)) := hd.comp (contDiff_const.prodMk contDiff_id)
  have hcs : ContDiff ℝ ∞ (fun p => c (y, p)) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hfield := contDiff_rootRescaledField hds hcs δ
  refine ⟨n04Flow_reverse_endpoint_rightInverse hfield (hforward y) (hreverse y) v θ, ?_⟩
  have hh : N04FlowEquations
      (n04FlowReverseField (n04FlowReverseField
        (rootRescaledField (fun p => d (y, p)) (fun p => c (y, p)) δ)))
      (fun v => Θ (y, v)) := by
    rw [n04FlowReverseField_reverse]
    exact hforward y
  exact n04Flow_reverse_endpoint_rightInverse
    (n04FlowReverseField_contDiff hfield) (hreverse y) hh v θ

namespace N04RealizationStart.NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- Construct the actual pair once on each finite state plot, retaining
its complete coefficient germs on the entire closed physical half. -/
theorem fullHalfFields_finiteRootFlow
    {n : ℕ} (x : AnnularState W.S × ℝ)
    (hx : x ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState W.S × ℝ))
    (m : ℕ) (side : Bool) (δ : ℝ) :
    ∃ d c : (Fin n → ℝ) × PolarPoint → ℝ,
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c ∧
      (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) ∧
      (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) ∧
      (∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
        d =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfDrift (x + L q.1) m side q.2) ∧
        c =ᶠ[𝓝 (0, p)] (fun q => F.fullHalfSpeed (x + L q.1) m side q.2)) ∧
      (∃ V : Set (Fin n → ℝ), IsOpen V ∧ (0 : Fin n → ℝ) ∈ V ∧
        (∀ y ∈ V, x + L y ∈ stateNeighborhood W.S W.C W.base (W.ε / 2)) ∧
        ∀ y ∈ V, ∀ p : PolarPoint,
          p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
          d (y, p) = F.fullHalfDrift (x + L y) m side p ∧
          c (y, p) = F.fullHalfSpeed (x + L y) m side p) ∧
      Nonempty (NegativeChartRootFlowData d c δ) := by
  obtain ⟨d, c, hd, hc, hdp, hcp, hg, hV⟩ :=
    F.fullHalfFields_finiteAffine_representatives_uniform x hx L m side
  exact ⟨d, c, hd, hc, hdp, hcp, hg, hV, exists_rootPlotFlowData hd hc hdp hcp δ⟩

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_finiteRootFlow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.fullHalfFields_finiteRootFlow
