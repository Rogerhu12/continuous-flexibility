import ContinuousFlexibility.Radial.InnerGapDirichlet
import ContinuousFlexibility.Radial.InnerRadialEnergyDomain

/-!
# The positive-gap solution in the common physical H¹ domain

The extra potential coordinate is used only in the coercive construction.
The same solution witness projects continuously to the common physical
function/weighted-derivative domain used by every finite inner piece.
No change of measure or alternative derivative representation is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem innerGapFormSpace_radialH1 (D : ReferenceData) (j a b : ℝ)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    (q.fst, q.snd.fst) ∈ innerRadialH1Zero D a b := by
  let π : InnerGapEnergyTriple D → InnerRadialH1Pair D := fun q => (q.fst, q.snd.fst)
  have hπ : Continuous π :=
    (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous.prodMk
      ((WithLp.fstL 2 ℝ (RadialModeL2 D) (RadialModeL2 D)).continuous.comp
        (WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous)
  have hclosed : IsClosed {q : InnerGapEnergyTriple D | π q ∈ innerRadialH1Zero D a b} :=
    (innerRadialH1Zero D a b).isClosed.preimage hπ
  apply (closure_minimal ?_ hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  rintro r ⟨u, hu, hcompact, hsupport, hvalue, hgrad, _⟩
  apply (mem_innerRadialH1Zero D a b (π r)).mpr
  exact subset_closure ⟨u, hu, hcompact, hsupport, hvalue, hgrad⟩

/-- A single witness supplies both the common H¹ derivative and the
whole closed-form equation. -/
theorem innerGapFormGraph_radialH1 (D : ReferenceData) (j a b : ℝ)
    (u f : RadialModeL2 D) (h : InnerGapFormGraph D j a b u f) :
    ∃ q : InnerGapEnergyTriple D, q ∈ innerGapFormSpace D j a b ∧ q.fst = u ∧
      (u, q.snd.fst) ∈ innerRadialH1Zero D a b ∧
      ∀ r ∈ innerGapFormSpace D j a b, ⟪f, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ := by
  obtain ⟨q, hq, hvalue, hform⟩ := (innerGapFormGraph_iff D j a b u f).mp h
  refine ⟨q, hq, hvalue, ?_, hform⟩
  simpa only [hvalue] using innerGapFormSpace_radialH1 D j a b q hq

end ContinuousFlexibility.Radial
