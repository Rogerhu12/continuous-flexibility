import ContinuousFlexibility.Radial.InnerRadialWeakDirichlet
import ContinuousFlexibility.Radial.InnerRadialPhysicalSchur

/-!
# The actual physical weak graph satisfies the frozen inner graph

The supported physical forcing is recovered exactly by its actual piece
projections. The field and scalar are those of the same physical graph
witness. No replacement solution or new source is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

/-- The genuine local forcing coordinates sum to the original supported
source, with no change of measure and no omitted internal cut term. -/
theorem innerRadialPhysicalForcing_sum (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    (∑ k, innerRadialPhysicalForcing D G bordered F k) = F.val.fst := by
  have hmem := (mem_innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) bordered F.val).mp F.property
  have hs := innerL2PieceProjection_supported (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (innerRadialChainRegion_measurable D G) F.val.fst
  rw [hmem.2] at hs
  simp only [innerRadialPhysicalForcing_apply]
  exact innerL2PieceProjections_sum_eq (radialHilbertMeasure D)
    (fun k => Ioo (G.left k) (G.right k)) (fun _ => measurableSet_Ioo)
    (innerRadialChainPieces_disjoint D G) F.val.fst hs

/-- A true physical finite-chain solution satisfies the entire frozen
inner Dirichlet graph, including its actual C¹ representative, boundary
values, exterior zero extension, scalar row, and modal equation. -/
theorem innerRadialPhysicalWeakGraph_frozen {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {M : RadialMatchingData D} {n : ℕ}
    (G : InnerRadialChainGeometry D n)
    (hleft : G.left 0 = M.innerLeft) (hright : G.right (Fin.last n) = M.innerRight)
    (hab : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    {central : Fin (n + 1)} {column : RadialModeL2 D}
    (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r)
    (hgs : Function.support (referenceColumn D) ⊆ Ioo (G.left central) (G.right central))
    {u F : InnerRadialPhysicalSource D G (decide (M.frequency = 2))}
    (hgraph : InnerRadialPhysicalWeakGraph D hw.continuous G (decide (M.frequency = 2))
      (M.frequency : ℝ) central column u F) :
    ModeInnerDirichletGraph D M (WithLp.ofLp u.val) (WithLp.ofLp F.val) := by
  obtain ⟨q, v, c, hu, hq⟩ := (innerRadialPhysicalWeakGraph_iff D hw.continuous G
    (decide (M.frequency = 2)) (M.frequency : ℝ) central column u F).mp hgraph
  have hf (k : Fin (n + 1)) : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) →
        innerRadialPhysicalForcing D G (decide (M.frequency = 2)) F k r = 0 := by
    rw [innerRadialPhysicalForcing_apply]
    exact innerL2PieceProjection_supported (radialHilbertMeasure D)
      (Ioo (G.left k) (G.right k)) measurableSet_Ioo F.val.fst
  have he := innerRadialChainWeakGraph_frozen hD hB hw G hleft hright hab hsub
    (innerRadialChainPieces_disjoint D G) hq hf hc hgs
  have hu' : WithLp.ofLp u.val = (∑ k, (q k).1, c) := by
    rw [hu, WithLp.ofLp_toLp]
  have hF' : WithLp.ofLp F.val =
      (∑ k, innerRadialPhysicalForcing D G (decide (M.frequency = 2)) F k,
        innerRadialPhysicalRowLinear D G (decide (M.frequency = 2)) F) := by
    apply Prod.ext
    · rw [WithLp.ofLp_fst, innerRadialPhysicalForcing_sum]
    · rw [WithLp.ofLp_snd, innerRadialPhysicalRowLinear_apply]
  rw [hu', hF']
  exact he

end ContinuousFlexibility.Radial
