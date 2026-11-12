import ContinuousFlexibility.Radial.MatchedInnerFiniteTests

/-!
# The finite physical weak equation in the frozen modal language

The same physical tests give the exact modal Jacobi equation. The
temporary central column is identified with the actual border divided
by the true Hilbert density. The scalar row is therefore the original
unweighted border integral, and remains active only at frequency two.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace BigOperators
open ContinuousFlexibility.Statements

theorem matchedInner_border_test_pairing {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ⟪matchingBorderVector D hD hB, matchingSmoothVector D hD ψ hψ⟫_ℝ =
      ∫ r in D.a..D.b, referenceColumn D r * ψ r := by
  rw [real_inner_comm, ← matchingColumn_integral_eq_inner hD hB]
  apply matchingInterval_congr_ae hD
  filter_upwards [matchingTestInput_coe hD ψ hψ 0] with r hr
  change matchingSmoothVector D hD ψ hψ r = ψ r at hr
  rw [hr]

/-- The actual finite weak graph implies the frozen local modal equation
for the actual sums of the value and forcing coordinates. -/
theorem matchedInnerChainWeakGraph_equation {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (bordered : Bool) (j : ℕ) (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    {q : Fin (n + 1) → InnerRadialH1Pair D}
    {v f : Fin (n + 1) → RadialModeL2 D} {scalar rowSource : ℝ}
    (hf : ∀ p, innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left p) (G.right p)) (f p) = f p)
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G bordered (j : ℝ)
      central column q v f scalar rowSource) :
    ModeLocalEquation D j (Ioo (G.left 0) (G.right (Fin.last n)))
      (∑ p, (q p).1, scalar) (∑ p, f p, rowSource) := by
  classical
  apply (modeLocalEquation_iff_inner hD j _ _ _).mpr
  intro ψ hψ _ hs
  let T := matchedInnerChainSmoothTest D hw.continuous G ψ hψ
  let J := matchingJacobiVector D hD j ψ hψ
  let P := matchingSmoothVector D hD ψ hψ
  let E (p : Fin (n + 1)) := ⟪(q p).2, (T p).2⟫_ℝ + ⟪v p, (T p).1⟫_ℝ
  have hl : ψ (G.left 0) = 0 := by
    by_contra hn
    exact (lt_irrefl (G.left 0)) (hs hn).1
  have hr : ψ (G.right (Fin.last n)) = 0 := by
    by_contra hn
    exact (lt_irrefl (G.right (Fin.last n))) (hs hn).2
  have hT : T ∈ innerRadialChainDomain D hw.continuous G :=
    matchedInnerChainSmoothTest_mem D hw.continuous G ψ hψ hl hr
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw.continuous G q).mp hgraph.1
  have hgreen (p : Fin (n + 1)) :
      E p + ⟪(q p).1, J⟫_ℝ =
        innerChainBoundaryRestriction n p ξ 1 * (D.w (G.right p) * deriv ψ (G.right p)) -
          innerChainBoundaryRestriction n p ξ 0 * (D.w (G.left p) * deriv ψ (G.left p)) := by
    have h := matchedInnerSmoothTest_green hD hw (G.left_lt_right p) (G.left_pos p)
      (G.in_core p) (G.weight_pos p) j ψ hψ (hξ p).1 (hgraph.2.1 p)
    refine h.trans ?_
    exact congrArg (fun t : Fin 2 → ℝ =>
      t 1 * (D.w (G.right p) * deriv ψ (G.right p)) -
        t 0 * (D.w (G.left p) * deriv ψ (G.left p))) (hξ p).2
  have hgreenSum : (∑ p, E p) + ⟪∑ p, (q p).1, J⟫_ℝ = 0 := by
    rw [sum_inner, ← Finset.sum_add_distrib]
    calc
      _ = ∑ p : Fin (n + 1),
          (innerChainBoundaryRestriction n p ξ 1 *
              (D.w (G.right p) * deriv ψ (G.right p)) -
            innerChainBoundaryRestriction n p ξ 0 *
              (D.w (G.left p) * deriv ψ (G.left p))) :=
        Finset.sum_congr rfl (fun p _ => hgreen p)
      _ = 0 := matchedInnerChain_boundary_cancel G ξ (fun r => D.w r * deriv ψ r)
  have hsource (p : Fin (n + 1)) : ⟪f p, (T p).1⟫_ℝ = ⟪f p, P⟫_ℝ := by
    change ⟪f p, (matchedInnerSmoothTest D hw.continuous
      (G.left_pos p) (G.in_core p) (G.weight_pos p) ψ hψ).1⟫_ℝ = _
    rw [matchedInnerSmoothTest_value_projection hD hw.continuous
      (G.left_pos p) (G.in_core p) (G.weight_pos p)]
    have hproj : ⟪innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left p) (G.right p)) P, f p⟫_ℝ = ⟪P, f p⟫_ℝ :=
      innerL2PieceProjection_inner_fixed (radialHilbertMeasure D)
        (Ioo (G.left p) (G.right p)) P (f p) (hf p)
    exact (real_inner_comm _ _).trans (hproj.trans (real_inner_comm _ _))
  have hsourceSum : (∑ p, ⟪f p, (T p).1⟫_ℝ) = ⟪∑ p, f p, P⟫_ℝ := by
    rw [sum_inner]
    exact Finset.sum_congr rfl (fun p _ => hsource p)
  have hcolumnTest : ⟪column, (T central).1⟫_ℝ =
      ∫ r in D.a..D.b, referenceColumn D r * ψ r := by
    change ⟪column, (matchedInnerSmoothTest D hw.continuous
      (G.left_pos central) (G.in_core central) (G.weight_pos central) ψ hψ).1⟫_ℝ = _
    rw [matchedInnerSmoothTest_value_projection hD hw.continuous
      (G.left_pos central) (G.in_core central) (G.weight_pos central)]
    have hproj : ⟪innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left central) (G.right central)) P, column⟫_ℝ = ⟪P, column⟫_ℝ :=
      innerL2PieceProjection_inner_fixed (radialHilbertMeasure D)
        (Ioo (G.left central) (G.right central)) P column hcolfix
    have hswap : ⟪column, innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left central) (G.right central)) P⟫_ℝ = ⟪column, P⟫_ℝ :=
      (real_inner_comm _ _).trans (hproj.trans (real_inner_comm _ _))
    refine hswap.trans ?_
    rw [hcolumn]
    exact matchedInner_border_test_pairing hD hB ψ hψ
  have hcolumnSum :
      (∑ p : Fin (n + 1), ⟪if p = central then column else 0, (T p).1⟫_ℝ) =
        ⟪column, (T central).1⟫_ℝ := by
    rw [Finset.sum_eq_single central]
    · rw [if_pos rfl]
    · intro p _ hp
      rw [if_neg hp, inner_zero_left]
    · intro hc
      exact (hc (Finset.mem_univ central)).elim
  have hweak := hgraph.2.2.2 T hT
  change (∑ p, ((E p + scalar *
      ⟪if p = central then column else 0, (T p).1⟫_ℝ) - ⟪f p, (T p).1⟫_ℝ)) = 0 at hweak
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hcolumnSum, hcolumnTest, hsourceSum] at hweak
  change ⟪∑ p, (q p).1, J⟫_ℝ -
    scalar * (∫ r in D.a..D.b, referenceColumn D r * ψ r) = -⟪∑ p, f p, P⟫_ℝ
  linarith only [hgreenSum, hweak]

/-- The true central support identifies the single finite scalar row with
the frozen border integral. The other modes retain both scalar zeros. -/
theorem matchedInnerChainWeakGraph_row {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : Continuous D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (hdis : Pairwise (fun p k : Fin (n + 1) =>
      Disjoint (Ioo (G.left p) (G.right p)) (Ioo (G.left k) (G.right k))))
    (j : ℕ) (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    {q : Fin (n + 1) → InnerRadialH1Pair D}
    {v f : Fin (n + 1) → RadialModeL2 D} {scalar rowSource : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw G (decide (j = 2)) (j : ℝ)
      central column q v f scalar rowSource) :
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (∑ p, (q p).1 : RadialModeL2 D) r) = rowSource
    else scalar = 0 ∧ rowSource = 0 := by
  classical
  by_cases hj : j = 2
  · simp only [if_pos hj]
    have hrow : ⟪column, (q central).1⟫_ℝ = rowSource := by
      simpa [hj] using hgraph.2.2.1
    obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G q).mp hgraph.1
    have hs (p : Fin (n + 1)) :
        ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo (G.left p) (G.right p) → (q p).1 r = 0 :=
      innerRadialH1Domain_supported D hw (G.left_pos p) (G.in_core p)
        (G.weight_pos p) (hξ p).1
    have hc : ∀ᵐ r ∂radialHilbertMeasure D,
        r ∉ Ioo (G.left central) (G.right central) → column r = 0 := by
      have h := innerL2PieceProjection_supported (radialHilbertMeasure D)
        (Ioo (G.left central) (G.right central)) measurableSet_Ioo column
      rwa [hcolfix] at h
    rw [matchingColumn_integral_eq_inner hD hB, ← hcolumn, sum_inner,
      Finset.sum_eq_single central]
    · rw [real_inner_comm]
      exact hrow
    · intro p _ hp
      exact innerL2_disjoint_inner_zero (hdis hp) (q p).1 column (hs p) hc
    · intro hc
      exact (hc (Finset.mem_univ central)).elim
  · simp only [if_neg hj]
    simpa [hj] using hgraph.2.2.1

end ContinuousFlexibility.Radial
