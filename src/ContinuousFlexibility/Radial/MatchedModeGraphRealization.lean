module

public import ContinuousFlexibility.Radial.MatchedModeGraphProjection
public import ContinuousFlexibility.Radial.MatchedModeTestClosure

/-!
# The full modal graph of a physical weak solution

The actual cosine projection is first tested on compactly contained radial
supports. The proved test closure then recovers the complete frozen graph,
including the frequency-two row and the opposite model scalar.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Any actual modal L² representatives of a physical graph solution satisfy
the full frozen one-dimensional graph, including endpoint-flat tests. -/
theorem ReferenceGraph.modeFullGraph_of_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) {j : ℕ} (hj : 0 < j)
    {u f : RadialModeL2 D}
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] referenceMode U.1 j)
    (hf : (f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -referenceMode F.1 j r / Radial.matchingDensity D r)) :
    ModeFullGraph D j (u, -(if j = 2 then U.2 else 0))
      (f, if j = 2 then F.2 else 0) := by
  constructor
  · apply Radial.modeLocalEquation_of_compactCore hD hB
    intro ψ hψ hcψ hψs
    have heU :
        (∫ r in D.a..D.b, u r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
          ∫ r in D.a..D.b, referenceMode U.1 j r *
            Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r := by
      apply Radial.matchingInterval_congr_ae hD
      filter_upwards [hu] with r hr
      rw [hr]
    have heF := Radial.matchedMode_physicalSource_pairing hD
      (F := (f, if j = 2 then F.2 else 0)) hf ψ
    change (∫ r in D.a..D.b, u r * Radial.radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      (-(if j = 2 then U.2 else 0)) *
        (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, Radial.matchingDensity D r * f r * ψ r)
    rw [heU, heF, neg_mul, sub_neg_eq_add]
    exact hG.modeWeak_compactCore hD hj hψ hcψ hψs
  · by_cases hj2 : j = 2
    · subst j
      simpa only [ite_true] using hG.modeTwo_row_of_ae hD hu
    · simp only [hj2, ite_false, neg_zero, and_self]

/-- The coefficient vectors obtained by toLp belong to the actual graph. -/
theorem ReferenceGraph.modeFullGraph_of_memLp {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) {j : ℕ} (hj : 0 < j)
    (hu : MemLp (referenceMode U.1 j) 2 (radialHilbertMeasure D))
    (hf : MemLp (fun r => -referenceMode F.1 j r / Radial.matchingDensity D r)
      2 (radialHilbertMeasure D)) :
    ModeFullGraph D j
      (hu.toLp (referenceMode U.1 j), -(if j = 2 then U.2 else 0))
      (Radial.matchedModePhysicalSource D (referenceMode F.1 j) hf
        (if j = 2 then F.2 else 0)) :=
  hG.modeFullGraph_of_ae hD hB hj hu.coeFn_toLp
    (Radial.matchedModePhysicalSource_ae D (referenceMode F.1 j) hf
      (if j = 2 then F.2 else 0))

/-- The frozen modal uniqueness theorem identifies the actual coefficient,
with no replacement of its test class or its scalar sign. -/
theorem ReferenceGraph.mode_eq_inverse {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} {U : RadialUnknown} {F : RadialSource}
    (hG : ReferenceGraph D γ M₀ M₁ U F) {j : ℕ} (hj : 0 < j)
    {G : RadialModePair D →L[ℝ] RadialModePair D}
    (hInv : ModeInverseProperties D j G) {u f : RadialModeL2 D}
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] referenceMode U.1 j)
    (hf : (f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => -referenceMode F.1 j r / Radial.matchingDensity D r)) :
    G (f, if j = 2 then F.2 else 0) = (u, -(if j = 2 then U.2 else 0)) :=
  hInv.2 _ _ (hG.modeFullGraph_of_ae hD hB hj hu hf)

end ContinuousFlexibility.Statements
