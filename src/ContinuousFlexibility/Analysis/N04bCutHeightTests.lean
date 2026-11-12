import ContinuousFlexibility.Analysis.N04bCutVariationTests
import ContinuousFlexibility.Scalar.WeightedCompactRadial
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual weighted height directions for the cut-variation tests

The compact radial tests are members of the actual material height model.
Its surjective decoder therefore provides a genuine HeightPair with zero
cutoff component. The resulting direction is available for every choice
of physical spaces satisfying the frozen contract.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A compact smooth radial test has an actual preimage in the frozen
height model; no new completion or surrogate function space is used. -/
theorem n04b_heightPair_of_compact_radial
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo D.a D.b) :
    ∃ u : HeightPair S, u.2 = 0 ∧
      heightPairField S u = fun p : PolarPoint => f p.1 := by
  have hsupp : HasCompactRadialSupport D (fun p : PolarPoint => f p.1) := by
    refine ⟨tsupport f, hc, hs, ?_⟩
    intro r hr θ
    by_contra hn
    exact hr (subset_tsupport f hn)
  have hm : HeightMember D T (3 / 4 : ℝ) (fun p : PolarPoint => f p.1) :=
    heightMember_radial_of_compact_support hT hf hsupp
  obtain ⟨v, hv⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _ hm
  refine ⟨(v, 0), rfl, ?_⟩
  funext p
  simp only [heightPairField, hv, zero_mul, add_zero]

/-- The zero-total, nonzero-half variation occurs inside the actual
weighted height space for every admissible existential choice of spaces. -/
theorem n04b_exists_heightPair_cut_test
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcore : Ioo a b ⊆ Ioo D.a D.b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b))
    (hwa : w a = 0) (hwb : w b = 0) (hwc : w c ≠ 0) :
    ∃ f : ℝ → ℝ, ∃ u : HeightPair S,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo a b ∧
      u.2 = 0 ∧ heightPairField S u = (fun p : PolarPoint => f p.1) ∧
      (∫ r, w r * deriv f r) = 0 ∧
      (∫ r in Ioo a c, w r * deriv f r) = 1 := by
  obtain ⟨f, hf, hc, hs, ht, hl⟩ :=
    Analysis.n04b_exists_zero_total_nonzero_half_test hac hcb hw hwa hwb hwc
  obtain ⟨u, hu, hfield⟩ :=
    n04b_heightPair_of_compact_radial hT hS hf hc (hs.trans hcore)
  exact ⟨f, u, hf, hc, hs, hu, hfield, ht, hl⟩

end ContinuousFlexibility.Statements
