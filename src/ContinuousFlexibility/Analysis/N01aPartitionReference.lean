module

public import ContinuousFlexibility.Analysis.N01aPartitionBounds
public import ContinuousFlexibility.Analysis.N01aReferenceCoarseningClosure
public import ContinuousFlexibility.Analysis.N01aReferenceCoarseningInverse

/-!
# Retaining the full radial reference under cell grouping

All physical equations remain identical. The inverse, graph topology and
first-normal estimate are transported using the proved norm comparisons.
The source-measurability bridge is kept explicit at this intermediate
stage; it is discharged from the actual reference graph separately.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

namespace N01aReferenceCoarsening

variable {D E : ReferenceData} {σ : ℕ → ℕ} (h : N01aReferenceCoarsening D E σ)

include h

theorem natural_kernels_iff : RadialNaturalKernels E ↔ RadialNaturalKernels D := by
  simp only [RadialNaturalKernels, NaturalRadialNull, radialHilbertMeasure,
    h.core_eq, h.w_eq, h.phi_eq, h.a_eq, h.b_eq]

theorem true_border_iff : RadialTrueBorder E ↔ RadialTrueBorder D := by
  simp only [RadialTrueBorder, h.chi_eq, h.chiLeft_eq, h.core_eq, h.w_eq,
    h.column_eq, h.phi_eq, h.a_eq, h.b_eq]

theorem component_iff (l r : ℝ) :
    NegativeRadialComponent E l r ↔ NegativeRadialComponent D l r := by
  simp only [NegativeRadialComponent, h.a_eq, h.b_eq, h.w_eq]

theorem travel_eq (l r : ℝ) : radialTravel E l r = radialTravel D l r := by
  simp only [radialTravel, h.w_eq]

theorem return_margins (hcell : ∀ i, D.cells i ⊆ E.cells (σ i))
    (hR : RadialReturnMargins D) : RadialReturnMargins E := by
  refine ⟨?_, ?_⟩
  · intro r hr hneg
    have hrD : r ∈ radialCore D := by simpa only [h.core_eq] using hr
    have hnegD : deriv D.w r < 0 := by simpa only [h.w_eq] using hneg
    obtain ⟨l, r', hc, hi⟩ := hR.1 r hrD hnegD
    exact ⟨l, r', (h.component_iff l r').mpr hc, hi⟩
  · obtain ⟨C, hC, hmargin⟩ := hR.2
    refine ⟨C, hC, ?_⟩
    intro l r hc
    obtain ⟨hq, i, hi, c, hcpos, hb, hsin⟩ := hmargin l r ((h.component_iff l r).mp hc)
    refine ⟨?_, σ i, hi.trans (hcell i), c, hcpos, ?_, ?_⟩
    · simpa only [h.travel_eq] using hq
    · simpa only [h.index_eq] using hb
    · simpa only [h.travel_eq] using hsin

theorem radial_reference_of_source_measurable
    (hD : IsRadialReference D) (hE : IsAccumulatingProfile E)
    (hcell : ∀ i, D.cells i ⊆ E.cells (σ i))
    (hMeas : ∀ γ M₀ M₁ : ℝ, ∀ G : RadialSource → RadialUnknown, 0 < γ →
      ReferenceInverseProperties D γ M₀ M₁ G →
      ReferenceSmoothCoreClosure D γ M₀ M₁ →
      ReferenceGreenReciprocity D γ M₀ M₁ →
      ∀ F : RadialSource, SourceMember D γ M₀ F →
        AEMeasurable F.1 (radialPhysicalMeasure D)) :
    IsRadialReference E := by
  obtain ⟨hAccum, hNat, hRet, hBorder, ε, M₀, M₁, hε, hεlt, G, hG⟩ := hD
  have hpartD : RadialPartition D := hAccum.choose_spec.2.1
  have hpartE : RadialPartition E := hE.choose_spec.2.1
  have hab : D.a ≤ D.b := hAccum.choose_spec.1.2.1.le
  refine ⟨hE, h.natural_kernels_iff.mpr hNat, h.return_margins hcell hRet,
    h.true_border_iff.mpr hBorder, ε, M₀, M₁, hε, hεlt, G, ?_⟩
  intro γ hγ
  obtain ⟨hinv, hclosed, hcore, hgreen, hnormal⟩ := hG γ hγ
  have hγpos : 0 < γ := by
    rcases hγ with rfl | rfl | rfl <;> dsimp only [referenceBeta] <;> linarith
  have hm := hMeas γ M₀ M₁ G hγpos hinv hcore hgreen
  exact ⟨h.inverse_properties hpartD hpartE hab hinv,
    h.graph_closed_of_source_aemeasurable hpartD hpartE hab hm hclosed,
    h.smooth_core_closure_of_source_aemeasurable hpartD hpartE hab hm hcore,
    h.green_reciprocity hpartD hpartE hab hgreen,
    h.first_normal_estimate hpartD hpartE hab hnormal⟩

end N01aReferenceCoarsening

theorem exists_n01a_grouped_reference_of_source_measurable {D : ReferenceData}
    (hD : IsRadialReference D)
    (hMeas : ∀ γ M₀ M₁ : ℝ, ∀ G : RadialSource → RadialUnknown, 0 < γ →
      ReferenceInverseProperties D γ M₀ M₁ G →
      ReferenceSmoothCoreClosure D γ M₀ M₁ →
      ReferenceGreenReciprocity D γ M₀ M₁ →
      ∀ F : RadialSource, SourceMember D γ M₀ F →
        AEMeasurable F.1 (radialPhysicalMeasure D)) :
    ∃ E : RadialReference, ∃ σ : ℕ → ℕ,
      N01aReferenceCoarsening D E.val σ ∧ ∀ j, j ≤ 2 * E.val.cellIndex j + 1 := by
  obtain ⟨E, σ, hcoarse, hAccum, _, hcell, hindex⟩ := exists_n01a_grouped_profile hD.1
  exact ⟨⟨E, hcoarse.radial_reference_of_source_measurable hD hAccum hcell hMeas⟩,
    σ, hcoarse, hindex⟩

end ContinuousFlexibility.Statements
