import ContinuousFlexibility.Radial.R11bLeftCorrection
import ContinuousFlexibility.Radial.R11bZeroMode
import ContinuousFlexibility.Radial.R11bHilbertRepresentatives
import ContinuousFlexibility.Radial.ProfileScalarSquares

/-!
# Scalar weighted norms of the actual compact corrections

Radial fields have precisely the scalar cell square, since the normalized
mean of a constant is itself. Both the border forcing and the derivative
of the left-tail cutoff therefore have every required coefficient weight.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem r11b_referenceCellSquare_radial {D : ReferenceData} (hab : D.a ≤ D.b)
    (f : ℝ → ℝ) (m : ℕ) :
    referenceCellSquare D m (fun x : PolarPoint => f x.1) =
      profileScalarCellSquare D f m := by
  change (∫ r in D.a..D.b,
    radialAngularMean (fun _θ => (D.localizer m r * f r) ^ 2)) =
      ∫ r in radialCore D, (D.localizer m r * f r) ^ 2
  simp_rw [r11b_radialAngularMean_const]
  exact r11b_intervalIntegral_eq_core hab _

theorem r11b_radial_source_scalar_summable {D : ReferenceData}
    (hab : D.a ≤ D.b) {γ M : ℝ} {f : ℝ → ℝ}
    (hf : SourceDerivativeMember D γ M (fun x : PolarPoint => f x.1)) :
    Summable (fun m => Real.exp
      (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D f m) := by
  refine hf.2.congr (fun m => ?_)
  change Real.exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    referenceCellSquare D m (fun x : PolarPoint => f x.1) = _
  rw [r11b_referenceCellSquare_radial hab]

theorem r11b_chiLeft_flux_scalar_source_summable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) (γ M : ℝ) :
    Summable (fun m => Real.exp
      (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (deriv (fun t => D.w t * deriv D.chiLeft t)) m) :=
  r11b_radial_source_scalar_summable hD.choose_spec.1.2.1.le
    (r11b_chiLeft_flux_sourceDerivativeMember hD hborder γ M)

theorem r11b_referenceColumn_scalar_source_summable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {Mdata : RadialMatchingData D}
    (hM : ActualMatchedRepresentation D G Mdata) (γ M : ℝ) :
    Summable (fun m => Real.exp
      (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (referenceColumn D) m) := by
  obtain ⟨K, hK, hKcore, hs⟩ := r11b_referenceColumn_compact_core hM
  apply r11b_radial_source_scalar_summable hD.choose_spec.1.2.1.le
  apply r11b_compact_sourceDerivativeMember hD hK hKcore
    ((r11b_continuous_referenceColumn hD.choose_spec.1 hborder).comp continuous_fst)
  intro r _ hrK θ
  change referenceColumn D r = 0
  by_contra hne
  exact hrK (hs hne)

theorem r11b_deriv_zero_of_constant_on_Ioo {χ : ℝ → ℝ} {l h c : ℝ}
    (hχ : ∀ r ∈ Ioo l h, χ r = c) {r : ℝ} (hr : r ∈ Ioo l h) :
    deriv χ r = 0 := by
  have heq : χ =ᶠ[𝓝 r] (fun _ : ℝ => c) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact hχ t ht
  rw [heq.deriv_eq]
  exact deriv_const r c

theorem r11b_chiLeft_deriv_compact_core {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, r ∉ K → deriv D.chiLeft r = 0 := by
  obtain ⟨ε, hε, hleft, hright⟩ := hborder.2.2.2.2.2
  let δ : ℝ := min (ε / 2) ((D.b - D.a) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith [hgeom.2.1])
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨Icc (D.a + δ) (D.b - δ), isCompact_Icc, ?_, ?_⟩
  · intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · intro r hr hrK
    change ¬(D.a + δ ≤ r ∧ r ≤ D.b - δ) at hrK
    rcases not_and_or.mp hrK with hL | hR
    · apply r11b_deriv_zero_of_constant_on_Ioo hleft
      exact ⟨hr.1, by linarith [lt_of_not_ge hL]⟩
    · apply r11b_deriv_zero_of_constant_on_Ioo hright
      exact ⟨by linarith [lt_of_not_ge hR], hr.2⟩

theorem r11b_chiLeft_deriv_scalar_output_summable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) (γ M : ℝ) :
    Summable (fun m => Real.exp
      (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (deriv D.chiLeft) m) := by
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  obtain ⟨K, hK, hKcore, hz⟩ := r11b_chiLeft_deriv_compact_core hgeom hborder
  have hc : Continuous (deriv D.chiLeft) :=
    (contDiff_infty_iff_deriv.mp hborder.2.2.2.2.1).2.continuous
  have h := r11b_compact_output_cell_summable hD hK hKcore
    (hc.comp continuous_fst) (fun r hr hrK _ => hz r hr hrK) γ M
  refine h.2.congr (fun m => ?_)
  change Real.exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
    referenceCellSquare D m (fun x : PolarPoint => deriv D.chiLeft x.1) = _
  rw [r11b_referenceCellSquare_radial hgeom.2.1.le]

end ContinuousFlexibility.Radial
