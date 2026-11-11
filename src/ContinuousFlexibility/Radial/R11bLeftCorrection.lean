import ContinuousFlexibility.Radial.R11bCompactSources

/-!
# The compact forcing produced by the left-tail constant

The tail cutoff is constant near each end of the core. Its conormal flux
therefore has zero derivative there. A single local-constant lemma treats
both endpoints and gives a compact interior correction in every cell weight.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_flux_deriv_zero_of_constant_on_Ioo {w χ : ℝ → ℝ} {l h c : ℝ}
    (hχ : ∀ r ∈ Ioo l h, χ r = c) {r : ℝ} (hr : r ∈ Ioo l h) :
    deriv (fun t => w t * deriv χ t) r = 0 := by
  have hd (t : ℝ) (ht : t ∈ Ioo l h) : deriv χ t = 0 := by
    have heq : χ =ᶠ[𝓝 t] (fun _ : ℝ => c) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
      exact hχ y hy
    rw [heq.deriv_eq]
    exact deriv_const t c
  have heq : (fun t => w t * deriv χ t) =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    rw [hd t ht, mul_zero]
  rw [heq.deriv_eq]
  exact deriv_const r 0

theorem r11b_chiLeft_flux_compact_core {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ radialCore D ∧
      ∀ r ∈ radialCore D, r ∉ K →
        deriv (fun t => D.w t * deriv D.chiLeft t) r = 0 := by
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
    · apply r11b_flux_deriv_zero_of_constant_on_Ioo hleft
      exact ⟨hr.1, by linarith [lt_of_not_ge hL]⟩
    · apply r11b_flux_deriv_zero_of_constant_on_Ioo hright
      exact ⟨by linarith [lt_of_not_ge hR], hr.2⟩

theorem r11b_continuous_chiLeft_flux {D : ReferenceData}
    (hgeom : RadialProfileGeometry D) (hborder : RadialTrueBorder D) :
    Continuous (deriv (fun t => D.w t * deriv D.chiLeft t)) := by
  have hχ : ContDiff ℝ ∞ (deriv D.chiLeft) :=
    (contDiff_infty_iff_deriv.mp hborder.2.2.2.2.1).2
  exact (contDiff_infty_iff_deriv.mp (hgeom.2.2.1.1.mul hχ)).2.continuous

theorem r11b_chiLeft_flux_sourceDerivativeMember {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) (γ M : ℝ) :
    SourceDerivativeMember D γ M (fun x : PolarPoint =>
      deriv (fun t => D.w t * deriv D.chiLeft t) x.1) := by
  obtain ⟨C, hgeom, hrest⟩ := hD
  obtain ⟨K, hK, hKcore, hz⟩ := r11b_chiLeft_flux_compact_core hgeom hborder
  apply r11b_compact_sourceDerivativeMember ⟨C, hgeom, hrest⟩ hK hKcore
    ((r11b_continuous_chiLeft_flux hgeom hborder).comp continuous_fst)
  exact fun r hr hrK _ => hz r hr hrK

theorem r11b_chiLeft_flux_output_cells {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D) (γ M : ℝ) :
    RadialCellIntegrable D (fun x : PolarPoint =>
        deriv (fun t => D.w t * deriv D.chiLeft t) x.1) ∧
      Summable (outputCellSquare D γ M (fun x : PolarPoint =>
        deriv (fun t => D.w t * deriv D.chiLeft t) x.1)) := by
  obtain ⟨C, hgeom, hrest⟩ := hD
  obtain ⟨K, hK, hKcore, hz⟩ := r11b_chiLeft_flux_compact_core hgeom hborder
  apply r11b_compact_output_cell_summable ⟨C, hgeom, hrest⟩ hK hKcore
    ((r11b_continuous_chiLeft_flux hgeom hborder).comp continuous_fst)
  exact fun r hr hrK _ => hz r hr hrK

end ContinuousFlexibility.Radial
