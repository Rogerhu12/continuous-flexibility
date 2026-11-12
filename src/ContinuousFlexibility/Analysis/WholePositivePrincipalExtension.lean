import ContinuousFlexibility.Analysis.WholePositivePrincipalJetMatching
import ContinuousFlexibility.Analysis.PositiveConformalCanonicalExtension

/-!
# A genuine smooth representative of the positive principal difference

For a whole positive component whose two endpoints lie in the physical
annulus, only the physical coefficient fields are cut off. The displayed
transport, inverse and height remain unchanged. The resulting global
smooth difference agrees with the actual difference as a joint germ on
the entire closed component, so all its true endpoint jets are retained.

No unit determinant, unit principal field or vanishing jet is an input.
Ambient endpoints are not covered by this buffered extension lemma.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem wholePositive_cutoff_mul_smooth
    {χ : ℝ → ℝ} {a b : ℝ} {f : PolarPoint → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo a b)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (fun p => χ p.1 * f p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ tsupport χ
  · exact (hχ.comp contDiff_fst).contDiffAt.mul
      (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs hp, mem_univ _⟩))
  · have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
      (continuous_fst.tendsto p)
    have he : (fun q : PolarPoint => χ q.1 * f q) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hz] with q hq
      have hq' : χ q.1 = 0 := by
        simpa only [Function.comp_apply, Pi.zero_apply] using hq
      simp only [hq', zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- The extension preserves the actual difference, not a replacement
normal form. The cutoff is applied before the genuine coordinate map. -/
theorem exists_wholePositivePrincipal_difference_extension
    {A Aref : SymmetricCoefficients} {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {a l r b c d : ℝ}
    (hal : a < l) (hlr : l < r) (hrb : r < b)
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (ha : ContDiffOn ℝ ∞ A.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb : ContDiffOn ℝ ∞ A.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : ContDiffOn ℝ ∞ A.c (Ioo a b ×ˢ (univ : Set ℝ)))
    (ha₀ : ContDiffOn ℝ ∞ Aref.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb₀ : ContDiffOn ℝ ∞ Aref.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc₀ : ContDiffOn ℝ ∞ Aref.c (Ioo a b ×ˢ (univ : Set ℝ))) :
    ∃ F : Fin 3 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (F i)) ∧
      ∀ i p, p ∈ Icc l r ×ˢ (univ : Set ℝ) →
        F i =ᶠ[𝓝 p] (fun q =>
          canonicalCoefficientComponent i (wholePositiveCanonicalCoefficients A τ σ Q) q -
            canonicalCoefficientComponent i Aref q) := by
  obtain ⟨χ, hχ, hsupport, hone⟩ := exists_bufferedRadialCutoff hal hlr.le hrb
  let Aext : SymmetricCoefficients :=
    ⟨fun p => χ p.1 * A.a p, fun p => χ p.1 * A.b p, fun p => χ p.1 * A.c p⟩
  let Arefext : SymmetricCoefficients :=
    ⟨fun p => χ p.1 * Aref.a p, fun p => χ p.1 * Aref.b p,
      fun p => χ p.1 * Aref.c p⟩
  have hAe : ContDiff ℝ ∞ Aext.a ∧ ContDiff ℝ ∞ Aext.b ∧ ContDiff ℝ ∞ Aext.c :=
    ⟨wholePositive_cutoff_mul_smooth hχ hsupport ha,
      wholePositive_cutoff_mul_smooth hχ hsupport hb,
      wholePositive_cutoff_mul_smooth hχ hsupport hc⟩
  have hAre : ContDiff ℝ ∞ Arefext.a ∧ ContDiff ℝ ∞ Arefext.b ∧
      ContDiff ℝ ∞ Arefext.c :=
    ⟨wholePositive_cutoff_mul_smooth hχ hsupport ha₀,
      wholePositive_cutoff_mul_smooth hχ hsupport hb₀,
      wholePositive_cutoff_mul_smooth hχ hsupport hc₀⟩
  let B := wholePositiveCanonicalCoefficients Aext τ σ Q
  have hD (p : PolarPoint) := contDiffAt_coordinatePrincipalDensity
    (hAe.1.contDiffAt (x := p)) hAe.2.1.contDiffAt hAe.2.2.contDiffAt
    H.chart_smooth.contDiffAt H.height_smooth.contDiffAt (H.jacobian_positive p).ne'
  have hBa : ContDiff ℝ ∞ B.a :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).1).comp H.inverse_smooth
  have hBb : ContDiff ℝ ∞ B.b :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).2.1).comp H.inverse_smooth
  have hBc : ContDiff ℝ ∞ B.c :=
    (contDiff_iff_contDiffAt.mpr fun p => (hD p).2.2).comp H.inverse_smooth
  have hBi (i : Fin 3) : ContDiff ℝ ∞ (canonicalCoefficientComponent i B) := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hBa
    · exact hBb
    · exact hBc
  have hAri (i : Fin 3) : ContDiff ℝ ∞ (canonicalCoefficientComponent i Arefext) := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hAre.1
    · exact hAre.2.1
    · exact hAre.2.2
  refine ⟨fun i q => canonicalCoefficientComponent i B q -
    canonicalCoefficientComponent i Arefext q, fun i => (hBi i).sub (hAri i), ?_⟩
  intro i p hp
  have hcurrent := (hone (τ p).1 (H.inverse_maps_closed (x := p) hp).1).comp_tendsto
    (H.inverse_smooth.continuous.fst.tendsto p)
  have hreference := (hone p.1 hp.1).comp_tendsto (continuous_fst.tendsto p)
  filter_upwards [hcurrent, hreference] with q hq hq₀
  have hq' : χ (τ q).1 = 1 := by
    simpa only [Function.comp_apply, Pi.one_apply] using hq
  have hq₀' : χ q.1 = 1 := by
    simpa only [Function.comp_apply, Pi.one_apply] using hq₀
  simp only [B, Aext, Arefext, wholePositiveCanonicalCoefficients,
    inverseChartPrincipalCoefficients, coordinatePrincipalDensity,
    canonicalCoefficientComponent, ite_apply, coefficientQuadratic, hq', hq₀', one_mul]

end ContinuousFlexibility.Analysis
