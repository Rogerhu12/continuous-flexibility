import ContinuousFlexibility.Analysis.WholePositiveAmbientPrincipal
import ContinuousFlexibility.Analysis.PositiveConformalCanonicalExtension

/-!
# A smooth principal difference patched by its flat physical difference

Only the physical coefficients are cut off before applying the actual
coordinate map. Outside the buffered middle, identity germs of the same
transport and gauge allow the flat physical difference to restore the
actual numerator. Its ambient germ is the flat representative, without
using any totalized physical coefficient value there.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem contDiff_flatPrincipal_cutoff_mul
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

/-- The central germ uses actual buffer invariance. In an identity germ,
the patch uses only the physical current-minus-reference germ. At an
ambient point it equals the supplied flat field as a genuine germ. -/
theorem exists_wholePositivePrincipal_flat_patch
    {A Aref : SymmetricCoefficients} {τ σ : PolarPoint → PolarPoint}
    {Q : PolarPoint → ℝ} {E : Fin 3 → PolarPoint → ℝ}
    {a u v b l r c d : ℝ}
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (H : WholePositiveChartGeometry σ τ (wholePositiveChartHeight σ Q) l r c d)
    (hmap : MapsTo τ (Icc u v ×ˢ (univ : Set ℝ))
      (Icc u v ×ˢ (univ : Set ℝ)))
    (ha : ContDiffOn ℝ ∞ A.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb : ContDiffOn ℝ ∞ A.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc : ContDiffOn ℝ ∞ A.c (Ioo a b ×ˢ (univ : Set ℝ)))
    (ha₀ : ContDiffOn ℝ ∞ Aref.a (Ioo a b ×ˢ (univ : Set ℝ)))
    (hb₀ : ContDiffOn ℝ ∞ Aref.b (Ioo a b ×ˢ (univ : Set ℝ)))
    (hc₀ : ContDiffOn ℝ ∞ Aref.c (Ioo a b ×ˢ (univ : Set ℝ)))
    (hE : ∀ i, ContDiff ℝ ∞ (E i)) :
    ∃ F : Fin 3 → PolarPoint → ℝ, (∀ i, ContDiff ℝ ∞ (F i)) ∧
      (∀ (i : Fin 3) (p : PolarPoint), p ∈ Icc u v ×ˢ (univ : Set ℝ) →
        F i =ᶠ[𝓝 p] (fun q => canonicalCoefficientComponent i
          (wholePositiveCanonicalCoefficients A τ σ Q) q -
            canonicalCoefficientComponent i Aref q)) ∧
      (∀ (i : Fin 3) (p : PolarPoint),
        τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) →
        σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) →
        Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) →
        E i =ᶠ[𝓝 p] (fun q => canonicalCoefficientComponent i A q -
          canonicalCoefficientComponent i Aref q) →
        F i =ᶠ[𝓝 p] (fun q => canonicalCoefficientComponent i
          (wholePositiveCanonicalCoefficients A τ σ Q) q -
            canonicalCoefficientComponent i Aref q)) ∧
      ∀ (i : Fin 3) (p : PolarPoint), p.1 ∉ Ioo a b →
        τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) →
        σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) →
        Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) → F i =ᶠ[𝓝 p] E i := by
  obtain ⟨χ, hχ, hsupport, hone⟩ := exists_bufferedRadialCutoff hau huv hvb
  let cut (B : SymmetricCoefficients) : SymmetricCoefficients :=
    ⟨fun p => χ p.1 * B.a p, fun p => χ p.1 * B.b p, fun p => χ p.1 * B.c p⟩
  have hcut (B : SymmetricCoefficients) (i : Fin 3) (p : PolarPoint) :
      canonicalCoefficientComponent i (cut B) p =
        χ p.1 * canonicalCoefficientComponent i B p := by
    unfold canonicalCoefficientComponent
    split_ifs <;> rfl
  have hAe : ContDiff ℝ ∞ (cut A).a ∧ ContDiff ℝ ∞ (cut A).b ∧
      ContDiff ℝ ∞ (cut A).c :=
    ⟨contDiff_flatPrincipal_cutoff_mul hχ hsupport ha,
      contDiff_flatPrincipal_cutoff_mul hχ hsupport hb,
      contDiff_flatPrincipal_cutoff_mul hχ hsupport hc⟩
  have hAre : ContDiff ℝ ∞ (cut Aref).a ∧ ContDiff ℝ ∞ (cut Aref).b ∧
      ContDiff ℝ ∞ (cut Aref).c :=
    ⟨contDiff_flatPrincipal_cutoff_mul hχ hsupport ha₀,
      contDiff_flatPrincipal_cutoff_mul hχ hsupport hb₀,
      contDiff_flatPrincipal_cutoff_mul hχ hsupport hc₀⟩
  let B := wholePositiveCanonicalCoefficients (cut A) τ σ Q
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
  have hAri (i : Fin 3) : ContDiff ℝ ∞ (canonicalCoefficientComponent i (cut Aref)) := by
    unfold canonicalCoefficientComponent
    split_ifs
    · exact hAre.1
    · exact hAre.2.1
    · exact hAre.2.2
  let F (i : Fin 3) (p : PolarPoint) : ℝ :=
    canonicalCoefficientComponent i B p - canonicalCoefficientComponent i (cut Aref) p +
      (1 - χ p.1) * E i p
  refine ⟨F, fun i => ((hBi i).sub (hAri i)).add
    ((contDiff_const.sub (hχ.comp contDiff_fst)).mul (hE i)), ?_, ?_, ?_⟩
  · intro i p hp
    have hcurrent := (hone (τ p).1 (hmap (x := p) hp).1).comp_tendsto
      (H.inverse_smooth.continuous.fst.tendsto p)
    have hreference := (hone p.1 hp.1).comp_tendsto (continuous_fst.tendsto p)
    filter_upwards [hcurrent, hreference] with q hq hq₀
    have hq' : χ (τ q).1 = 1 := by
      simpa only [Function.comp_apply, Pi.one_apply] using hq
    have hq₀' : χ q.1 = 1 := by
      simpa only [Function.comp_apply, Pi.one_apply] using hq₀
    simp only [F, B, cut, wholePositiveCanonicalCoefficients,
      inverseChartPrincipalCoefficients, coordinatePrincipalDensity,
      canonicalCoefficientComponent, ite_apply, coefficientQuadratic, hq', hq₀',
      one_mul, sub_self, zero_mul, add_zero]
  · intro i p hτ hσ hQ hphysical
    have hcutg := wholePositiveCanonicalCoefficient_identity_germ (cut A) hτ hσ hQ i
    have hactual := wholePositiveCanonicalCoefficient_identity_germ A hτ hσ hQ i
    filter_upwards [hcutg, hactual, hphysical] with q hcutq hactualq hphysicalq
    change canonicalCoefficientComponent i B q - canonicalCoefficientComponent i (cut Aref) q +
      (1 - χ q.1) * E i q = _
    change canonicalCoefficientComponent i B q = _ at hcutq
    rw [hcutq, hactualq, hphysicalq, hcut A i q, hcut Aref i q]
    ring
  · intro i p hp hτ hσ hQ
    have hnot : p.1 ∉ tsupport χ := fun hmem => hp (hsupport hmem)
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (continuous_fst.tendsto p)
    have hg := wholePositiveCanonicalCoefficient_identity_germ (cut A) hτ hσ hQ i
    filter_upwards [hz, hg] with q hzero hgq
    have hzero' : χ q.1 = 0 := by
      simpa only [Function.comp_apply, Pi.zero_apply] using hzero
    change canonicalCoefficientComponent i B q = _ at hgq
    change canonicalCoefficientComponent i B q - canonicalCoefficientComponent i (cut Aref) q +
      (1 - χ q.1) * E i q = E i q
    rw [hgq, hcut A i q, hcut Aref i q, hzero']
    ring

end ContinuousFlexibility.Analysis
