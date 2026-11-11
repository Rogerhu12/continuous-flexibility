import ContinuousFlexibility.Radial.ReferenceCosinePairing
import ContinuousFlexibility.Radial.ReferenceCosineTestOperator
import ContinuousFlexibility.Radial.ReferenceTestIntegrability

/-!
# Actual Fourier test pairings on the physical annulus

Every compact radial support is enclosed in one interior rectangle.
The frozen local cell L² condition already supplies ordinary L² on that
rectangle. Applying actual Fourier analysis there and then removing the
harmless restriction gives the paired series in the frozen dr integrals.
No global weighted-measure comparison is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private theorem memLp_normalized_angular {μ : Measure ℝ} {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (μ.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :
    MemLp f 2 (μ.prod referenceAngularMeasure) := by
  simpa only [referenceAngularMeasure, Measure.prod_smul_right] using
    hf.smul_measure (c := ENNReal.ofReal ((2 * Real.pi)⁻¹)) ENNReal.ofReal_ne_top

/-- The full paired series for any continuous, compactly radially supported test. -/
theorem RadialCellIntegrable.cosine_pairing_hasSum {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f)
    (hfp : Function.Periodic f (0, Real.pi))
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hg : Continuous g) {K : Set ℝ}
    (hK : IsCompact K) (hKcore : K ⊆ radialCore D)
    (hgs : ∀ r ∉ K, ∀ θ, g (r, θ) = 0) :
    HasSum (fun n : ℕ => ∫ r in D.a..D.b,
      referenceCosineCoefficient f n r * referenceCosineCoefficient g n r)
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * g (r, θ))) := by
  have hgeom : RadialProfileGeometry D := by
    obtain ⟨C, hC⟩ := hD
    exact hC.1
  obtain ⟨l, h, hal, hlh, hhb, hcover⟩ :=
    Radial.compact_subset_Ioo_enclosure hgeom.2.1 hK hKcore
  have hsub : Icc l h ⊆ radialCore D :=
    fun r hr => ⟨hal.trans_le hr.1, hr.2.trans_lt hhb⟩
  have hfl := memLp_normalized_angular (hf.memLp_on_interval hD hsub)
  have hgl := memLp_normalized_angular (continuous_memLp_reference_interval hg l h)
  have hfp' (r : ℝ) : Function.Periodic (fun θ => f (r, θ)) Real.pi := by
    intro θ
    have hh := hfp (r, θ)
    change f (r + 0, θ + Real.pi) = f (r, θ) at hh
    simpa only [add_zero] using hh
  have hi : Integrable (fun x : PolarPoint => f x * g x)
      ((volume.restrict (Icc l h)).prod referenceAngularMeasure) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hfl.toLp f) (hgl.toLp g)).congr
    filter_upwards [hfl.coeFn_toLp, hgl.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, hx, hy]
  have hinter (v : ℝ → ℝ) (hvs : Function.support v ⊆ K) :
      (∫ r, v r ∂volume.restrict (Icc l h)) = ∫ r in D.a..D.b, v r := by
    calc
      _ = ∫ r in Ioc l h, v r := integral_Icc_eq_integral_Ioc
      _ = ∫ r in l..h, v r := (intervalIntegral.integral_of_le hlh.le).symm
      _ = ∫ r : ℝ, v r :=
        Radial.intervalIntegral_eq_integral_of_support_subset hlh.le (hvs.trans hcover)
      _ = _ := (Radial.intervalIntegral_eq_integral_of_support_subset
        hgeom.2.1.le (hvs.trans hKcore)).symm
  have hcoeff (n : ℕ) :
      Function.support (fun r =>
        referenceCosineCoefficient f n r * referenceCosineCoefficient g n r) ⊆ K := by
    intro r hr
    by_contra hrK
    apply hr
    change referenceCosineCoefficient f n r * referenceCosineCoefficient g n r = 0
    rw [referenceCosineCoefficient_eq_zero_of_radial_support hgs n hrK, mul_zero]
  have hmean :
      Function.support (fun r => radialAngularMean (fun θ => f (r, θ) * g (r, θ))) ⊆ K := by
    intro r hr
    by_contra hrK
    apply hr
    simp only [radialAngularMean, hgs r hrK, mul_zero,
      intervalIntegral.integral_zero]
  have hs := referenceCosineAnalysis_pairing_hasSum hfl hfp' hfe hgl
  have hterms :
      (fun n : ℕ => ∫ r,
        referenceCosineCoefficient f n r * referenceCosineCoefficient g n r
        ∂volume.restrict (Icc l h)) =
      (fun n : ℕ => ∫ r in D.a..D.b,
        referenceCosineCoefficient f n r * referenceCosineCoefficient g n r) :=
    funext (fun n => hinter _ (hcoeff n))
  have hFub :
      (∫ x : PolarPoint, f x * g x
        ∂(volume.restrict (Icc l h)).prod referenceAngularMeasure) =
      ∫ r, radialAngularMean (fun θ => f (r, θ) * g (r, θ))
        ∂volume.restrict (Icc l h) := by
    rw [integral_prod _ hi]
    simp only [integral_referenceAngularMeasure]
  rw [hterms, hFub, hinter _ hmean] at hs
  exact hs

theorem RadialCellIntegrable.cosine_test_pairing_hasSum {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f)
    (hfp : Function.Periodic f (0, Real.pi))
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hψ : RadialTest D ψ) :
    HasSum (fun n : ℕ => ∫ r in D.a..D.b,
      referenceCosineCoefficient f n r * referenceCosineCoefficient ψ n r)
      (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * ψ (r, θ))) := by
  obtain ⟨K, hK, hKcore, hs⟩ := hψ.2.2
  exact hf.cosine_pairing_hasSum hD hfp hfe hψ.1.continuous hK hKcore hs

theorem RadialCellIntegrable.cosine_testOperator_pairing_hasSum {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {f ψ : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f)
    (hfp : Function.Periodic f (0, Real.pi))
    (hfe : ∀ r θ, f (r, -θ) = f (r, θ))
    (hψ : RadialTest D ψ) :
    HasSum (fun n : ℕ => ∫ r in D.a..D.b,
      referenceCosineCoefficient f n r *
        Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w
          (referenceCosineCoefficient ψ n) r)
      (radialWeakPairing D f ψ) := by
  obtain ⟨K, hK, hKcore, hs⟩ := hψ.operator_radial_support
  have hw : ContDiff ℝ ∞ D.w := by
    obtain ⟨C, hC⟩ := hD
    exact hC.1.2.2.1.1
  have hh := hf.cosine_pairing_hasSum hD hfp hfe
    (hψ.operator_continuous hD) hK hKcore hs
  change HasSum (fun n : ℕ => ∫ r in D.a..D.b,
    referenceCosineCoefficient f n r *
      referenceCosineCoefficient
        (fun x : PolarPoint => Radial.radialPDE D.w (fun t θ => ψ (t, θ)) x.1 x.2) n r)
    (radialWeakPairing D f ψ) at hh
  have hterms :
      (fun n : ℕ => ∫ r in D.a..D.b,
        referenceCosineCoefficient f n r *
          referenceCosineCoefficient
            (fun x : PolarPoint => Radial.radialPDE D.w (fun t θ => ψ (t, θ)) x.1 x.2) n r) =
      (fun n : ℕ => ∫ r in D.a..D.b,
        referenceCosineCoefficient f n r *
          Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) D.w
            (referenceCosineCoefficient ψ n) r) := by
    funext n
    apply intervalIntegral.integral_congr
    intro r _
    exact congrArg (fun z : ℝ => referenceCosineCoefficient f n r * z)
      (referenceCosineCoefficient_radialPDE hw hψ.1 hψ.2.1 n r)
  rw [hterms] at hh
  exact hh

end ContinuousFlexibility.Statements
