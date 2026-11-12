import ContinuousFlexibility.Analysis.N07aAngularOpenRegularity
import ContinuousFlexibility.Analysis.N07aAngularPhysicalPairing
import ContinuousFlexibility.Analysis.N07aAngularInteriorCoefficient
import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals
import ContinuousFlexibility.Analysis.N07aAngularDistributionRestriction
import ContinuousFlexibility.Analysis.N07aCanonicalPieceReconstruction

/-!
# Interior regularity of the original physical weak equation

The hypotheses describe the actual coefficients, source and weak pairing.
Only angular weak jets of the rough physical unknown are supplied. An
outer compact interval gives bounded actual coefficient jets; the true
second-normal primitive recovers one radial derivative on a smaller
interval, and the open bootstrap then supplies every mixed derivative of
the same L² class. No interface traces are required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}

private theorem n07aNormalRegular_smul {J : CanonicalData S} {m n : ℕ}
    {u : CanonicalL2 S J m} (hu : N07aCanonicalNormalRegular S J m u n) (c : ℝ) :
    N07aCanonicalNormalRegular S J m (c • u) n := by
  intro a ha b
  obtain ⟨v, hv⟩ := hu a ha b
  exact ⟨c • v, hv.smul c⟩

/-- Every compact inner physical strip has a smooth periodic representative
of the original rough unknown satisfying its original weak equation. -/
theorem n07a_physical_equation_innerSmooth (habD : D.a ≤ D.b)
    (A : SymmetricCoefficients)
    (hA : ContDiffOn ℝ ∞ A.a (annularOpen D) ∧
      ContDiffOn ℝ ∞ A.b (annularOpen D) ∧ ContDiffOn ℝ ∞ A.c (annularOpen D))
    (hAp : ∀ p ∈ annularOpen D, A.a (p + (0, Real.pi)) = A.a p ∧
      A.b (p + (0, Real.pi)) = A.b p ∧ A.c (p + (0, Real.pi)) = A.c p)
    (hapos : ∀ p ∈ annularOpen D, 0 < A.a p)
    (η f f₀ ν ψ : PolarPoint → ℝ) (μ lam : ℝ)
    (hηp : Function.Periodic η (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (hf₀ : ContDiffOn ℝ ∞ f₀ (annularOpen D))
    (hν : ContDiffOn ℝ ∞ ν (annularOpen D))
    (hψ : ContDiffOn ℝ ∞ ψ (annularOpen D))
    (hf₀p : Function.Periodic f₀ (0, Real.pi))
    (hνp : Function.Periodic ν (0, Real.pi))
    (hψp : Function.Periodic ψ (0, Real.pi))
    (hangular : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo D.a D.b →
      ∃ u : CanonicalL2 S (n07aRadialIntervalData K a b) 0,
        N07aCanonicalNormalRegular S (n07aRadialIntervalData K a b) 0 u 0 ∧
        (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S (n07aRadialIntervalData K a b) 0] η)
    (hsource : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo D.a D.b →
      f =ᵐ[canonicalMeasure S (n07aRadialIntervalData K a b) 0] f₀)
    (heq : ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        η (r, θ) * divergenceOperator A φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => ν (r, θ) * φ (r, θ))) +
      lam * (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ)))
    (l r : ℝ) (hlr : l < r) (hinner : Icc l r ⊆ Ioo D.a D.b) :
    ∃ v : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ v (canonicalOpen S (n07aRadialIntervalData K l r) 0) ∧
      Function.Periodic v (0, Real.pi) ∧
      v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K l r) 0] η := by
  let a := (D.a + l) / 2
  let b := (r + D.b) / 2
  have hal : D.a < l := (hinner ⟨le_rfl, hlr.le⟩).1
  have hrb : r < D.b := (hinner ⟨hlr.le, le_rfl⟩).2
  have haa : D.a < a := by dsimp only [a]; linarith
  have hal' : a < l := by dsimp only [a]; linarith
  have hrb' : r < b := by dsimp only [b]; linarith
  have hbb : b < D.b := by dsimp only [b]; linarith
  have hab : a < b := hal'.trans (hlr.trans hrb')
  have houter : Icc a b ⊆ Ioo D.a D.b :=
    fun _ hp => ⟨haa.trans_le hp.1, hp.2.trans_lt hbb⟩
  let J := n07aRadialIntervalData K a b
  let Q := n07aRadialIntervalData K l r
  have hsub : Ioo (Q.left 0) (Q.right 0) ⊆ Ioo (J.left 0) (J.right 0) :=
    fun _ hp => ⟨hal'.trans hp.1, hp.2.trans hrb'⟩
  let aa : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.1 (fun p hp => (hAp p hp).1) houter
  let bb : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.2.1 (fun p hp => (hAp p hp).2.1) houter
  let cc : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.2.2 (fun p hp => (hAp p hp).2.2) houter
  let ρ : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorReciprocal hA.1 (fun p hp => (hAp p hp).1)
      (fun p hp => (hapos p hp).ne') houter
  have hcoeff : (⟨aa.value, bb.value, cc.value⟩ : SymmetricCoefficients) = A := by
    cases A
    rfl
  have hinv : ∀ᵐ p ∂canonicalMeasure S J 0, ρ.value p * aa.value p = 1 :=
    n07aInteriorReciprocal_mul_value hA.1 (fun p hp => (hAp p hp).1)
      (fun p hp => (hapos p hp).ne') houter
  let cF : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hf₀ (fun p _ => hf₀p p) houter
  let cV : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hν (fun p _ => hνp p) houter
  let cW : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hψ (fun p _ => hψp p) houter
  obtain ⟨u, hu, hue⟩ := hangular a b hab houter
  have hFe : (cF.toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J 0] f :=
    cF.toLp_ae.trans (hsource a b hab houter).symm
  have hdist : N07aCanonicalDistributionEquation S J 0
      ⟨aa.value, bb.value, cc.value⟩ u (cF.toLp - μ • cV.toLp - lam • cW.toLp) := by
    apply n07a_physicalWeak_inner_distribution habD
      (fun x hx => houter (Ioo_subset_Icc_self hx)) aa bb cc
      u cF.toLp cV.toLp cW.toLp hue hFe cV.toLp_ae cW.toLp_ae
      (fun p _ => hηp p) (fun p _ => hfp p)
      (fun p _ => hνp p) (fun p _ => hψp p)
    simpa only [hcoeff, cV, cW, n07aInteriorCoefficient] using heq
  have hFreg (n : ℕ) : N07aCanonicalNormalRegular S J 0
      (cF.toLp - μ • cV.toLp - lam • cW.toLp) n :=
    ((cF.toLp_normalRegular n).sub
      (n07aNormalRegular_smul (cV.toLp_normalRegular n) μ)).sub
      (n07aNormalRegular_smul (cW.toLp_normalRegular n) lam)
  obtain ⟨ξ, hξ, hone⟩ := n07a_innerInterval_cutoff (S := S) (K := K) hal' hlr hrb'
  have hfirst := n07a_distribution_firstRegular_restrict hab aa bb cc ρ hinv hu
    (hFreg 0) hdist hsub hξ (fun p hp => hone p.1 (Ioo_subset_Icc_self hp.1))
  have hall := n07a_openDistribution_allNormal (aa.restrict hsub) (bb.restrict hsub)
    (cc.restrict hsub) (ρ.restrict hsub)
    (hinv.filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub))) hfirst
    (fun n => n07aCanonicalRestrict_normalRegular hsub (hFreg n))
    (n07a_distribution_restrict aa bb cc hsub hdist)
  obtain ⟨v, hv, hvp, hve, _⟩ :=
    n07a_exists_smooth_canonicalRepresentative hlr (n07aCanonicalRestrict hsub u) hall
  exact ⟨v, hv, hvp, hve.trans ((n07aCanonicalRestrict_ae hsub u).trans
    (hue.filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub))))⟩

end ContinuousFlexibility.Analysis
