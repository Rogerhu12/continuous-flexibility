module

public import ContinuousFlexibility.Analysis.N07aAngularClassicalEquation
public import ContinuousFlexibility.Analysis.N07aAngularPhysicalPairing
public import ContinuousFlexibility.Analysis.N07aAngularInteriorCoefficient
public import ContinuousFlexibility.Analysis.N07aAngularInnerIntervals

/-!
# Pointwise physical equation of the reconstructed weak representative

Only compact inner physical strips are used. The original full-period
weak equation is restricted to genuine compact canonical tests, then the
actual Green identity and L² test separation identify its classical
source. In particular no two-period test is silently treated as a
one-period test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {D : ReferenceData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_physicalWeak_smooth_classical (habD : D.a ≤ D.b)
    (A : SymmetricCoefficients)
    (hA : ContDiffOn ℝ ∞ A.a (annularOpen D) ∧
      ContDiffOn ℝ ∞ A.b (annularOpen D) ∧ ContDiffOn ℝ ∞ A.c (annularOpen D))
    (hAp : ∀ p ∈ annularOpen D, A.a (p + (0, Real.pi)) = A.a p ∧
      A.b (p + (0, Real.pi)) = A.b p ∧ A.c (p + (0, Real.pi)) = A.c p)
    (η f v f₀ ν ψ : PolarPoint → ℝ) (μ lam : ℝ)
    (hηp : Function.Periodic η (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (hv : ContDiffOn ℝ ∞ v (annularOpen D))
    (hf₀ : ContDiffOn ℝ ∞ f₀ (annularOpen D))
    (hν : ContDiffOn ℝ ∞ ν (annularOpen D))
    (hψ : ContDiffOn ℝ ∞ ψ (annularOpen D))
    (hvp : Function.Periodic v (0, Real.pi))
    (hf₀p : Function.Periodic f₀ (0, Real.pi))
    (hνp : Function.Periodic ν (0, Real.pi))
    (hψp : Function.Periodic ψ (0, Real.pi))
    (hve : v =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] η)
    (hfe : f =ᵐ[canonicalMeasure S (n07aRadialIntervalData K D.a D.b) 0] f₀)
    (heq : ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        η (r, θ) * divergenceOperator A φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => ν (r, θ) * φ (r, θ))) +
      lam * (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) :
    ∀ p ∈ annularOpen D, divergenceOperator A v p + μ * ν p + lam * ψ p = f₀ p := by
  let Full := n07aRadialIntervalData K D.a D.b
  have hdiv : ContDiffOn ℝ ∞ (divergenceOperator A v) (annularOpen D) :=
    n07a_canonicalOpen_divergence_contDiffOn (S := S) (K := Full) (m := 0)
      A hA.1 hA.2.1 hA.2.2 hv
  have hdivp : ∀ p ∈ annularOpen D,
      divergenceOperator A v (p + (0, Real.pi)) = divergenceOperator A v p :=
    n07a_canonicalOpen_divergence_periodic (S := S) (K := Full) (m := 0)
      A hA.1 hA.2.1 hA.2.2 (fun p hp => (hAp p hp).1)
      (fun p hp => (hAp p hp).2.1) (fun p hp => (hAp p hp).2.2) hv (fun p _ => hvp p)
  intro p hp
  let l := (D.a + p.1) / 2
  let r := (p.1 + D.b) / 2
  have hal : D.a < l := by dsimp only [l]; linarith [hp.1.1]
  have hlp : l < p.1 := by dsimp only [l]; linarith [hp.1.1]
  have hpr : p.1 < r := by dsimp only [r]; linarith [hp.1.2]
  have hrb : r < D.b := by dsimp only [r]; linarith [hp.1.2]
  have hlr := hlp.trans hpr
  have hinner : Icc l r ⊆ Ioo D.a D.b :=
    fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  let J := n07aRadialIntervalData K l r
  have hsub : Ioo (J.left 0) (J.right 0) ⊆ Ioo (Full.left 0) (Full.right 0) :=
    fun _ hx => hinner (Ioo_subset_Icc_self hx)
  have hsubp : canonicalOpen S J 0 ⊆ annularOpen D :=
    fun _ hx => ⟨hsub hx.1, mem_univ _⟩
  let aa : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.1 (fun q hq => (hAp q hq).1) hinner
  let bb : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.2.1 (fun q hq => (hAp q hq).2.1) hinner
  let cc : N07aCanonicalOpenCoefficient S J 0 :=
    n07aInteriorCoefficient hA.2.2 (fun q hq => (hAp q hq).2.2) hinner
  have hcoeff : (⟨aa.value, bb.value, cc.value⟩ : SymmetricCoefficients) = A := by
    cases A
    rfl
  let cu : N07aCanonicalOpenCoefficient S J 0 := n07aInteriorCoefficient hv (fun q _ => hvp q) hinner
  let cF : N07aCanonicalOpenCoefficient S J 0 := n07aInteriorCoefficient hf₀ (fun q _ => hf₀p q) hinner
  let cV : N07aCanonicalOpenCoefficient S J 0 := n07aInteriorCoefficient hν (fun q _ => hνp q) hinner
  let cW : N07aCanonicalOpenCoefficient S J 0 := n07aInteriorCoefficient hψ (fun q _ => hψp q) hinner
  let cd : N07aCanonicalOpenCoefficient S J 0 := n07aInteriorCoefficient hdiv hdivp hinner
  have hue : (cu.toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J 0] η :=
    cu.toLp_ae.trans (hve.filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub)))
  have hFe : (cF.toLp : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J 0] f :=
    cF.toLp_ae.trans (hfe.filter_mono (ae_mono (n07a_canonicalMeasure_mono hsub))).symm
  have hdist : N07aCanonicalDistributionEquation S J 0 A cu.toLp
      (cF.toLp - μ • cV.toLp - lam • cW.toLp) := by
    rw [← hcoeff]
    apply n07a_physicalWeak_inner_distribution habD hsub aa bb cc
      cu.toLp cF.toLp cV.toLp cW.toLp hue hFe cV.toLp_ae cW.toLp_ae
      (fun q _ => hηp q) (fun q _ => hfp q) (fun q _ => hνp q) (fun q _ => hψp q)
    simpa only [hcoeff, cV, cW, n07aInteriorCoefficient] using heq
  let rhs : PolarPoint → ℝ := fun q => f₀ q - μ * ν q - lam * ψ q
  have hrhs : (cF.toLp - μ • cV.toLp - lam • cW.toLp : CanonicalL2 S J 0)
      =ᵐ[canonicalMeasure S J 0] rhs := by
    filter_upwards [Lp.coeFn_sub (cF.toLp - μ • cV.toLp) (lam • cW.toLp),
      Lp.coeFn_sub cF.toLp (μ • cV.toLp), Lp.coeFn_smul μ cV.toLp,
      Lp.coeFn_smul lam cW.toLp, cF.toLp_ae, cV.toLp_ae, cW.toLp_ae]
      with q h₁ h₂ h₃ h₄ hF hV hW
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, hF, hV, hW]
    rfl
  have hrhss : ContDiffOn ℝ ∞ rhs (annularOpen D) :=
    (hf₀.sub (contDiffOn_const.mul hν)).sub (contDiffOn_const.mul hψ)
  have hrhsp : ∀ q ∈ canonicalOpen S J 0, rhs (q + (0, Real.pi)) = rhs q := by
    intro q _
    simp only [rhs, hf₀p q, hνp q, hψp q]
  have hLp : MemLp (divergenceOperator A v) 2 (canonicalMeasure S J 0) :=
    (memLp_congr_ae cd.toLp_ae).mp (Lp.memLp cd.toLp)
  have hpoint := n07a_openDistribution_smooth_eqOn hlr A
    (hA.1.mono hsubp) (hA.2.1.mono hsubp) (hA.2.2.mono hsubp)
    (fun q hq => (hAp q (hsubp hq)).1)
    (fun q hq => (hAp q (hsubp hq)).2.1)
    (fun q hq => (hAp q (hsubp hq)).2.2)
    (hv.mono hsubp) (fun q _ => hvp q) (hrhss.continuousOn.mono hsubp) hrhsp
    cu.toLp_ae hrhs hLp hdist ⟨⟨hlp, hpr⟩, mem_univ _⟩
  change divergenceOperator A v p = f₀ p - μ * ν p - lam * ψ p at hpoint
  linarith only [hpoint]

end ContinuousFlexibility.Analysis
