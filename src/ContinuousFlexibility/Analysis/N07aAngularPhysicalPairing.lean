import ContinuousFlexibility.Analysis.N07aAngularPhysicalPatch
import ContinuousFlexibility.Analysis.N07aPeriodicRadialPairing
import ContinuousFlexibility.Analysis.N07aCanonicalTestOperator

/-!
# Restricting the original physical weak equation to an inner strip

The original equation uses the full normalized physical angular mean.
Actual local L² representatives and compact tests give integrability,
after which the exact half-period pairing gives the original distribution
equation on an arbitrary inner physical interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open ContinuousFlexibility.Radial
open scoped ContDiff Topology

variable {D : ReferenceData} {S : PhysicalSpacesData} {J : CanonicalData S} {n : ℕ}

theorem n07a_innerCanonicalTest_radial {φ : PolarPoint → ℝ}
    (hφ : CanonicalTest S J n φ)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b) : RadialTest D φ := by
  refine ⟨hφ.1, ?_, ?_⟩
  · intro p
    have hp := (hφ.2.1 (p + (0, Real.pi))).trans (hφ.2.1 p)
    have he : p + (0, Real.pi) + (0, Real.pi) = p + (0, 2 * Real.pi) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rwa [he] at hp
  · obtain ⟨Q, hQ, hQI, hzero⟩ := hφ.2.2
    exact ⟨Q, hQ, hQI.trans hsub, hzero⟩

/-- The full physical mean of a compactly tested rough function is its
actual local canonical pairing, with the exact factor `π⁻¹`. -/
theorem n07a_inner_radial_pairing (hab : D.a ≤ D.b)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    {f φ : PolarPoint → ℝ} (u : CanonicalL2 S J n)
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] f)
    (hp : ∀ p ∈ canonicalOpen S J n, f (p + (0, Real.pi)) = f p)
    (hφ : CanonicalTest S J n φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) =
      Real.pi⁻¹ * ∫ p, u p * φ p ∂canonicalMeasure S J n := by
  let Q : Set PolarPoint := Ioo (J.left n) (J.right n) ×ˢ Ioc (0 : ℝ) Real.pi
  let A : Set PolarPoint := Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi
  let g : PolarPoint → ℝ := fun p => f p * φ p
  have hQm : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioc
  have hAm : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioc
  have hQA : Q ⊆ A := fun _ hp => ⟨hsub hp.1, hp.2⟩
  have hge : (fun p => u p * φ p) =ᵐ[canonicalMeasure S J n] g :=
    hu.mono fun p hp => congrArg (· * φ p) hp
  have hQ : IntegrableOn g Q :=
    (integrable_congr hge).mp ((Lp.memLp u).integrable_mul (n07a_canonicalTest_memLp hφ))
  have houtside : ∀ p ∈ A \ Q, g p = 0 := by
    intro p hp
    have hpr : p.1 ∉ Ioo (J.left n) (J.right n) := fun hr => hp.2 ⟨hr, hp.1.2⟩
    exact (congrArg (f p * ·) (n07a_canonicalTest_zero_outside hφ hpr)).trans (mul_zero _)
  have hdiff : IntegrableOn g (A \ Q) := (integrable_congr
    ((ae_restrict_mem (hAm.diff hQm)).mono houtside)).mpr (integrable_zero _ _ _)
  have hA : IntegrableOn g A := (hQ.union hdiff).mono_set (by
    intro p hp
    by_cases h : p ∈ Q
    · exact Or.inl h
    · exact Or.inr ⟨hp, h⟩)
  have hmeasure : (volume.restrict (Ioo D.a D.b)).prod angleMeasure = volume.restrict A := by
    rw [angleMeasure, Measure.prod_restrict]
    rfl
  have hperiod : ∀ᵐ r ∂volume.restrict (Ioo D.a D.b),
      Function.Periodic (fun θ => g (r, θ)) Real.pi := by
    apply Eventually.of_forall
    intro r θ
    by_cases hr : r ∈ Ioo (J.left n) (J.right n)
    · have hpf := hp (r, θ) ⟨hr, mem_univ _⟩
      have hpφ := hφ.2.1 (r, θ)
      simpa only [g, Prod.mk_add_mk, add_zero] using congrArg₂ (· * ·) hpf hpφ
    · have hz (α : ℝ) : φ (r, α) = 0 :=
        n07a_canonicalTest_zero_outside (p := (r, α)) hφ hr
      simp only [g, hz, mul_zero]
  have hhalf := n07a_periodic_radial_mean_eq_half hab
    (show Integrable g ((volume.restrict (Ioo D.a D.b)).prod angleMeasure) by
      rw [hmeasure]; exact hA) hperiod
  rw [hmeasure] at hhalf
  calc
    _ = Real.pi⁻¹ * ∫ p in A, g p := hhalf
    _ = Real.pi⁻¹ * ∫ p in Q, g p := congrArg (Real.pi⁻¹ * ·)
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hAm hQA houtside)
    _ = _ := congrArg (Real.pi⁻¹ * ·) (integral_congr_ae hge).symm

/-- Restriction retains the original unknown and both scalar columns;
only the exact normalization of its test pairing changes. -/
theorem n07a_physicalWeak_inner_distribution (hab : D.a ≤ D.b)
    (hsub : Ioo (J.left n) (J.right n) ⊆ Ioo D.a D.b)
    (a b c : N07aCanonicalOpenCoefficient S J n)
    {η f ν ψ : PolarPoint → ℝ} {μ lam : ℝ}
    (u F V W : CanonicalL2 S J n)
    (hu : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] η)
    (hF : (F : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] f)
    (hV : (V : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] ν)
    (hW : (W : PolarPoint → ℝ) =ᵐ[canonicalMeasure S J n] ψ)
    (hηp : ∀ p ∈ canonicalOpen S J n, η (p + (0, Real.pi)) = η p)
    (hfp : ∀ p ∈ canonicalOpen S J n, f (p + (0, Real.pi)) = f p)
    (hνp : ∀ p ∈ canonicalOpen S J n, ν (p + (0, Real.pi)) = ν p)
    (hψp : ∀ p ∈ canonicalOpen S J n, ψ (p + (0, Real.pi)) = ψ p)
    (heq : ∀ φ, RadialTest D φ →
      (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) *
        divergenceOperator ⟨a.value, b.value, c.value⟩ φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => ν (r, θ) * φ (r, θ))) +
      lam * (∫ r in D.a..D.b, radialAngularMean (fun θ => ψ (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) :
    N07aCanonicalDistributionEquation S J n ⟨a.value, b.value, c.value⟩ u
      (F - μ • V - lam • W) := by
  intro φ hφ
  have hd := n07a_canonicalTest_divergence ⟨a.value, b.value, c.value⟩
    a.smooth b.smooth c.smooth a.periodic b.periodic c.periodic hφ
  have h := heq φ (n07a_innerCanonicalTest_radial hφ hsub)
  rw [n07a_inner_radial_pairing hab hsub u hu hηp hd,
    n07a_inner_radial_pairing hab hsub V hV hνp hφ,
    n07a_inner_radial_pairing hab hsub W hW hψp hφ,
    n07a_inner_radial_pairing hab hsub F hF hfp hφ] at h
  have hcancel : Real.pi⁻¹ *
      ((∫ p, u p * divergenceOperator ⟨a.value, b.value, c.value⟩ φ p ∂canonicalMeasure S J n) +
        μ * (∫ p, V p * φ p ∂canonicalMeasure S J n) +
        lam * (∫ p, W p * φ p ∂canonicalMeasure S J n) -
        ∫ p, F p * φ p ∂canonicalMeasure S J n) = 0 := by
    linear_combination h
  have hzero := (mul_eq_zero.mp hcancel).resolve_left (inv_ne_zero Real.pi_ne_zero)
  rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ),
    map_sub, map_sub, map_smul, map_smul,
    n07aCanonicalTestPairing_apply, n07aCanonicalTestPairing_apply,
    n07aCanonicalTestPairing_apply]
  simp only [smul_eq_mul]
  linarith only [hzero]

end ContinuousFlexibility.Analysis
