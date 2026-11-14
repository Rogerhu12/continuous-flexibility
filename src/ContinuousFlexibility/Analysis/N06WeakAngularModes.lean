module

public import ContinuousFlexibility.Analysis.N06WeakAngularCalculus
public import ContinuousFlexibility.Analysis.SpacesCircleFourierJets
public import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
public import ContinuousFlexibility.Radial.R11bModeL2

/-!
# Actual angular coefficients of canonical weak derivatives

Compact radial tests times smooth periodic angular factors belong to the
frozen canonical test class. Fubini and the fundamental lemma therefore
identify the radial coefficient functions of every weak angular jet.
The source and its derivative are arbitrary elements of the actual L² space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

/-- The upstream `SFinite angleMeasure` instances are private to their modules. -/
private instance : MeasureTheory.SFinite ContinuousFlexibility.Statements.angleMeasure := by
  unfold ContinuousFlexibility.Statements.angleMeasure; infer_instance

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

theorem n06_canonicalMeasure_eq_radial_prod
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ) :
    canonicalMeasure S K m =
      (volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) =
    (volume.restrict (Ioo (K.left m) (K.right m))).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi))
  exact (Measure.prod_restrict _ _).symm

/-- The coefficient uses the exact half-period angular measure. Dividing
by π gives the usual normalized Fourier coefficient. -/
def n06AngularCoefficient (f : PolarPoint → ℝ) (e : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ, f (r, θ) * e θ ∂angleMeasure

theorem n06_canonical_angularCoefficient_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) {e : ℝ → ℝ} (he : MemLp e 2 angleMeasure) :
    MemLp (n06AngularCoefficient f e) 2
      (volume.restrict (Ioo (K.left m) (K.right m))) := by
  have hf : MemLp (f : PolarPoint → ℝ) 2
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) :=
    (congrArg (fun μ : Measure PolarPoint => MemLp (f : PolarPoint → ℝ) 2 μ)
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mp (Lp.memLp f)
  exact (r11b_memLp_modeCoefficient hf he).1

theorem n06_canonicalTest_tensor
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ e : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo (K.left m) (K.right m))
    (he : ContDiff ℝ ∞ e) (hp : Function.Periodic e Real.pi) :
    CanonicalTest S K m (fun p => φ p.1 * e p.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (he.comp contDiff_snd), ?_,
    tsupport φ, hφc, hφs, ?_⟩
  · intro p
    simp only [Prod.fst_add, Prod.snd_add, add_zero, hp p.2]
  · intro r hr θ
    change φ r * e θ = 0
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem n06_mixedAngular_tensor (φ e : ℝ → ℝ) (j : ℕ) :
    mixedDerivative 0 j (fun p : PolarPoint => φ p.1 * e p.2) =
      fun p => φ p.1 * iteratedDeriv j e p.2 := by
  funext p
  simp only [mixedDerivative, iteratedDeriv_zero]
  exact iteratedDeriv_const_mul_field _ _

/-- Fubini for the actual canonical L² representative paired with a
continuous tensor. The radial coefficient is the original angular integral. -/
theorem n06_canonical_tensor_pairing
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (f : CanonicalL2 S K m) {φ e : ℝ → ℝ}
    (hφ : Continuous φ) (he : Continuous e) :
    (∫ p, f p * (φ p.1 * e p.2) ∂canonicalMeasure S K m) =
      ∫ r, n06AngularCoefficient f e r * φ r
        ∂volume.restrict (Ioo (K.left m) (K.right m)) := by
  have ht : Continuous (fun p : PolarPoint => φ p.1 * e p.2) :=
    (hφ.comp continuous_fst).mul (he.comp continuous_snd)
  have hi := n06_integrable_canonical_mul_continuous f ht
  have hiProd : Integrable (fun p => f p * (φ p.1 * e p.2))
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure) :=
    (congrArg (fun μ : Measure PolarPoint =>
      Integrable (fun p => f p * (φ p.1 * e p.2)) μ)
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mp hi
  have hInt := congrArg (fun μ : Measure PolarPoint =>
    ∫ p, f p * (φ p.1 * e p.2) ∂μ)
      (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)
  rw [hInt, integral_prod _ hiProd]
  apply integral_congr_ae
  filter_upwards with r
  change (∫ θ, f (r, θ) * (φ r * e θ) ∂angleMeasure) =
    (∫ θ, f (r, θ) * e θ ∂angleMeasure) * φ r
  have hfun : (fun θ => f (r, θ) * (φ r * e θ)) =
      fun θ => (f (r, θ) * e θ) * φ r := by
    funext θ
    ring
  rw [hfun, integral_mul_const]

/-- The canonical weak identity tested on a tensor is the genuine radial
coefficient identity, for every angular derivative order. -/
theorem WeakCanonicalAngularDerivative.n06_coefficient_pairing
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    {e φ : ℝ → ℝ} (he : ContDiff ℝ ∞ e) (hp : Function.Periodic e Real.pi)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo (K.left m) (K.right m)) :
    (∫ r, n06AngularCoefficient g e r * φ r
      ∂volume.restrict (Ioo (K.left m) (K.right m))) =
      (-1 : ℝ) ^ j * (∫ r, n06AngularCoefficient f (iteratedDeriv j e) r * φ r
        ∂volume.restrict (Ioo (K.left m) (K.right m))) := by
  have h := hfg _ (n06_canonicalTest_tensor hφ hφc hφs he hp)
  rw [n06_mixedAngular_tensor,
    n06_canonical_tensor_pairing g hφ.continuous he.continuous,
    n06_canonical_tensor_pairing f hφ.continuous
      (circleFourier_contDiff_iteratedDeriv he j).continuous] at h
  exact h

private theorem n06_radial_test_setIntegral_eq_integral
    {l r : ℝ} (c : ℝ → ℝ) {φ : ℝ → ℝ} (hφs : tsupport φ ⊆ Ioo l r) :
    (∫ x, c x * φ x ∂volume.restrict (Ioo l r)) = ∫ x, c x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), mul_zero]

/-- Weak angular differentiation determines the actual radial coefficient
functions almost everywhere. No smooth representative of either L² field
is used, and no sectionwise weak derivative is assumed. -/
theorem WeakCanonicalAngularDerivative.n06_coefficient_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m j : ℕ}
    {f g : CanonicalL2 S K m}
    (hfg : WeakCanonicalAngularDerivative S K m f g j)
    {e : ℝ → ℝ} (he : ContDiff ℝ ∞ e) (hp : Function.Periodic e Real.pi) :
    n06AngularCoefficient g e =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))]
      (fun r => (-1 : ℝ) ^ j * n06AngularCoefficient f (iteratedDeriv j e) r) := by
  let μ : Measure ℝ := volume.restrict (Ioo (K.left m) (K.right m))
  let Cg := n06AngularCoefficient g e
  let Cf := n06AngularCoefficient f (iteratedDeriv j e)
  let σ : ℝ := (-1) ^ j
  letI : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show Ioo (K.left m) (K.right m) ⊆
      Icc (K.left m) (K.right m) from Ioo_subset_Icc_self)).trans_lt
        isCompact_Icc.measure_lt_top⟩
  have hcg : MemLp Cg 2 μ := n06_canonical_angularCoefficient_memLp g
    (memLp_angleMeasure_of_continuous he.continuous)
  have hcf : MemLp Cf 2 μ := n06_canonical_angularCoefficient_memLp f
    (memLp_angleMeasure_of_continuous (circleFourier_contDiff_iteratedDeriv he j).continuous)
  have hcgLoc : LocallyIntegrableOn Cg (Ioo (K.left m) (K.right m)) volume :=
    (show IntegrableOn Cg (Ioo (K.left m) (K.right m)) volume from
      hcg.integrable (by norm_num)).locallyIntegrableOn
  have hcfLoc : LocallyIntegrableOn Cf (Ioo (K.left m) (K.right m)) volume :=
    (show IntegrableOn Cf (Ioo (K.left m) (K.right m)) volume from
      hcf.integrable (by norm_num)).locallyIntegrableOn
  have hsLoc : LocallyIntegrableOn (fun r => σ * Cf r)
      (Ioo (K.left m) (K.right m)) volume := by
    have heq : σ • Cf = (fun r => σ * Cf r) := by funext r; rfl
    rw [← heq]
    exact hcfLoc.smul σ
  have hzero : ∀ᵐ r ∂volume, r ∈ Ioo (K.left m) (K.right m) → Cg r - σ * Cf r = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hcgLoc.sub hsLoc)
    intro φ hφ hφc hφs
    have hig : Integrable (fun r => Cg r * φ r) :=
      Analysis.interval_integrable_mul_test hcgLoc hφ.continuous hφc hφs
    have hif : Integrable (fun r => Cf r * φ r) :=
      Analysis.interval_integrable_mul_test hcfLoc hφ.continuous hφc hφs
    have hpair := hfg.n06_coefficient_pairing he hp hφ hφc hφs
    rw [n06_radial_test_setIntegral_eq_integral _ hφs,
      n06_radial_test_setIntegral_eq_integral _ hφs] at hpair
    change (∫ r, Cg r * φ r) = σ * (∫ r, Cf r * φ r) at hpair
    have hfun : (fun r => φ r • (Cg r - σ * Cf r)) =
        fun r => Cg r * φ r - σ * (Cf r * φ r) := by
      funext r
      simp only [smul_eq_mul]
      ring
    have hsub := integral_sub hig (hif.const_mul σ)
    change (∫ r, Cg r * φ r - σ * (Cf r * φ r)) =
      (∫ r, Cg r * φ r) - ∫ r, σ * (Cf r * φ r) at hsub
    change (∫ r, φ r • (Cg r - σ * Cf r)) = 0
    rw [hfun, hsub, integral_const_mul, hpair, sub_self]
  have hz : ∀ᵐ r ∂μ, Cg r - σ * Cf r = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hzero
  filter_upwards [hz] with r hr
  exact sub_eq_zero.mp hr

end ContinuousFlexibility.Statements
