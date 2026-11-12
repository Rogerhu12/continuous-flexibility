import ContinuousFlexibility.Analysis.N07aAngularRadialRecovery
import ContinuousFlexibility.Analysis.N07aAngularEven
import ContinuousFlexibility.Analysis.N07aLocalizedWeakJets
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# Angular weak jets extend across radial piece endpoints

Only angular integration by parts is used. A radial indicator therefore
introduces no boundary term. Every angular jet of a smooth interior L²
representative extends by zero as its genuine cylinder weak derivative,
even when no radial trace is known.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

/-- Angular integration by parts requires no compact support inside the
radial piece. The only boundaries involved are the two equal angular ends. -/
theorem n07a_angular_piece_first_pairing {f φ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hLp : MemLp f 2 (canonicalMeasure S K m))
    (hdLp : MemLp (mixedDerivative 0 1 f) 2 (canonicalMeasure S K m))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, mixedDerivative 0 1 f p * φ p ∂canonicalMeasure S K m) =
      -(∫ p, f p * mixedDerivative 0 1 φ p ∂canonicalMeasure S K m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hi₁ : Integrable (fun p => mixedDerivative 0 1 f p * φ p)
      (canonicalMeasure S K m) := by
    simpa only [Pi.mul_def] using
      hdLp.integrable_mul (n07a_smoothCanonical_memLp hφ)
  have hi₂ : Integrable (fun p => f p * mixedDerivative 0 1 φ p)
      (canonicalMeasure S K m) := by
    simpa only [Pi.mul_def] using hLp.integrable_mul
      (n07a_smoothCanonical_memLp (contDiff_mixedDerivative hφ 0 1))
  have hrow (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      (∫ θ, mixedDerivative 0 1 f (r, θ) * φ (r, θ) ∂angleMeasure) =
        -(∫ θ, f (r, θ) * mixedDerivative 0 1 φ (r, θ) ∂angleMeasure) := by
    have hfs : ContDiff ℝ ∞ (fun θ : ℝ => f (r, θ)) :=
      hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨hr, mem_univ _⟩)
    have hps : ContDiff ℝ ∞ (fun θ : ℝ => φ (r, θ)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    have hdf : Continuous (fun θ => mixedDerivative 0 1 f (r, θ)) :=
      (contDiffOn_mixedDerivative hU hf 0 1).continuousOn.comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ => ⟨hr, mem_univ _⟩)
    have hdp : Continuous (fun θ => mixedDerivative 0 1 φ (r, θ)) :=
      (contDiff_mixedDerivative hφ 0 1).continuous.comp
        (continuous_const.prodMk continuous_id)
    have hder (θ : ℝ) : HasDerivAt (fun t => f (r, t) * φ (r, t))
        (mixedDerivative 0 1 f (r, θ) * φ (r, θ) +
          f (r, θ) * mixedDerivative 0 1 φ (r, θ)) θ := by
      simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one] using
        ((hfs.differentiable (by simp) θ).hasDerivAt.fun_mul
          (hps.differentiable (by simp) θ).hasDerivAt)
    have hint := ((hdf.mul hps.continuous).add (hfs.continuous.mul hdp)).intervalIntegrable
      (μ := volume) 0 Real.pi
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ) hint
    have hfe : f (r, Real.pi) = f (r, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hfp (r, 0) ⟨hr, mem_univ _⟩
    have hpe : φ (r, Real.pi) = φ (r, 0) := by
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using hφp (r, 0)
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, hfe, hpe, sub_self] at hftc
    have hiR : Integrable (fun θ => mixedDerivative 0 1 f (r, θ) * φ (r, θ)) angleMeasure :=
      (hdf.mul hps.continuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hiA : Integrable (fun θ => f (r, θ) * mixedDerivative 0 1 φ (r, θ)) angleMeasure :=
      (hfs.continuous.mul hdp).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hadd := integral_add hiR hiA
    change (∫ θ, mixedDerivative 0 1 f (r, θ) * φ (r, θ) +
      f (r, θ) * mixedDerivative 0 1 φ (r, θ) ∂angleMeasure) = 0 at hftc
    rw [hadd] at hftc
    linarith only [hftc]
  rw [n07aCanonicalMeasure_eq_prod] at hi₁ hi₂ ⊢
  rw [integral_prod _ hi₁, integral_prod _ hi₂, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact hrow r hr

/-- The same actual representative has every weak angular derivative when
tested against a smooth periodic function, without radial endpoint conditions. -/
theorem n07a_angular_piece_pairing {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hLp : ∀ n, MemLp (mixedDerivative 0 n f) 2 (canonicalMeasure S K m))
    (n : ℕ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, mixedDerivative 0 n f p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ n * ∫ p, f p * mixedDerivative 0 n φ p ∂canonicalMeasure S K m := by
  induction n generalizing φ with
  | zero => simp only [pow_zero, one_mul, spaces_mixedDerivative_zero]
  | succ n ih =>
    have hU : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
    have he : mixedDerivative 0 1 (mixedDerivative 0 n f) =ᵐ[canonicalMeasure S K m]
        mixedDerivative 0 (n + 1) f := by
      filter_upwards [n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp
      simpa only [Nat.zero_add, Nat.add_comm] using
        n07a_mixedDerivative_mixedDerivative_on hU hf 0 1 0 n hp
    have hfirst := n07a_angular_piece_first_pairing
      (contDiffOn_mixedDerivative hU hf 0 n) (n07a_mixedDerivative_periodic_on hfp 0 n)
      (hLp n) ((memLp_congr_ae he).mpr (hLp (n + 1))) hφ hφp
    have hleft : (∫ p, mixedDerivative 0 1 (mixedDerivative 0 n f) p * φ p
        ∂canonicalMeasure S K m) =
        ∫ p, mixedDerivative 0 (n + 1) f p * φ p ∂canonicalMeasure S K m :=
      integral_congr_ae (he.mono fun p hp => congrArg (· * φ p) hp)
    rw [hleft, ih (contDiff_mixedDerivative hφ 0 1)
      (n07a_canonicalCoefficient_derivative_periodic hφp 0 1)] at hfirst
    have ht : mixedDerivative 0 n (mixedDerivative 0 1 φ) = mixedDerivative 0 (n + 1) φ := by
      funext p
      simpa only [Nat.zero_add] using
        n07a_mixedDerivative_mixedDerivative_on isOpen_univ hφ.contDiffOn 0 n 0 1 (mem_univ p)
    rw [ht] at hfirst
    simpa only [pow_succ, mul_neg_one, neg_mul] using hfirst

def n07aPieceAngularJet {f : PolarPoint → ℝ}
    (hLp : ∀ n, MemLp (mixedDerivative 0 n f) 2 (canonicalMeasure S K m))
    (n : ℕ) : CylinderL2 :=
  n07aCanonicalExtension ((hLp n).toLp (mixedDerivative 0 n f))

theorem n07aPieceAngularJet_ae {f : PolarPoint → ℝ}
    (hLp : ∀ n, MemLp (mixedDerivative 0 n f) 2 (canonicalMeasure S K m)) (n : ℕ) :
    (n07aPieceAngularJet hLp n : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (canonicalOpen S K m).indicator (mixedDerivative 0 n f) := by
  filter_upwards [n07aCanonicalZeroExtension_ae ((hLp n).toLp (mixedDerivative 0 n f)),
    n07aCanonical_ae_imp (MemLp.coeFn_toLp (hLp n))] with p hp hq
  change n07aCanonicalExtension _ p = _
  rw [n07aCanonicalExtension_apply, hp]
  by_cases hpm : p ∈ canonicalOpen S K m
  · simp only [indicator_of_mem hpm]
    exact hq hpm
  · simp only [indicator_of_notMem hpm]

/-- Radial zero extension preserves every angular weak derivative. No
radial derivative or trace of the piece function is an input. -/
theorem n07aPieceAngularJet_weak {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    (hLp : ∀ n, MemLp (mixedDerivative 0 n f) 2 (canonicalMeasure S K m)) (n : ℕ) :
    HasWeakMixedDerivative (n07aPieceAngularJet hLp 0) (n07aPieceAngularJet hLp n) 0 n := by
  intro φ hφ
  rw [n07aPieceAngularJet, n07aPieceAngularJet, n07aCanonicalExtension_pairing,
    n07aCanonicalExtension_pairing]
  have hi (k : ℕ) (ψ : PolarPoint → ℝ) :
      (∫ p, (hLp k).toLp (mixedDerivative 0 k f) p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, mixedDerivative 0 k f p * ψ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hLp k)] with p hp
    rw [hp]
  rw [hi n φ, hi 0 _, spaces_mixedDerivative_zero]
  simpa only [Nat.zero_add] using n07a_angular_piece_pairing hf hfp hLp n hφ.1 hφ.2.1

end ContinuousFlexibility.Analysis
