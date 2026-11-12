import ContinuousFlexibility.Analysis.N06AngularJetParseval
import ContinuousFlexibility.Analysis.N06CylinderLp
import ContinuousFlexibility.Analysis.N06WeakGraph

/-!
# Finite cylinder Parseval with merely L2 radial coefficients

Angular smoothness suffices for all pure angular derivatives. Radial
continuity is unnecessary: the actual half-period volume norm is computed
by Fubini from the L2 radial coefficients and the angular Gram matrix.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06_weak_unitWindow_eq_prod :
    cylinderWindowMeasure 0 = (volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
  rw [← n06_unitCanonicalMeasure_eq_window]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
    (Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) Real.pi) = _
  exact (Measure.prod_restrict _ _).symm

theorem n06_weak_halfPeriod_memLp_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
  have heq : (volume.restrict (Ioo (0 : ℝ) Real.pi) : Measure ℝ) =
      volume.restrict (Ioc (0 : ℝ) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [← heq]
  exact interval_memLp_of_continuous hf

/-- The original finite synthesis belongs to the canonical cylinder L2 space. -/
theorem n06_weak_finiteSynthesis_memLp {ι : Type*}
    (s : Finset ι) (u e : ι → ℝ → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : ∀ i ∈ s, Continuous (e i)) :
    MemLp (r11bFiniteSynthesis s u e) 2 (cylinderWindowMeasure 0) := by
  rw [n06_weak_unitWindow_eq_prod]
  exact memLp_finsetSum s (fun i hi => r11b_memLp_tensor (hu i hi)
    (n06_weak_halfPeriod_memLp_of_continuous (he i hi)))

/-- Actual volume Parseval with arbitrary L2 radial coefficients and a diagonal
angular Gram matrix, including zero angular vectors. -/
theorem n06_weak_finiteSynthesis_norm_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u e : ι → ℝ → ℝ) (w : ι → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : ∀ i ∈ s, Continuous (e i))
    (hp : ∀ i ∈ s, Function.Periodic (e i) Real.pi)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      angularPairing (e i) (e j) = if i = j then w i else 0)
    (hLp : MemLp (r11bFiniteSynthesis s u e) 2 (cylinderWindowMeasure 0)) :
    ‖hLp.toLp (r11bFiniteSynthesis s u e)‖ ^ 2 =
      Real.pi * ∑ i ∈ s, w i * ∫ y in (0 : ℝ)..1, u i y ^ 2 := by
  have hhalf (y : ℝ) :
      (∫ θ, r11bFiniteSynthesis s u e (y, θ) ^ 2
        ∂volume.restrict (Ioc (0 : ℝ) Real.pi)) =
        Real.pi * ∑ i ∈ s, w i * u i y ^ 2 := by
    have hc : Continuous (fun θ => r11bFiniteSynthesis s u e (y, θ)) := by
      change Continuous (fun θ : ℝ => ∑ i ∈ s, u i y * e i θ)
      exact continuous_finsetSum s (fun i hi => continuous_const.mul (he i hi))
    have hper : Function.Periodic (fun θ => r11bFiniteSynthesis s u e (y, θ))
        Real.pi := by
      intro θ
      exact Finset.sum_congr rfl (fun i hi => congrArg (fun z => u i y * z) (hp i hi θ))
    have hmean : angularAverage (fun θ => r11bFiniteSynthesis s u e (y, θ) ^ 2) =
        Real.pi⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
          r11bFiniteSynthesis s u e (y, θ) ^ 2 := by
      simpa only [angularAverage, radialAngularMean, one_div, Pi.pow_apply] using
        radialAngularMean_eq_halfPeriod
          (fun θ => congrArg (fun z : ℝ => z ^ 2) (hper θ))
          ((hc.pow 2).intervalIntegrable 0 (2 * Real.pi))
    have hparse : angularAverage (fun θ => r11bFiniteSynthesis s u e (y, θ) ^ 2) =
        ∑ i ∈ s, w i * u i y ^ 2 :=
      n06_angularAverage_sq_finite_orthogonal s e w (fun i => u i y) he horth
    calc
      _ = Real.pi * angularAverage (fun θ => r11bFiniteSynthesis s u e (y, θ) ^ 2) := by
        rw [hmean, intervalIntegral.integral_of_le Real.pi_pos.le]
        field_simp [Real.pi_ne_zero]
      _ = _ := by rw [hparse]
  have hi : Integrable (fun p => r11bFiniteSynthesis s u e p ^ 2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) Real.pi))) := by
    rw [← n06_weak_unitWindow_eq_prod]
    exact hLp.integrable_sq
  rw [r11b_norm_toLp_sq, n06_weak_unitWindow_eq_prod, integral_prod _ hi]
  simp_rw [hhalf]
  rw [integral_const_mul, integral_finsetSum s
    (fun i hi => (hu i hi).integrable_sq.const_mul (w i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, n06_unit_intervalIntegral_eq]

theorem n06_weak_referenceAngular_pairing (i j : ℕ) :
    angularPairing (referenceAngularBasis i) (referenceAngularBasis j) =
      if i = j then 1 else 0 := by
  simpa only [angularPairing, angularAverage, radialAngularMean, one_div] using
    referenceAngularBasis_pairing i j

/-- All actual angular derivatives exist in L2 even for nonsmooth radial coefficients. -/
theorem n06_weak_even_angularJet_memLp (s : Finset ℕ) (u : ℕ → ℝ → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ) :
    MemLp (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) 2
      (cylinderWindowMeasure 0) := by
  rw [n06_mixedAngularDerivative_finiteSynthesis s u referenceAngularBasis
    (fun i _ => contDiff_referenceAngularBasis i) k]
  exact n06_weak_finiteSynthesis_memLp s u _ hu (fun i _ =>
    (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) k).continuous)

/-- The k-th actual angular derivative has precisely the square weight (2i)^(2k). -/
theorem n06_weak_even_angularJet_norm_sq (s : Finset ℕ) (u : ℕ → ℝ → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict (Ioo (0 : ℝ) 1))) (k : ℕ)
    (hLp : MemLp (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) 2
      (cylinderWindowMeasure 0)) :
    ‖hLp.toLp (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis))‖ ^ 2 =
      Real.pi * ∑ i ∈ s, ((2 * i : ℕ) : ℝ) ^ (2 * k) *
        ∫ y in (0 : ℝ)..1, u i y ^ 2 := by
  have heq := n06_mixedAngularDerivative_finiteSynthesis s u referenceAngularBasis
    (fun i _ => contDiff_referenceAngularBasis i) k
  have hSyn : MemLp (r11bFiniteSynthesis s u
      (fun i => iteratedDeriv k (referenceAngularBasis i))) 2 (cylinderWindowMeasure 0) :=
    n06_weak_finiteSynthesis_memLp s u _ hu (fun i _ =>
      (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) k).continuous)
  have heqLp : hLp.toLp
      (mixedDerivative 0 k (r11bFiniteSynthesis s u referenceAngularBasis)) =
      hSyn.toLp (r11bFiniteSynthesis s u
        (fun i => iteratedDeriv k (referenceAngularBasis i))) :=
    MemLp.toLp_congr hLp hSyn (Eventually.of_forall fun p => congrFun heq p)
  rw [heqLp]
  apply n06_weak_finiteSynthesis_norm_sq s u _ _ hu
    (fun i _ =>
      (circleFourier_contDiff_iteratedDeriv (contDiff_referenceAngularBasis i) k).continuous)
    (fun i _ => circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) k)
    _ hSyn
  exact (n06_iteratedDeriv_partner_pairings s referenceAngularBasis n06AngularPartner
    (fun i => ((2 * i : ℕ) : ℝ))
    (fun i _ j _ => n06_weak_referenceAngular_pairing i j)
    (fun i _ j _ => n06_angularPartner_pairing i j)
    (fun i _ θ => n06_referenceAngularBasis_hasDerivAt i θ)
    (fun i _ θ => n06_angularPartner_hasDerivAt i θ) k).1

/-- Finite synthesis preserves almost-everywhere equality of its radial coefficients. -/
theorem n06_weak_finiteSynthesis_congr_ae {ι : Type*}
    (s : Finset ι) (u v e : ι → ℝ → ℝ)
    (huv : ∀ i ∈ s, u i =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v i) :
    r11bFiniteSynthesis s u e =ᵐ[cylinderWindowMeasure 0] r11bFiniteSynthesis s v e := by
  rw [n06_weak_unitWindow_eq_prod]
  have hall : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioc (0 : ℝ) Real.pi)), ∀ i ∈ s, u i p.1 = v i p.1 := by
    apply (eventually_all_finset s).mpr
    intro i hi
    exact (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := volume.restrict (Ioc (0 : ℝ) Real.pi))).ae_eq_comp (huv i hi)
  filter_upwards [hall] with p hp
  exact Finset.sum_congr rfl (fun i hi => congrArg (fun z => z * e i p.2) (hp i hi))

end ContinuousFlexibility.Analysis
