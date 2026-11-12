import ContinuousFlexibility.Analysis.N06EvenCylinder
import ContinuousFlexibility.Analysis.N06CubicLp
import ContinuousFlexibility.Scalar.Conservation
import Mathlib.Tactic.FinCases

/-!
# The cubic graph estimate in the actual cylinder L² space

The normalized Fourier square integrals are identified with the existing
`cylinderWindowMeasure 0`. The five fields used by the differential
perturbation estimate therefore have a genuine L² graph bound, with the
same constant as the scalar positive-cylinder estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem n06_continuous_integrable_unitWindow {f : PolarPoint → ℝ}
    (hf : Continuous f) : Integrable f (cylinderWindowMeasure 0) := by
  have h : IntegrableOn f (Icc (0 : ℝ) 1 ×ˢ Icc 0 Real.pi) volume :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simpa only [cylinderWindowMeasure, cylinderWindow, zero_add, IntegrableOn] using
    h.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The canonical open radial interval and the existing cylinder window
carry the same measure; endpoint conventions introduce no new source space. -/
theorem n06_unitCanonicalMeasure_eq_window :
    (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) Real.pi) : Measure PolarPoint) =
      cylinderWindowMeasure 0 := by
  rw [cylinderWindowMeasure_eq_prod, zero_add]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) Real.pi) =
    (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) Real.pi))
  rw [← Measure.prod_restrict]
  congr 1
  exact Measure.restrict_congr_set Ioo_ae_eq_Ioc

/-- Fubini on the actual half-period cylinder. -/
theorem n06_integral_unitWindow {f : PolarPoint → ℝ} (hf : Continuous f) :
    (∫ p, f p ∂cylinderWindowMeasure 0) =
      ∫ y in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..Real.pi, f (y, θ) := by
  have h := n06_continuous_integrable_unitWindow hf
  rw [cylinderWindowMeasure_eq_prod] at h ⊢
  rw [integral_prod _ h]
  simp only [zero_add, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le Real.pi_pos.le]

private theorem n06_periodic_slice {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (y : ℝ) :
    Function.Periodic (fun θ => f (y, θ)) Real.pi := by
  intro θ
  simpa only [Prod.mk_add_mk, add_zero] using hf (y, θ)

/-- Parseval's normalization is exactly the half-period volume factor. -/
theorem n06_weighted_integral_eq_pi_mul_square (k : ℕ) (U : PolarPoint → ℝ)
    (hU : Continuous U) (hp : Function.Periodic U (0, Real.pi)) :
    (∫ p, cylinderWeight p.1 ^ k * U p ^ 2 ∂cylinderWindowMeasure 0) =
      Real.pi * n06CylinderSquare k U := by
  have h := n06CylinderSquare_eq_halfPeriod k U hU (n06_periodic_slice hp)
  have hw : Continuous (fun p : PolarPoint => cylinderWeight p.1 ^ k * U p ^ 2) :=
    ((cylinderWeight_continuous.comp continuous_fst).pow k).mul (hU.pow 2)
  have hi : (∫ p, cylinderWeight p.1 ^ k * U p ^ 2 ∂cylinderWindowMeasure 0) =
      ∫ y in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..Real.pi, cylinderWeight y ^ k * U (y, θ) ^ 2 :=
    n06_integral_unitWindow hw
  have hi' : (∫ p, cylinderWeight p.1 ^ k * U p ^ 2 ∂cylinderWindowMeasure 0) =
      ∫ y in (0 : ℝ)..1, cylinderWeight y ^ k *
        (∫ θ in (0 : ℝ)..Real.pi, U (y, θ) ^ 2) := by
    rw [hi]
    apply intervalIntegral.integral_congr
    intro y _
    exact intervalIntegral.integral_const_mul _ _
  rw [← hi'] at h
  have hd : n06CylinderSquare k U =
      (∫ p, cylinderWeight p.1 ^ k * U p ^ 2 ∂cylinderWindowMeasure 0) / Real.pi := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  simpa only [mul_comm] using ((eq_div_iff Real.pi_ne_zero).mp hd).symm

theorem n06CylinderSquare_nonneg (k : ℕ) (U : PolarPoint → ℝ) :
    0 ≤ n06CylinderSquare k U := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro y hy
  apply mul_nonneg (pow_nonneg (cylinderWeight_nonneg hy) k)
  rw [angularAverage_eq_integral_angularMeanMeasure]
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Smoothness supplies membership of all five weighted derivative fields. -/
theorem n06_cubicGraphFields_memLp {U : PolarPoint → ℝ} (hU : ContDiff ℝ ∞ U)
    (i : Fin 5) :
    MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) U i) 2
      (cylinderWindowMeasure 0) := by
  have hd : Continuous (fun p : PolarPoint => cylinderWeight p.1) :=
    cylinderWeight_continuous.comp continuous_fst
  have hr := contDiff_cylinder_radialPartial hU
  have ht := contDiff_cylinder_angularPartial hU
  have hrr := contDiff_cylinder_radialPartial hr
  have hrt := contDiff_cylinder_angularPartial hr
  have htt := contDiff_cylinder_angularPartial ht
  fin_cases i
  · exact continuous_memLp_cylinderWindow ((hd.pow 2).mul hrr.continuous) 0
  · exact continuous_memLp_cylinderWindow
      (((hd.pow 2).mul hd.sqrt).mul hrt.continuous) 0
  · exact continuous_memLp_cylinderWindow ((hd.pow 3).mul htt.continuous) 0
  · exact continuous_memLp_cylinderWindow (hd.mul hr.continuous) 0
  · exact continuous_memLp_cylinderWindow ((hd.mul hd.sqrt).mul ht.continuous) 0

/-- The five actual L² fields are controlled by the full cylinder graph
quantity. The extra zeroth-order terms in that graph quantity are nonnegative. -/
theorem n06_cubicGraphFields_norm_sq_le_graph
    {U : PolarPoint → ℝ} (hU : ContDiff ℝ ∞ U)
    (hp : Function.Periodic U (0, Real.pi))
    (hgraph : ∀ i, MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) U i) 2
      (cylinderWindowMeasure 0)) :
    (∑ i, ‖(hgraph i).toLp
      (n06CubicGraphFields (fun p => cylinderWeight p.1) U i)‖ ^ 2) ≤
        Real.pi * n06CylinderGraphSquare U := by
  have hd : Continuous (fun p : PolarPoint => cylinderWeight p.1) :=
    cylinderWeight_continuous.comp continuous_fst
  have hr := contDiff_cylinder_radialPartial hU
  have ht := contDiff_cylinder_angularPartial hU
  have hrr := contDiff_cylinder_radialPartial hr
  have hrt := contDiff_cylinder_angularPartial hr
  have htt := contDiff_cylinder_angularPartial ht
  have hpr := periodic_radialPartial hp
  have hpt := periodic_angularPartial hp
  have hprr := periodic_radialPartial hpr
  have hprt := periodic_angularPartial hpr
  have hptt := periodic_angularPartial hpt
  have hi4 : Integrable (fun p => cylinderWeight p.1 ^ 4 *
      radialPartial (radialPartial U) p ^ 2) (cylinderWindowMeasure 0) :=
    n06_continuous_integrable_unitWindow ((hd.pow 4).mul (hrr.continuous.pow 2))
  have hi5 : Integrable (fun p => cylinderWeight p.1 ^ 5 *
      angularPartial (radialPartial U) p ^ 2) (cylinderWindowMeasure 0) :=
    n06_continuous_integrable_unitWindow ((hd.pow 5).mul (hrt.continuous.pow 2))
  have hi6 : Integrable (fun p => cylinderWeight p.1 ^ 6 *
      angularPartial (angularPartial U) p ^ 2) (cylinderWindowMeasure 0) :=
    n06_continuous_integrable_unitWindow ((hd.pow 6).mul (htt.continuous.pow 2))
  have hi2 : Integrable (fun p => cylinderWeight p.1 ^ 2 *
      radialPartial U p ^ 2) (cylinderWindowMeasure 0) :=
    n06_continuous_integrable_unitWindow ((hd.pow 2).mul (hr.continuous.pow 2))
  have hi3 : Integrable (fun p => cylinderWeight p.1 ^ 3 *
      angularPartial U p ^ 2) (cylinderWindowMeasure 0) :=
    n06_continuous_integrable_unitWindow ((hd.pow 3).mul (ht.continuous.pow 2))
  have hmem : ∀ᵐ p ∂cylinderWindowMeasure 0, p ∈ cylinderWindow 0 :=
    ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hdAE : ∀ᵐ p ∂cylinderWindowMeasure 0, 0 ≤ cylinderWeight p.1 := by
    filter_upwards [hmem] with p hp
    exact cylinderWeight_nonneg ⟨hp.1.1.le, by simpa only [zero_add] using hp.1.2⟩
  calc
    (∑ i, ‖(hgraph i).toLp
        (n06CubicGraphFields (fun p => cylinderWeight p.1) U i)‖ ^ 2) =
        ∫ p, ∑ i, (n06CubicGraphFields (fun p => cylinderWeight p.1) U i p) ^ 2
          ∂cylinderWindowMeasure 0 := by
      simp_rw [r11b_norm_toLp_sq]
      exact (integral_finsetSum Finset.univ (fun i _ => (hgraph i).integrable_sq)).symm
    _ = ∫ p,
        cylinderWeight p.1 ^ 4 * radialPartial (radialPartial U) p ^ 2 +
        cylinderWeight p.1 ^ 5 * angularPartial (radialPartial U) p ^ 2 +
        cylinderWeight p.1 ^ 6 * angularPartial (angularPartial U) p ^ 2 +
        cylinderWeight p.1 ^ 2 * radialPartial U p ^ 2 +
        cylinderWeight p.1 ^ 3 * angularPartial U p ^ 2 ∂cylinderWindowMeasure 0 := by
      apply integral_congr_ae
      filter_upwards [hdAE] with p hdp
      exact n06CubicGraphFields_square_sum (fun p => cylinderWeight p.1) U p hdp
    _ = Real.pi * (n06CylinderSquare 4 (radialPartial (radialPartial U)) +
        n06CylinderSquare 5 (angularPartial (radialPartial U)) +
        n06CylinderSquare 6 (angularPartial (angularPartial U)) +
        n06CylinderSquare 2 (radialPartial U) + n06CylinderSquare 3 (angularPartial U)) := by
      have hI3 := integral_add (((hi4.add hi5).add hi6).add hi2) hi3
      have hI2 := integral_add ((hi4.add hi5).add hi6) hi2
      have hI6 := integral_add (hi4.add hi5) hi6
      have hI5 := integral_add hi4 hi5
      simp only [Pi.add_apply] at hI3 hI2 hI6 hI5
      rw [hI3, hI2, hI6, hI5,
        n06_weighted_integral_eq_pi_mul_square 4 _ hrr.continuous hprr,
        n06_weighted_integral_eq_pi_mul_square 5 _ hrt.continuous hprt,
        n06_weighted_integral_eq_pi_mul_square 6 _ htt.continuous hptt,
        n06_weighted_integral_eq_pi_mul_square 2 _ hr.continuous hpr,
        n06_weighted_integral_eq_pi_mul_square 3 _ ht.continuous hpt]
      ring
    _ ≤ Real.pi * n06CylinderGraphSquare U := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      unfold n06CylinderGraphSquare
      linarith [n06CylinderSquare_nonneg 3 U, n06CylinderSquare_nonneg 6 U,
        n06CylinderSquare_nonneg 6 (angularPartial U),
        n06CylinderSquare_nonneg 5 (radialPartial U)]

/-- The normalized scalar estimate bounds the actual five L² graph fields
of every finite even Fourier solution, including arbitrary radial boundary values. -/
theorem n06_even_cylinder_graph_lp_bound
    (s : Finset ℕ) (u F : ℕ → ℝ → ℝ)
    {a c V q : ℝ → ℝ} {K : ℝ}
    (ha : ContDiff ℝ 1 a) (hu : ∀ i ∈ s, ContDiff ℝ ∞ (u i))
    (hc : Continuous c) (hV : Continuous V) (hq : ContDiff ℝ 2 q)
    (hF : ∀ i ∈ s, ∀ y, F i y =
      -deriv (fun t => a t * deriv (u i) t) y +
        ((2 * i : ℕ) : ℝ) ^ 2 * c y * u i y + V y * u i y)
    (hK : 1 ≤ K)
    (ha₁ : ∀ y ∈ Icc (0 : ℝ) 1, 1 / K ≤ a y)
    (ha₂ : ∀ y ∈ Icc (0 : ℝ) 1, a y ≤ K)
    (ha₃ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv a y| ≤ K)
    (hc₁ : ∀ y ∈ Icc (0 : ℝ) 1, cylinderWeight y / K ≤ c y)
    (hV₁ : ∀ y ∈ Icc (0 : ℝ) 1, |V y| ≤ K)
    (hqa : ∀ y ∈ Icc (0 : ℝ) 1, c y = a y * q y)
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) 1, |deriv (deriv q) y| ≤ K) :
    let U := r11bFiniteSynthesis s u referenceAngularBasis
    let G := r11bFiniteSynthesis s F referenceAngularBasis
    ∃ hULp : MemLp U 2 (cylinderWindowMeasure 0),
    ∃ hGLp : MemLp G 2 (cylinderWindowMeasure 0),
    ∃ hgraph : ∀ i, MemLp (n06CubicGraphFields (fun p => cylinderWeight p.1) U i) 2
      (cylinderWindowMeasure 0),
      (∑ i, ‖(hgraph i).toLp
        (n06CubicGraphFields (fun p => cylinderWeight p.1) U i)‖ ^ 2) ≤
          16384 * K ^ 10 * (‖hGLp.toLp G‖ ^ 2 + ‖hULp.toLp U‖ ^ 2) := by
  let U := r11bFiniteSynthesis s u referenceAngularBasis
  let G := r11bFiniteSynthesis s F referenceAngularBasis
  have hU : ContDiff ℝ ∞ U := n06_contDiff_finiteSynthesis s u referenceAngularBasis hu
    (fun i _ => contDiff_referenceAngularBasis i)
  have hFc (i : ℕ) (hi : i ∈ s) : Continuous (F i) :=
    continuous_forcing ha ((hu i hi).of_le (by simp)) hc hV (hF i hi)
  have hG : Continuous G :=
    continuous_finsetSum s (fun i hi => ((hFc i hi).comp continuous_fst).mul
      ((contDiff_referenceAngularBasis i).continuous.comp continuous_snd))
  have hper (v : ℕ → ℝ → ℝ) :
      Function.Periodic (r11bFiniteSynthesis s v referenceAngularBasis) (0, Real.pi) := by
    intro p
    apply Finset.sum_congr rfl
    intro i _
    simp only [Prod.fst_add, Prod.snd_add, add_zero, referenceAngularBasis_periodic i p.2]
  let hULp := continuous_memLp_cylinderWindow hU.continuous 0
  let hGLp := continuous_memLp_cylinderWindow hG 0
  let hgraph := n06_cubicGraphFields_memLp hU
  refine ⟨hULp, hGLp, hgraph, ?_⟩
  have hgraphBound := n06_even_cylinder_graph_bound s u F ha hu hc hV hq hF
    hK ha₁ ha₂ ha₃ hc₁ hV₁ hqa hq₂
  have hUnorm : ‖hULp.toLp U‖ ^ 2 = Real.pi * n06CylinderSquare 0 U := by
    rw [r11b_norm_toLp_sq]
    simpa only [pow_zero, one_mul] using
      n06_weighted_integral_eq_pi_mul_square 0 U hU.continuous (hper u)
  have hGnorm : ‖hGLp.toLp G‖ ^ 2 = Real.pi * n06CylinderSquare 0 G := by
    rw [r11b_norm_toLp_sq]
    simpa only [pow_zero, one_mul] using
      n06_weighted_integral_eq_pi_mul_square 0 G hG (hper F)
  calc
    _ ≤ Real.pi * n06CylinderGraphSquare U :=
      n06_cubicGraphFields_norm_sq_le_graph hU (hper u) hgraph
    _ ≤ Real.pi * (16384 * K ^ 10 *
        (n06CylinderSquare 0 G + n06CylinderSquare 0 U)) :=
      mul_le_mul_of_nonneg_left hgraphBound Real.pi_pos.le
    _ = 16384 * K ^ 10 * (‖hGLp.toLp G‖ ^ 2 + ‖hULp.toLp U‖ ^ 2) := by
      rw [hUnorm, hGnorm]
      ring

end ContinuousFlexibility.Analysis
