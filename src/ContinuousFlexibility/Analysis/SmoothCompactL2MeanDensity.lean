module

public import ContinuousFlexibility.Analysis.SmoothCompactL2Density
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth approximation with an additional integral

A function in L² of one measure and L¹ of a finite second measure can be
approximated both in the L² norm and in its integral. Bounded truncation
allows smooth approximation for the sum measure. This is useful when a
source has an exact ordinary-integral compatibility condition but its
Hilbert norm uses a singular weight.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem norm_toLp_sq_eq_integral_sq {μ : Measure E} {f : E → ℝ}
    (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, pow_two]

theorem norm_toLp_mono_measure {μ ν : Measure E} (hμν : μ ≤ ν)
    {f : E → ℝ} (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν) :
    ‖hμ.toLp f‖ ≤ ‖hν.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hν.eLpNorm_ne_top (eLpNorm_mono_measure f hμν)

/-- The norm of the ordinary integral functional on a finite-measure L²
space, without needing an explicit square-root formula for the mass. -/
theorem abs_integral_le_L2_one_norm {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : MemLp f 2 μ) :
    |∫ x, f x ∂μ| ≤ ‖(memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : E => 1)‖ *
      ‖hf.toLp f‖ := by
  let h1 : MemLp (fun _ : E => (1 : ℝ)) 2 μ := memLp_const 1
  have heq : (∫ x, f x ∂μ) = inner ℝ (h1.toLp (fun _ => 1)) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [h1.coeFn_toLp, hf.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, hx, hy, one_mul]
  rw [heq]
  exact abs_real_inner_le_norm _ _

private def boundedTruncation (n : ℕ) (t : ℝ) : ℝ :=
  max (-(n : ℝ)) (min (n : ℝ) t)

private theorem boundedTruncation_eq {n : ℕ} {t : ℝ}
    (ht : |t| ≤ (n : ℝ)) : boundedTruncation n t = t := by
  have h := abs_le.mp ht
  simp only [boundedTruncation, min_eq_right h.2, max_eq_right h.1]

private theorem boundedTruncation_bounds (n : ℕ) (t : ℝ) :
    |boundedTruncation n t| ≤ (n : ℝ) ∧
      |boundedTruncation n t| ≤ |t| ∧
      |boundedTruncation n t - t| ≤ |t| := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hlo : t ≤ -(n : ℝ)
  · have ht : t ≤ 0 := hlo.trans (neg_nonpos.mpr hn)
    have hval : boundedTruncation n t = -(n : ℝ) := by
      rw [boundedTruncation, min_eq_right (hlo.trans (by linarith)), max_eq_left hlo]
    rw [hval, abs_neg, abs_of_nonneg hn, abs_of_nonpos ht,
      abs_of_nonneg (by linarith : 0 ≤ -(n : ℝ) - t)]
    exact ⟨le_rfl, by linarith, by linarith⟩
  · by_cases hhi : (n : ℝ) ≤ t
    · have ht : 0 ≤ t := hn.trans hhi
      have hval : boundedTruncation n t = (n : ℝ) := by
        rw [boundedTruncation, min_eq_left hhi, max_eq_right (by linarith)]
      rw [hval, abs_of_nonneg hn, abs_of_nonneg ht,
        abs_of_nonpos (sub_nonpos.mpr hhi)]
      exact ⟨le_rfl, hhi, by linarith⟩
    · have habs : |t| ≤ (n : ℝ) := abs_le.mpr ⟨(not_le.mp hlo).le, (not_le.mp hhi).le⟩
      rw [boundedTruncation_eq habs, sub_self, abs_zero]
      exact ⟨habs, le_rfl, abs_nonneg t⟩

private theorem boundedTruncation_tendsto (t : ℝ) :
    Tendsto (fun n => boundedTruncation n t) atTop (𝓝 t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  have heq : (fun n => boundedTruncation n t) =ᶠ[atTop] fun _ => t := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact boundedTruncation_eq (hN.le.trans (by exact_mod_cast hn))
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

private theorem boundedTruncation_aestronglyMeasurable
    {μ : Measure E} {f : E → ℝ} (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (fun x => boundedTruncation n (f x)) μ :=
  aestronglyMeasurable_const.sup (aestronglyMeasurable_const.inf hf)

/-- Simultaneous approximation in a weighted Hilbert norm and an ordinary
integral. The second measure is only required to be finite. -/
theorem MemLp.exists_contDiff_compact_approximation_integral
    {μ ν : Measure E} [IsFiniteMeasure ν] {U : Set E} {f : E → ℝ}
    (hf : MemLp f 2 μ) (hfi : Integrable f ν)
    (hU : IsOpen U) (hcarryμ : ∀ᵐ x ∂μ, x ∈ U) (hcarryν : ∀ᵐ x ∂ν, x ∈ U)
    (hfinite : ∀ K : Set E, IsCompact K → K ⊆ U → μ K < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∃ hg : MemLp g 2 μ, ‖hg.toLp g - hf.toLp f‖ < ε ∧
        |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| < ε := by
  let fN (n : ℕ) (x : E) := boundedTruncation n (f x)
  have hNμ (n : ℕ) : MemLp (fN n) 2 μ :=
    hf.of_le (boundedTruncation_aestronglyMeasurable hf.aestronglyMeasurable n)
      (ae_of_all _ (fun x => (boundedTruncation_bounds n (f x)).2.1))
  have hNν (n : ℕ) : MemLp (fN n) 2 ν :=
    MemLp.of_bound (boundedTruncation_aestronglyMeasurable hfi.aestronglyMeasurable n) n
      (ae_of_all _ (fun x => (boundedTruncation_bounds n (f x)).1))
  have hNsum (n : ℕ) : MemLp (fN n) 2 (μ + ν) := by
    apply (memLp_two_iff_integrable_sq
      ((hNμ n).aestronglyMeasurable.add_measure (hNν n).aestronglyMeasurable)).mpr
    exact (hNμ n).integrable_sq.add_measure (hNν n).integrable_sq
  have hsq : Tendsto (fun n => ∫ x, (fN n x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (fN n x - f x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards with x
      simpa only [fN, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        ((boundedTruncation_tendsto (f x)).sub
          (tendsto_const_nhds (x := f x))).pow 2
    have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖(fN n x - f x) ^ 2‖ ≤ f x ^ 2 := by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq).mpr (boundedTruncation_bounds n (f x)).2.2
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence
        (F := fun n x => (fN n x - f x) ^ 2) (f := fun _ => (0 : ℝ))
        (fun x => f x ^ 2)
        (fun n => ((hNμ n).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
        hf.integrable_sq hdom hlim
  have hnorm : Tendsto (fun n => ‖(hNμ n).toLp (fN n) - hf.toLp f‖)
      atTop (𝓝 0) := by
    have hsq' : Tendsto (fun n => ‖(hNμ n).toLp (fN n) - hf.toLp f‖ ^ 2)
        atTop (𝓝 0) := by
      have heq (n : ℕ) : ‖(hNμ n).toLp (fN n) - hf.toLp f‖ ^ 2 =
          ∫ x, (fN n x - f x) ^ 2 ∂μ := by
        rw [← MemLp.toLp_sub]
        exact norm_toLp_sq_eq_integral_sq ((hNμ n).sub hf)
      simpa only [heq] using hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq'
  have hint : Tendsto (fun n => ∫ x, fN n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hNν n).aestronglyMeasurable) hfi.norm
      (fun n => ae_of_all _ (fun x => (boundedTruncation_bounds n (f x)).2.1))
      (ae_of_all _ (fun x => boundedTruncation_tendsto (f x)))
  have hinterr : Tendsto (fun n => |(∫ x, fN n x ∂ν) - ∫ x, f x ∂ν|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hint.sub (tendsto_const_nhds (x := ∫ x, f x ∂ν))).abs
  obtain ⟨n, hnμ, hnν⟩ := (((tendsto_order.1 hnorm).2 _ (half_pos hε)).and
    ((tendsto_order.1 hinterr).2 _ (half_pos hε))).exists
  let C : ℝ := ‖(memLp_const (μ := ν) (p := 2) (1 : ℝ)).toLp (fun _ : E => 1)‖
  have hC : 0 ≤ C := norm_nonneg _
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (C + 1) = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < C + 1 by positivity)]
  have hcarrysum : ∀ᵐ x ∂μ + ν, x ∈ U :=
    ae_add_measure_iff.mpr ⟨hcarryμ, hcarryν⟩
  have hfiniteSum (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) :
      (μ + ν) K < ⊤ := by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hfinite K hK hKU, measure_lt_top _ _⟩
  obtain ⟨g, hg, hgc, hgu, hgsum, hdist⟩ :=
    MemLp.exists_contDiff_compact_approximation (hNsum n) hU hcarrysum hfiniteSum hδ
  let hgμ : MemLp g 2 μ := hgsum.left_of_add_measure
  let hgν : MemLp g 2 ν := hgsum.right_of_add_measure
  have hdistμ : ‖hgμ.toLp g - (hNμ n).toLp (fN n)‖ < δ := by
    apply lt_of_le_of_lt _ hdist
    rw [← MemLp.toLp_sub, ← MemLp.toLp_sub]
    exact norm_toLp_mono_measure (Measure.le_add_right le_rfl)
      (hgμ.sub (hNμ n)) (hgsum.sub (hNsum n))
  have hdistν : ‖hgν.toLp g - (hNν n).toLp (fN n)‖ < δ := by
    apply lt_of_le_of_lt _ hdist
    rw [← MemLp.toLp_sub, ← MemLp.toLp_sub]
    exact norm_toLp_mono_measure (Measure.le_add_left le_rfl)
      (hgν.sub (hNν n)) (hgsum.sub (hNsum n))
  have hiμ : ‖hgμ.toLp g - (hNμ n).toLp (fN n)‖ < ε / 2 := by
    have hδle : δ ≤ ε / 2 := by nlinarith [mul_nonneg hδ.le hC]
    exact hdistμ.trans_le hδle
  have hiν : |(∫ x, g x ∂ν) - ∫ x, fN n x ∂ν| < ε / 2 := by
    have hgνi : Integrable g ν := memLp_one_iff_integrable.mp
      (hgν.mono_exponent (by norm_num))
    have hNνi : Integrable (fN n) ν := memLp_one_iff_integrable.mp
      ((hNν n).mono_exponent (by norm_num))
    rw [← integral_sub hgνi hNνi]
    have hbound := abs_integral_le_L2_one_norm (hgν.sub (hNν n))
    rw [MemLp.toLp_sub hgν (hNν n)] at hbound
    have hn0 : 0 ≤ ‖hgν.toLp g - (hNν n).toLp (fN n)‖ := norm_nonneg _
    change |∫ x, g x - fN n x ∂ν| ≤
      C * ‖hgν.toLp g - (hNν n).toLp (fN n)‖ at hbound
    have hmul := mul_le_mul_of_nonneg_left hdistν.le hC
    nlinarith
  refine ⟨g, hg, hgc, hgu, hgμ, ?_, ?_⟩
  · calc
      ‖hgμ.toLp g - hf.toLp f‖ ≤
          ‖hgμ.toLp g - (hNμ n).toLp (fN n)‖ +
            ‖(hNμ n).toLp (fN n) - hf.toLp f‖ := by
              simpa only [dist_eq_norm] using
                dist_triangle (hgμ.toLp g) ((hNμ n).toLp (fN n)) (hf.toLp f)
      _ < ε := by linarith
  · calc
      |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| ≤
          |(∫ x, g x ∂ν) - ∫ x, fN n x ∂ν| +
            |(∫ x, fN n x ∂ν) - ∫ x, f x ∂ν| := by
              simpa only [Real.dist_eq] using
                dist_triangle (∫ x, g x ∂ν) (∫ x, fN n x ∂ν) (∫ x, f x ∂ν)
      _ < ε := by linarith

end ContinuousFlexibility.Analysis
