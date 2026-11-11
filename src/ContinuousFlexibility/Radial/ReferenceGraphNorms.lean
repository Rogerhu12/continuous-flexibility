import ContinuousFlexibility.Radial.R11bGlobalL2
import ContinuousFlexibility.Radial.ReferenceCellAlgebra

/-!
# Physical square bounds for the reference graph norms

Positive attenuation controls the ordinary physical L² norm.  The output
estimate includes the actual left constant and its fixed cutoff.  These
bounds make distributional testing continuous in the frozen graph norms.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter Real
open scoped Topology RealInnerProductSpace
open ContinuousFlexibility.Statements

theorem referenceSource_physical_square_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : RadialSource, SourceMember D γ M F →
      F.2 ^ 2 + (∫ x, F.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
        C * sourceNormSquare D γ M F := by
  obtain ⟨_, hgeom, hpart, _⟩ := hD
  obtain ⟨K, hK, hbound⟩ :=
    r11b_cell_weighted_L2_bound hpart hgeom.2.1.le (2 * M) γ hγ
  refine ⟨K + 1, by linarith, fun F hF => ?_⟩
  have hI := (hbound F.1 hF.1 hF.2.1).2
  have hs : 0 ≤ ∑' m, sourceCellSquare D γ M F.1 m :=
    tsum_nonneg (fun m => sourceCellSquare_nonneg hgeom.2.1.le γ M hF.1 m)
  change F.2 ^ 2 + (∫ x, F.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
    (K + 1) * (F.2 ^ 2 + ∑' m, sourceCellSquare D γ M F.1 m)
  change (∫ x, F.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
    K * ∑' m, sourceCellSquare D γ M F.1 m at hI
  nlinarith [sq_nonneg F.2, mul_nonneg hK.le (sq_nonneg F.2)]

theorem referenceOutput_physical_square_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ : ℝ} (hγ : 0 < γ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (aL : ℝ) (U : RadialUnknown),
      OutputRealization D γ M aL U →
      U.2 ^ 2 + (∫ x, U.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
        C * outputNormSquare D γ M aL U := by
  obtain ⟨Cgeom, hgeom, hpart, hrest⟩ := hD
  have hD : IsAccumulatingProfile D := ⟨Cgeom, hgeom, hpart, hrest⟩
  obtain ⟨K, hK, hbound⟩ :=
    r11b_cell_weighted_L2_bound hpart hgeom.2.1.le (-2 * M) γ hγ
  let q : ℝ := ∫ x, (D.chiLeft x.1) ^ 2 ∂radialPhysicalMeasure D
  have hq : 0 ≤ q := integral_nonneg (fun _ => sq_nonneg _)
  have hcut : MemLp (fun x : PolarPoint => D.chiLeft x.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (hborder.2.2.2.2.1.continuous.comp continuous_fst)
  refine ⟨2 * K + 2 * q + 1, by positivity, fun aL U hU => ?_⟩
  have hrem := (hbound (outputRemainder D aL U) hU.1 hU.2.1).1
  have hremBound := (hbound (outputRemainder D aL U) hU.1 hU.2.1).2
  have hleft : MemLp (fun x : PolarPoint => aL * D.chiLeft x.1) 2
      (radialPhysicalMeasure D) := hcut.const_mul aL
  have hu := r11b_output_memLp hD hborder hγ (show OutputMember D γ M U from ⟨aL, hU⟩)
  have hleftSquare :
      (∫ x, (aL * D.chiLeft x.1) ^ 2 ∂radialPhysicalMeasure D) = aL ^ 2 * q := by
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hsplit :
      (∫ x, U.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
        2 * (∫ x, outputRemainder D aL U x ^ 2 ∂radialPhysicalMeasure D) +
          2 * aL ^ 2 * q := by
    calc
      (∫ x, U.1 x ^ 2 ∂radialPhysicalMeasure D)
          ≤ ∫ x, 2 * outputRemainder D aL U x ^ 2 +
              2 * (aL * D.chiLeft x.1) ^ 2 ∂radialPhysicalMeasure D := by
            apply integral_mono hu.integrable_sq
              ((hrem.integrable_sq.const_mul 2).add (hleft.integrable_sq.const_mul 2))
            intro x
            dsimp only [outputRemainder]
            nlinarith [sq_nonneg (U.1 x - 2 * (aL * D.chiLeft x.1))]
      _ = _ := by
        rw [integral_add (hrem.integrable_sq.const_mul 2)
          (hleft.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul,
          hleftSquare]
        ring
  have hs : 0 ≤ ∑' m, outputCellSquare D γ M (outputRemainder D aL U) m :=
    tsum_nonneg (fun m => outputCellSquare_nonneg hgeom.2.1.le γ M hU.1 m)
  change (∫ x, outputRemainder D aL U x ^ 2 ∂radialPhysicalMeasure D) ≤
    K * ∑' m, outputCellSquare D γ M (outputRemainder D aL U) m at hremBound
  change U.2 ^ 2 + (∫ x, U.1 x ^ 2 ∂radialPhysicalMeasure D) ≤
    (2 * K + 2 * q + 1) *
      (aL ^ 2 + U.2 ^ 2 + ∑' m, outputCellSquare D γ M (outputRemainder D aL U) m)
  nlinarith [sq_nonneg aL, sq_nonneg U.2,
    mul_nonneg hK.le (sq_nonneg aL), mul_nonneg hK.le (sq_nonneg U.2),
    mul_nonneg hq (sq_nonneg U.2), mul_nonneg hq hs]

/-- Pairings of actual L² representatives are the genuine scalar integrals. -/
theorem reference_memLp_inner_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

theorem reference_memLp_norm_sq_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, reference_memLp_inner_eq_integral hf hf]
  congr 1
  funext x
  ring

/-- Square-integral convergence gives convergence of the actual Hilbert
representatives, independently of the choice of their a.e. values. -/
theorem reference_memLp_tendsto_of_sub_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have heq (n : ℕ) :
      ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 =
        ∫ x, (f n x - g x) ^ 2 ∂μ := by
    have he : (hf n).toLp (f n) - hg.toLp g =
        ((hf n).sub hg).toLp (fun x => f n x - g x) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
        (hf n).coeFn_toLp, hg.coeFn_toLp, ((hf n).sub hg).coeFn_toLp]
        with x hsub hfn hgn hdiff
      rw [hsub, hfn, hgn, hdiff]
    rw [he, reference_memLp_norm_sq_eq_integral]
  have hsq : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [heq] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq

theorem reference_memLp_pairing_tendsto_of_sub_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g k : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hk : MemLp k 2 μ)
    (h : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * k x ∂μ) atTop (𝓝 (∫ x, g x * k x ∂μ)) := by
  have ht := (reference_memLp_tendsto_of_sub_sq hf hg h).inner
    (tendsto_const_nhds (x := hk.toLp k))
  simpa only [reference_memLp_inner_eq_integral] using ht


theorem referenceSource_sub {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {γ M : ℝ} {F K : RadialSource}
    (hF : SourceMember D γ M F) (hK : SourceMember D γ M K) :
    SourceMember D γ M (F - K) := by
  obtain ⟨_, hgeom, hpart, _⟩ := hD
  simpa only [neg_one_smul, sub_eq_add_neg] using
    hF.add hgeom.2.1.le hpart (hK.smul (-1))

theorem referenceSource_sub_sq_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : ℕ → RadialSource} {K : RadialSource}
    (hF : ∀ n, SourceMember D γ M (F n)) (hK : SourceMember D γ M K)
    (h : Tendsto (fun n => sourceNormSquare D γ M (F n - K)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ((F n).1 x - K.1 x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := referenceSource_physical_square_bound hD hγ M
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
  · intro n
    have hb := hbound (F n - K) (referenceSource_sub hD (hF n) hK)
    change ((F n).2 - K.2) ^ 2 +
      (∫ x, ((F n).1 x - K.1 x) ^ 2 ∂radialPhysicalMeasure D) ≤
        C * sourceNormSquare D γ M (F n - K) at hb
    linarith [sq_nonneg ((F n).2 - K.2)]
  · simpa only [mul_zero] using h.const_mul C

theorem referenceOutput_sub_sq_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : ℕ → RadialUnknown} {V : RadialUnknown}
    {a : ℕ → ℝ} (hU : ∀ n, OutputRealization D γ M (a n) (U n - V))
    (h : Tendsto (fun n => outputNormSquare D γ M (a n) (U n - V))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ((U n).1 x - V.1 x) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := referenceOutput_physical_square_bound hD hborder hγ M
  apply squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _))
  · intro n
    have hb := hbound (a n) (U n - V) (hU n)
    change ((U n).2 - V.2) ^ 2 +
      (∫ x, ((U n).1 x - V.1 x) ^ 2 ∂radialPhysicalMeasure D) ≤
        C * outputNormSquare D γ M (a n) (U n - V) at hb
    linarith [sq_nonneg ((U n).2 - V.2)]
  · simpa only [mul_zero] using h.const_mul C

theorem referenceSource_scalar_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {γ M : ℝ} (hγ : 0 < γ)
    {F : ℕ → RadialSource} {K : RadialSource}
    (hF : ∀ n, SourceMember D γ M (F n)) (hK : SourceMember D γ M K)
    (h : Tendsto (fun n => sourceNormSquare D γ M (F n - K)) atTop (𝓝 0)) :
    Tendsto (fun n => (F n).2) atTop (𝓝 K.2) := by
  obtain ⟨C, _, hbound⟩ := referenceSource_physical_square_bound hD hγ M
  have hs : Tendsto (fun n => ((F n).2 - K.2) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
    · intro n
      have hb := hbound (F n - K) (referenceSource_sub hD (hF n) hK)
      have hi : 0 ≤ ∫ x, ((F n).1 x - K.1 x) ^ 2 ∂radialPhysicalMeasure D :=
        integral_nonneg (fun _ => sq_nonneg _)
      change ((F n).2 - K.2) ^ 2 +
        (∫ x, ((F n).1 x - K.1 x) ^ 2 ∂radialPhysicalMeasure D) ≤
          C * sourceNormSquare D γ M (F n - K) at hb
      linarith
    · simpa only [mul_zero] using h.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs

theorem referenceOutput_scalar_tendsto {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {γ M : ℝ} (hγ : 0 < γ) {U : ℕ → RadialUnknown} {V : RadialUnknown}
    {a : ℕ → ℝ} (hU : ∀ n, OutputRealization D γ M (a n) (U n - V))
    (h : Tendsto (fun n => outputNormSquare D γ M (a n) (U n - V))
      atTop (𝓝 0)) :
    Tendsto (fun n => (U n).2) atTop (𝓝 V.2) := by
  obtain ⟨C, _, hbound⟩ := referenceOutput_physical_square_bound hD hborder hγ M
  have hs : Tendsto (fun n => ((U n).2 - V.2) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
    · intro n
      have hb := hbound (a n) (U n - V) (hU n)
      have hi : 0 ≤ ∫ x, ((U n).1 x - V.1 x) ^ 2 ∂radialPhysicalMeasure D :=
        integral_nonneg (fun _ => sq_nonneg _)
      change ((U n).2 - V.2) ^ 2 +
        (∫ x, ((U n).1 x - V.1 x) ^ 2 ∂radialPhysicalMeasure D) ≤
          C * outputNormSquare D γ M (a n) (U n - V) at hb
      linarith
    · simpa only [mul_zero] using h.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs

end ContinuousFlexibility.Radial
