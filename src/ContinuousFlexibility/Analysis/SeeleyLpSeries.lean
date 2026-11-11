import ContinuousFlexibility.Analysis.SeeleyLpBounds
import ContinuousFlexibility.Analysis.SeeleyJetExtension
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.NormNum

/-!
# Summable L² reflection series and the full extension estimate

The L² sum agrees almost everywhere with the pointwise series in
`seeleyReflection`. Consequently all estimates below apply to the actual
extension formula. No pointwise boundedness or differentiability assumption is
needed for these estimates; those properties enter only when identifying the
extension's derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {ι F : Type*} [Countable ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Absolute summability of actual L² norms identifies the L² sum with the
pointwise series and gives Minkowski's bound for that series. -/
theorem memLp_tsum_and_eLpNorm_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u : ι → X → F} (hu : ∀ i, MemLp (u i) 2 μ)
    (hsum : (∑' i, eLpNorm (u i) 2 μ) ≠ ∞) :
    MemLp (fun x => ∑' i, u i x) 2 μ ∧
      eLpNorm (fun x => ∑' i, u i x) 2 μ ≤ ∑' i, eLpNorm (u i) 2 μ := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let g : ι → Lp F 2 μ := fun i => (hu i).toLp (u i)
  have hnorm (i : ι) : ‖g i‖ₑ = eLpNorm (u i) 2 μ := Lp.enorm_toLp (hu i)
  have hnormsum : (∑' i, ‖g i‖ₑ) = ∑' i, eLpNorm (u i) 2 μ := tsum_congr hnorm
  have hg : (∑' i, ‖g i‖ₑ) ≠ ∞ := by rwa [hnormsum]
  have hterm : ∀ᵐ x ∂μ, ∀ i, g i x = u i x :=
    ae_all_iff.mpr (fun i => MemLp.coeFn_toLp (hu i))
  have hrep : ⇑(∑' i, g i) =ᵐ[μ] fun x => ∑' i, u i x := by
    filter_upwards [Lp.coeFn_tsum hg, hterm] with x hx hxi
    exact hx.trans (tsum_congr (fun i => hxi i))
  refine ⟨(memLp_congr_ae hrep).mp (Lp.memLp _), ?_⟩
  calc
    eLpNorm (fun x => ∑' i, u i x) 2 μ = eLpNorm (⇑(∑' i, g i)) 2 μ :=
      (eLpNorm_congr_ae hrep).symm
    _ = ‖∑' i, g i‖ₑ := (Lp.enorm_def _).symm
    _ ≤ ∑' i, ‖g i‖ₑ := enorm_tsum_le_tsum_enorm
    _ = ∑' i, eLpNorm (u i) 2 μ := hnormsum

theorem seeleyMomentNorm_nonneg (S : SeeleyData ι) (n : ℕ) :
    0 ≤ ∑' i, |S.a i| * S.b i ^ n :=
  tsum_nonneg (fun i => mul_nonneg (abs_nonneg _) (pow_nonneg (S.b_nonneg i) n))

private theorem seeleyReflection_memLp_bound (S : SeeleyData ι) (n : ℕ)
    {f : ℝ → F} (hf : MemLp f 2 (volume.restrict (Ici 0))) :
    MemLp (seeleyReflection S n f) 2 (volume.restrict (Iio 0)) ∧
      eLpNorm (seeleyReflection S n f) 2 (volume.restrict (Iio 0)) ≤
        ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
          eLpNorm f 2 (volume.restrict (Ici 0)) := by
  have hterm (i : ι) : MemLp (fun x =>
      (S.a i * (-S.b i) ^ n) • f (-S.b i * x)) 2 (volume.restrict (Iio 0)) := by
    simpa only [Pi.smul_apply] using
      (memLp_neg_mul_Iio hf (S.one_le_b i)).const_smul (S.a i * (-S.b i) ^ n)
  have hnorm (i : ι) :
      eLpNorm (fun x => (S.a i * (-S.b i) ^ n) • f (-S.b i * x))
          2 (volume.restrict (Iio 0)) ≤
        ENNReal.ofReal (|S.a i| * S.b i ^ n) *
          eLpNorm f 2 (volume.restrict (Ici 0)) := by
    calc
      eLpNorm (fun x => (S.a i * (-S.b i) ^ n) • f (-S.b i * x))
          2 (volume.restrict (Iio 0)) =
          ‖S.a i * (-S.b i) ^ n‖ₑ *
            eLpNorm (fun x => f (-S.b i * x)) 2 (volume.restrict (Iio 0)) := by
        simpa only [Pi.smul_apply] using eLpNorm_const_smul
          (S.a i * (-S.b i) ^ n) (fun x => f (-S.b i * x)) 2
          (volume.restrict (Iio 0))
      _ = ENNReal.ofReal (|S.a i| * S.b i ^ n) *
          eLpNorm (fun x => f (-S.b i * x)) 2 (volume.restrict (Iio 0)) := by
        rw [← ofReal_norm, norm_seeley_coefficient]
      _ ≤ ENNReal.ofReal (|S.a i| * S.b i ^ n) *
          eLpNorm f 2 (volume.restrict (Ici 0)) :=
        mul_le_mul_right (eLpNorm_neg_mul_Iio_le f 2 (S.one_le_b i)) _
  have hsum : (∑' i, eLpNorm
      (fun x => (S.a i * (-S.b i) ^ n) • f (-S.b i * x))
      2 (volume.restrict (Iio 0))) ≤
      ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
        eLpNorm f 2 (volume.restrict (Ici 0)) := by
    calc
      _ ≤ ∑' i, ENNReal.ofReal (|S.a i| * S.b i ^ n) *
          eLpNorm f 2 (volume.restrict (Ici 0)) := ENNReal.tsum_le_tsum hnorm
      _ = ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
          eLpNorm f 2 (volume.restrict (Ici 0)) := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
          (fun i => mul_nonneg (abs_nonneg _) (pow_nonneg (S.b_nonneg i) n))
          (S.summable_moment n)]
  have hfinite : (∑' i, eLpNorm
      (fun x => (S.a i * (-S.b i) ^ n) • f (-S.b i * x))
      2 (volume.restrict (Iio 0))) ≠ ∞ :=
    (hsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.mp hf))).ne
  obtain ⟨hm, hn⟩ := memLp_tsum_and_eLpNorm_le (volume.restrict (Iio 0)) hterm hfinite
  exact ⟨hm, hn.trans hsum⟩

theorem memLp_seeleyReflection (S : SeeleyData ι) (n : ℕ) {f : ℝ → F}
    (hf : MemLp f 2 (volume.restrict (Ici 0))) :
    MemLp (seeleyReflection S n f) 2 (volume.restrict (Iio 0)) :=
  (seeleyReflection_memLp_bound S n hf).1

theorem eLpNorm_seeleyReflection_le (S : SeeleyData ι) (n : ℕ) {f : ℝ → F}
    (hf : MemLp f 2 (volume.restrict (Ici 0))) :
    eLpNorm (seeleyReflection S n f) 2 (volume.restrict (Iio 0)) ≤
      ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
        eLpNorm f 2 (volume.restrict (Ici 0)) :=
  (seeleyReflection_memLp_bound S n hf).2

theorem norm_seeleyReflection_le (S : SeeleyData ι) (n : ℕ) {f : ℝ → F}
    (hf : MemLp f 2 (volume.restrict (Ici 0))) :
    (eLpNorm (seeleyReflection S n f) 2 (volume.restrict (Iio 0))).toReal ≤
      (∑' i, |S.a i| * S.b i ^ n) *
        (eLpNorm f 2 (volume.restrict (Ici 0))).toReal := by
  have hfinite : ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
      eLpNorm f 2 (volume.restrict (Ici 0)) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.mp hf)).ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (seeleyMomentNorm_nonneg S n)]
    using ENNReal.toReal_mono hfinite (eLpNorm_seeleyReflection_le S n hf)

/-- The two measurable half-lines give the actual global extension jet. -/
theorem seeleyExtensionJet_eq_indicators (S : SeeleyData ι) (J : ℕ → ℝ → F) (n : ℕ) :
    seeleyExtensionJet S J n = (Ici 0).indicator (J n) +
      (Iio 0).indicator (seeleyReflection S n (J n)) := by
  funext x
  by_cases hx : 0 ≤ x
  · simp only [seeleyExtensionJet_of_nonneg S J n hx, Pi.add_apply,
      indicator_of_mem hx, indicator_of_notMem (not_lt.mpr hx), add_zero]
  · have hneg : x < 0 := lt_of_not_ge hx
    simp only [seeleyExtensionJet_of_neg S J n hneg, Pi.add_apply,
      indicator_of_notMem hx, indicator_of_mem hneg, zero_add]

theorem eLpNorm_seeleyExtensionJet_le (S : SeeleyData ι) (J : ℕ → ℝ → F) (n : ℕ)
    (hf : MemLp (J n) 2 (volume.restrict (Ici 0))) :
    eLpNorm (seeleyExtensionJet S J n) 2 volume ≤
      ENNReal.ofReal (1 + ∑' i, |S.a i| * S.b i ^ n) *
        eLpNorm (J n) 2 (volume.restrict (Ici 0)) := by
  rw [seeleyExtensionJet_eq_indicators]
  calc
    _ ≤ eLpNorm ((Ici 0).indicator (J n)) 2 volume +
        eLpNorm ((Iio 0).indicator (seeleyReflection S n (J n))) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ = eLpNorm (J n) 2 (volume.restrict (Ici 0)) +
        eLpNorm (seeleyReflection S n (J n)) 2 (volume.restrict (Iio 0)) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici,
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iio]
    _ ≤ eLpNorm (J n) 2 (volume.restrict (Ici 0)) +
        ENNReal.ofReal (∑' i, |S.a i| * S.b i ^ n) *
          eLpNorm (J n) 2 (volume.restrict (Ici 0)) :=
      add_le_add le_rfl (eLpNorm_seeleyReflection_le S n hf)
    _ = ENNReal.ofReal (1 + ∑' i, |S.a i| * S.b i ^ n) *
        eLpNorm (J n) 2 (volume.restrict (Ici 0)) := by
      rw [ENNReal.ofReal_add zero_le_one (seeleyMomentNorm_nonneg S n),
        ENNReal.ofReal_one, add_mul, one_mul]

theorem memLp_seeleyExtensionJet (S : SeeleyData ι) (J : ℕ → ℝ → F) (n : ℕ)
    (hf : MemLp (J n) 2 (volume.restrict (Ici 0))) :
    MemLp (seeleyExtensionJet S J n) 2 volume :=
  memLp_iff.mpr ((eLpNorm_seeleyExtensionJet_le S J n hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.mp hf)))

/-- A finite real bound for the full extension jet, with the same coefficients
at every order and no assumption that the input jet is already extended. -/
theorem norm_seeleyExtensionJet_le (S : SeeleyData ι) (J : ℕ → ℝ → F) (n : ℕ)
    (hf : MemLp (J n) 2 (volume.restrict (Ici 0))) :
    (eLpNorm (seeleyExtensionJet S J n) 2 volume).toReal ≤
      (1 + ∑' i, |S.a i| * S.b i ^ n) *
        (eLpNorm (J n) 2 (volume.restrict (Ici 0))).toReal := by
  have hfinite : ENNReal.ofReal (1 + ∑' i, |S.a i| * S.b i ^ n) *
      eLpNorm (J n) 2 (volume.restrict (Ici 0)) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.mp hf)).ne
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (add_nonneg zero_le_one (seeleyMomentNorm_nonneg S n))]
    using ENNReal.toReal_mono hfinite (eLpNorm_seeleyExtensionJet_le S J n hf)

end ContinuousFlexibility.Analysis
