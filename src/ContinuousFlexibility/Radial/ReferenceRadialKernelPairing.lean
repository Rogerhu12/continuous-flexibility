module

public import ContinuousFlexibility.Radial.ReferenceRadialMeasureComparison
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Pairing a kernel row with the actual weighted radial source

The partition gives the same null sets as ordinary Lebesgue measure on
the core. A cellwise bound on a measurable kernel row then controls its
product with any actual weighted L2 source, including the ordinary L2
norm and the integral. The comparison constant is chosen before the
weight parameters and before the kernel row.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real Filter MeasureTheory
open scoped ENNReal

theorem referenceRadialWeightedMeasure_ae_iff {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) {p : ℝ → Prop} :
    (∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, p r) ↔
      ∀ᵐ r ∂volume.restrict (radialCore D), p r := by
  rw [referenceRadialWeightedMeasure_eq_sum hD γ M]
  constructor
  · intro h
    have hcell := Measure.ae_sum_iff.mp h
    have hbase (m : ℕ) : ∀ᵐ r ∂volume.restrict (radialCore D),
        referenceRadialCellDensity D γ M m r ≠ 0 → p r :=
      (ae_withDensity_iff (referenceRadialCellDensity_measurable hD γ M m)).mp (hcell m)
    have hall : ∀ᵐ r ∂volume.restrict (radialCore D), ∀ m,
        referenceRadialCellDensity D γ M m r ≠ 0 → p r := ae_all_iff.2 hbase
    filter_upwards [hall, ae_restrict_mem measurableSet_Ioo] with r hr hrmem
    obtain ⟨m, hm⟩ := hD.exists_localizer_ne_zero hrmem
    apply hr m
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (exp_pos _) (sq_pos_of_ne_zero hm))
  · intro h
    apply Measure.ae_sum_iff.mpr
    intro m
    apply (ae_withDensity_iff (referenceRadialCellDensity_measurable hD γ M m)).mpr
    exact h.mono (fun _ hp _ => hp)

theorem radialCoreMeasure_absolutelyContinuous_weighted {D : ReferenceData}
    (hD : RadialPartition D) (γ M : ℝ) :
    volume.restrict (radialCore D) ≪ referenceRadialWeightedMeasure D γ M := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hnot : ∀ᵐ r ∂referenceRadialWeightedMeasure D γ M, r ∉ s := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hs0
  have hp := (referenceRadialWeightedMeasure_ae_iff hD γ M).mp hnot
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hp

/-- Ordinary integral Cauchy--Schwarz, in squared form, for an actual
L2 function on the finite reference interval. -/
theorem referenceRadial_integral_sq_le {D : ReferenceData}
    (hab : D.a < D.b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (radialCore D))) :
    (∫ r in radialCore D, g r) ^ 2 ≤
      (D.b - D.a) * ∫ r in radialCore D, g r ^ 2 := by
  letI : IsFiniteMeasure (volume.restrict (radialCore D)) := by
    change IsFiniteMeasure (volume.restrict (Ioo D.a D.b))
    infer_instance
  let μ : Measure ℝ := volume.restrict (radialCore D)
  letI : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  have hmass : μ.real univ = D.b - D.a := by
    simp only [μ, measureReal_def, Measure.restrict_apply_univ, radialCore,
      Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hL : 0 < D.b - D.a := sub_pos.mpr hab
  let I : ℝ := ∫ r, g r ∂μ
  let E : ℝ := ∫ r, g r ^ 2 ∂μ
  let c : ℝ := I / (D.b - D.a)
  have hc : c * (D.b - D.a) = I := div_mul_cancel₀ I hL.ne'
  have hi : Integrable g μ := hg.integrable (by norm_num)
  have hisq : Integrable (fun r => g r ^ 2) μ := hg.integrable_sq
  have hlin : Integrable (fun r => (2 * c) * g r) μ := hi.const_mul _
  have hconst : Integrable (fun _ : ℝ => c ^ 2) μ := integrable_const _
  have hsub : Integrable (fun r => g r ^ 2 - (2 * c) * g r) μ := hisq.sub hlin
  have hn : 0 ≤ ∫ r, (g r - c) ^ 2 ∂μ :=
    integral_nonneg (fun r => sq_nonneg (g r - c))
  have he : (∫ r, (g r - c) ^ 2 ∂μ) = E - (2 * c) * I + c ^ 2 * (D.b - D.a) := by
    calc
      _ = ∫ r, (g r ^ 2 - (2 * c) * g r) + c ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun r => by ring)
      _ = _ := by
        rw [integral_add (f := fun r => g r ^ 2 - (2 * c) * g r)
          (g := fun _ : ℝ => c ^ 2) hsub hconst,
          integral_sub (f := fun r => g r ^ 2) (g := fun r => (2 * c) * g r) hisq hlin,
          integral_const_mul, integral_const, hmass, smul_eq_mul]
        dsimp only [E, I]
        ring
  rw [he] at hn
  have hc₂ : c ^ 2 * (D.b - D.a) = c * I := by rw [← hc]; ring
  rw [hc₂] at hn
  have hIE : c * I ≤ E := by linarith only [hn]
  change I ^ 2 ≤ (D.b - D.a) * E
  calc
    I ^ 2 = (D.b - D.a) * (c * I) := by rw [← hc]; ring
    _ ≤ (D.b - D.a) * E := mul_le_mul_of_nonneg_left hIE hL.le

/-- The same constant works for all source weights and all measurable
kernel rows with the displayed cellwise bound. -/
theorem referenceRadial_kernel_pairing {D : ReferenceData}
    (hab : D.a < D.b) (hD : RadialPartition D) :
    ∃ B : ℝ, 0 < B ∧ ∀ γ M K : ℝ, ∀ k f : ℝ → ℝ,
      0 ≤ K → Measurable k →
      MemLp f 2 (referenceRadialWeightedMeasure D γ M) →
      (∀ m : ℕ, ∀ r ∈ D.cells m,
        |k r| ≤ K * exp (M * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m))) →
      MemLp (fun r => k r * f r) 2 (volume.restrict (radialCore D)) ∧
      (∫ r in radialCore D, (k r * f r) ^ 2) ≤
        (K ^ 2 * B) * ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M ∧
      (∫ r in radialCore D, k r * f r) ^ 2 ≤
        ((D.b - D.a) * (K ^ 2 * B)) *
          ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M := by
  obtain ⟨B, hB, hcompare⟩ := referenceRadial_withDensity_le_weighted hD
  refine ⟨B, hB, ?_⟩
  intro γ M K k f hK hk hf hcell
  let σ (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((k r) ^ 2)
  have hσ : Measurable σ := (hk.pow_const 2).ennreal_ofReal
  have hσtop : ∀ᵐ r ∂volume.restrict (radialCore D), σ r < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hcell₂ (m : ℕ) (r : ℝ) (hr : r ∈ D.cells m) :
      (k r) ^ 2 ≤ K ^ 2 *
        exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
    have h := (sq_le_sq₀ (abs_nonneg (k r))
      (mul_nonneg hK (exp_pos _).le)).2 (hcell m r hr)
    have he : exp (M * radialQ (D.cellIndex m) + γ * radialS (D.cellIndex m)) ^ 2 =
        exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) := by
      rw [pow_two, ← exp_add]
      congr 1 <;> ring
    simpa only [sq_abs, mul_pow, he] using h
  have hmeasure :
      (volume.restrict (radialCore D)).withDensity σ ≤
        ENNReal.ofReal (K ^ 2 * B) • referenceRadialWeightedMeasure D γ M :=
    hcompare γ M (K ^ 2) (fun r => (k r) ^ 2) (sq_nonneg K)
      (fun _ _ => sq_nonneg _) hcell₂
  have hfσ : MemLp f 2 ((volume.restrict (radialCore D)).withDensity σ) :=
    hf.of_measure_le_smul ENNReal.ofReal_ne_top hmeasure
  have hfm : AEStronglyMeasurable f (volume.restrict (radialCore D)) :=
    hf.aestronglyMeasurable.mono_ac (radialCoreMeasure_absolutelyContinuous_weighted hD γ M)
  have hkm : AEStronglyMeasurable (fun r => k r * f r)
      (volume.restrict (radialCore D)) := hk.aestronglyMeasurable.mul hfm
  have hisq := (integrable_withDensity_iff_integrable_smul' hσ hσtop).mp hfσ.integrable_sq
  have hmul : MemLp (fun r => k r * f r) 2 (volume.restrict (radialCore D)) := by
    apply (memLp_two_iff_integrable_sq hkm).mpr
    apply hisq.congr
    exact ae_of_all _ (fun r => by
      simp only [σ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_pow])
  have hidentity :
      (∫ r, f r ^ 2 ∂(volume.restrict (radialCore D)).withDensity σ) =
        ∫ r in radialCore D, (k r * f r) ^ 2 := by
    rw [integral_withDensity_eq_integral_toReal_smul hσ hσtop]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by
      simp only [σ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_pow])
  have hbound := integral_mono_measure hmeasure
    (ae_of_all _ (fun r => sq_nonneg (f r)))
    (hf.integrable_sq.smul_measure ENNReal.ofReal_ne_top)
  rw [hidentity, integral_smul_measure,
    ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg K) hB.le), smul_eq_mul] at hbound
  refine ⟨hmul, hbound, ?_⟩
  calc
    (∫ r in radialCore D, k r * f r) ^ 2 ≤
        (D.b - D.a) * ∫ r in radialCore D, (k r * f r) ^ 2 :=
      referenceRadial_integral_sq_le hab hmul
    _ ≤ (D.b - D.a) *
        ((K ^ 2 * B) * ∫ r, f r ^ 2 ∂referenceRadialWeightedMeasure D γ M) :=
      mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hab.le)
    _ = _ := by ring

end ContinuousFlexibility.Statements
