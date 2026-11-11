import ContinuousFlexibility.Analysis.SeeleyJetExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# Sobolev half-line jets are bounded

For a Banach-valued function continuous up to zero, the fundamental theorem of
calculus on each interval `[x, x + 1]` bounds its value by the local integrals of
the norms of the function and its derivative.  The `L¹` to `L²` comparison on a
unit interval then gives a uniform bound by the two half-line `L²` norms.

Consequently, a smooth one-sided jet with every derivative in `L²` satisfies the
boundedness hypotheses of Seeley's extension.  No extension across zero or
global differentiability is assumed in obtaining these bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The endpoint value estimate on a unit interval, for Banach-valued functions
with a derivative only in the interior. -/
theorem norm_le_unitInterval_integrals {f g : ℝ → F} {x : ℝ}
    (hf : ContinuousOn f (Icc x (x + 1)))
    (hg : ContinuousOn g (Icc x (x + 1)))
    (hd : ∀ y ∈ Ioo x (x + 1), HasDerivAt f (g y) y) :
    ‖f x‖ ≤ (∫ y in Ioc x (x + 1), ‖f y‖) +
      ∫ y in Ioc x (x + 1), ‖g y‖ := by
  let A : ℝ := ∫ y in Ioc x (x + 1), ‖g y‖
  have hgi : IntegrableOn (fun y ↦ ‖g y‖) (Ioc x (x + 1)) volume :=
    hg.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfi : IntegrableOn (fun y ↦ ‖f y‖) (Ioc x (x + 1)) volume :=
    hf.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpoint (y : ℝ) (hy : y ∈ Ioc x (x + 1)) : ‖f x‖ ≤ ‖f y‖ + A := by
    have hsub : Icc x y ⊆ Icc x (x + 1) := Icc_subset_Icc le_rfl hy.2
    have hgy : IntervalIntegrable g volume x y :=
      (hg.mono hsub).intervalIntegrable_of_Icc hy.1.le
    have he : (∫ t in x..y, g t) = f y - f x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.1.le (hf.mono hsub)
        (fun t ht ↦ hd t ⟨ht.1, ht.2.trans_le hy.2⟩) hgy
    have hdiff : ‖f y - f x‖ ≤ A := by
      calc
        ‖f y - f x‖ = ‖∫ t in x..y, g t‖ := by rw [he]
        _ ≤ ∫ t in x..y, ‖g t‖ := intervalIntegral.norm_integral_le_integral_norm hy.1.le
        _ ≤ A := by
          rw [intervalIntegral.integral_of_le hy.1.le]
          exact setIntegral_mono_set hgi (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (Eventually.of_forall fun t ht ↦ ⟨ht.1, ht.2.trans hy.2⟩)
    calc
      ‖f x‖ = ‖f x - f y + f y‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
      _ = ‖f y - f x‖ + ‖f y‖ := by rw [norm_sub_rev]
      _ ≤ ‖f y‖ + A := by linarith
  have hleft : IntegrableOn (fun _ : ℝ ↦ ‖f x‖) (Ioc x (x + 1)) volume :=
    continuous_const.integrableOn_Ioc
  have hconst : IntegrableOn (fun _ : ℝ ↦ A) (Ioc x (x + 1)) volume :=
    continuous_const.integrableOn_Ioc
  have hm := setIntegral_mono_on hleft (hfi.add hconst) measurableSet_Ioc hpoint
  rw [integral_add' hfi hconst, setIntegral_const, setIntegral_const] at hm
  simpa only [measureReal_def, Real.volume_Ioc, add_sub_cancel_left,
    ENNReal.ofReal_one, ENNReal.toReal_one, smul_eq_mul, one_mul] using hm

/-- Local `L¹` norm on a unit interval is bounded by the actual half-line `L²`
norm.  The constant is independent of the position of the interval. -/
theorem integral_norm_unitInterval_le_halfLine_L2 {f : ℝ → F}
    (hf : MemLp f 2 (volume.restrict (Ici 0))) {x : ℝ} (hx : 0 ≤ x) :
    (∫ y in Ioc x (x + 1), ‖f y‖) ≤
      (eLpNorm f 2 (volume.restrict (Ici 0))).toReal := by
  let ν : Measure ℝ := volume.restrict (Ioc x (x + 1))
  have hν : ν ≤ volume.restrict (Ici 0) :=
    Measure.restrict_mono_set volume (fun y hy ↦ hx.trans hy.1.le)
  have hlocal : MemLp f 2 ν := hf.mono_measure hν
  have hmass : ν univ = 1 := by
    simp only [ν, Measure.restrict_apply_univ, Real.volume_Ioc, add_sub_cancel_left,
      ENNReal.ofReal_one]
  have hcompare : eLpNorm f 1 ν ≤ eLpNorm f 2 (volume.restrict (Ici 0)) := by
    calc
      eLpNorm f 1 ν ≤ eLpNorm f 2 ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal -
          1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hlocal.aestronglyMeasurable
      _ = eLpNorm f 2 ν := by rw [hmass, ENNReal.one_rpow, mul_one]
      _ ≤ eLpNorm f 2 (volume.restrict (Ici 0)) := eLpNorm_mono_measure f hν
  calc
    (∫ y in Ioc x (x + 1), ‖f y‖) = (eLpNorm f 1 ν).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hlocal.aestronglyMeasurable]
      exact integral_norm_eq_lintegral_enorm hlocal.aestronglyMeasurable
    _ ≤ (eLpNorm f 2 (volume.restrict (Ici 0))).toReal :=
      ENNReal.toReal_mono hf.eLpNorm_ne_top hcompare

/-- A true Sobolev pointwise estimate, including the boundary value at zero. -/
theorem norm_halfLine_le_L2_add_derivative_L2 {f g : ℝ → F}
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt f (g x) x)
    (hf₂ : MemLp f 2 (volume.restrict (Ici 0)))
    (hg₂ : MemLp g 2 (volume.restrict (Ici 0)))
    {x : ℝ} (hx : 0 ≤ x) :
    ‖f x‖ ≤ (eLpNorm f 2 (volume.restrict (Ici 0))).toReal +
      (eLpNorm g 2 (volume.restrict (Ici 0))).toReal := by
  have hsub : Icc x (x + 1) ⊆ Ici 0 := fun y hy ↦ hx.trans hy.1
  exact (norm_le_unitInterval_integrals (hf.mono hsub) (hg.mono hsub)
    (fun y hy ↦ hd y (hx.trans_lt hy.1))).trans
      (add_le_add (integral_norm_unitInterval_le_halfLine_L2 hf₂ hx)
        (integral_norm_unitInterval_le_halfLine_L2 hg₂ hx))

/-- `L²` control of every one-sided jet supplies the boundedness needed by the
reflection series; it is not an additional regularity assumption. -/
theorem isBoundedHalfLineJet_of_memLp {J : ℕ → ℝ → F}
    (hc : ∀ n, ContinuousOn (J n) (Ici 0))
    (hd : ∀ n x, 0 < x → HasDerivAt (J n) (J (n + 1) x) x)
    (hL₂ : ∀ n, MemLp (J n) 2 (volume.restrict (Ici 0))) :
    IsBoundedHalfLineJet J where
  continuous := hc
  derivative := hd
  bounded n := ⟨(eLpNorm (J n) 2 (volume.restrict (Ici 0))).toReal +
    (eLpNorm (J (n + 1)) 2 (volume.restrict (Ici 0))).toReal,
    fun x hx ↦ norm_halfLine_le_L2_add_derivative_L2 (hc n) (hc (n + 1))
      (hd n) (hL₂ n) (hL₂ (n + 1)) hx⟩

/-- The same Seeley operator extends every smooth half-line jet whose entries
belong to `L²`, without a separate pointwise boundedness hypothesis. -/
theorem contDiff_seeleyExtend_of_memLp {ι : Type*} (S : SeeleyData ι)
    {J : ℕ → ℝ → F} (hc : ∀ n, ContinuousOn (J n) (Ici 0))
    (hd : ∀ n x, 0 < x → HasDerivAt (J n) (J (n + 1) x) x)
    (hL₂ : ∀ n, MemLp (J n) 2 (volume.restrict (Ici 0))) :
    ContDiff ℝ ∞ (seeleyExtend S (J 0)) :=
  contDiff_seeleyExtend S (isBoundedHalfLineJet_of_memLp hc hd hL₂)

/-- Every derivative of the extended function agrees with the original jet on
the closed half-line. -/
theorem iteratedDeriv_seeleyExtend_of_memLp_nonneg {ι : Type*} (S : SeeleyData ι)
    {J : ℕ → ℝ → F} (hc : ∀ n, ContinuousOn (J n) (Ici 0))
    (hd : ∀ n x, 0 < x → HasDerivAt (J n) (J (n + 1) x) x)
    (hL₂ : ∀ n, MemLp (J n) 2 (volume.restrict (Ici 0)))
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv n (seeleyExtend S (J 0)) x = J n x :=
  iteratedDeriv_seeleyExtend_of_nonneg S (isBoundedHalfLineJet_of_memLp hc hd hL₂) n hx

end ContinuousFlexibility.Analysis
