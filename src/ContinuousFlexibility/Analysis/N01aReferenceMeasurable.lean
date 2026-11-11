import ContinuousFlexibility.Analysis.N01aReferencePairing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Measurability supplied by the actual smooth graph core

Integrability of a square alone does not imply measurability of its signed
square root.  The smooth-core approximation supplies the missing sign
information by convergence in measure.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

/-- Square convergence implies convergence in measure, without presupposing
measurability of either signed function. -/
theorem n01a_tendstoInMeasure_of_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hi : ∀ n, Integrable (fun x => (f n x - g x) ^ 2) μ)
    (hlim : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  have hm (n : ℕ) : MemLp (fun x => |f n x - g x|) 2 μ :=
    n01a_memLp_abs_of_integrable_sq (hi n)
  have heq (n : ℕ) : eLpNorm (fun x => |f n x - g x|) 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ)) := by
    rw [(hm n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, abs_abs, sq_abs]
    rw [← one_div, ← Real.sqrt_eq_rpow]
  have hnorm : Tendsto (fun n => eLpNorm (fun x => |f n x - g x|) 2 μ)
      atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ))
        atTop (𝓝 0) := by simpa only [Real.sqrt_zero] using hlim.sqrt
    simpa only [Function.comp_def, heq, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hsqrt
  have habs : TendstoInMeasure μ (fun n x => |f n x - g x|) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    simpa only [Pi.sub_def, sub_zero] using hnorm
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  simpa only [Real.dist_eq, sub_zero, abs_abs] using
    tendstoInMeasure_iff_dist.mp habs ε hε

theorem continuous_memLp_radialPhysicalMeasure {D : ReferenceData}
    {f : PolarPoint → ℝ} (hf : Continuous f) : MemLp f 2 (radialPhysicalMeasure D) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact ((hf.pow 2).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self)

/-- Every graph output is genuinely measurable because its prescribed smooth
core converges in the actual physical square integral. -/
theorem ReferenceGraph.aestronglyMeasurable {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    (hchi : ContDiff ℝ ∞ D.chiLeft) {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown} {F : RadialSource} (hgraph : ReferenceGraph D γ M₀ M₁ U F) :
    AEStronglyMeasurable U.1 (radialPhysicalMeasure D) := by
  obtain ⟨Un, Fn, an, hn, _, hlim⟩ := hcore U F hgraph
  obtain ⟨C, hC, hphysical⟩ := exists_output_physical_square_bound hab hpart hγ M₁
  let fn (n : ℕ) (p : PolarPoint) : ℝ := (Un n).1 p - an n * D.chiLeft p.1
  have hfn (n : ℕ) : AEStronglyMeasurable (fn n) (radialPhysicalMeasure D) :=
    ((hn n).2.1.1.continuous.sub
      (continuous_const.mul (hchi.continuous.comp continuous_fst))).aestronglyMeasurable
  have heq (n : ℕ) (p : PolarPoint) : fn n p - U.1 p =
      outputRemainder D (an n) (Un n - U) p := by
    simp only [fn, outputRemainder, Prod.fst_sub, Pi.sub_apply]
    ring
  have hi (n : ℕ) : Integrable (fun p => (fn n p - U.1 p) ^ 2)
      (radialPhysicalMeasure D) := by
    simpa only [heq] using (hphysical (Un n - U) (an n) (hn n).2.2).1
  have hb (n : ℕ) : (∫ p, (fn n p - U.1 p) ^ 2 ∂radialPhysicalMeasure D) ≤
      C * outputNormSquare D γ M₁ (an n) (Un n - U) := by
    simpa only [heq] using (hphysical (Un n - U) (an n) (hn n).2.2).2
  have hsquare : Tendsto (fun n => ∫ p, (fn n p - U.1 p) ^ 2 ∂radialPhysicalMeasure D)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
      (Eventually.of_forall hb)
    simpa only [mul_zero] using hlim.const_mul C
  exact (n01a_tendstoInMeasure_of_integral_sq hi hsquare).aestronglyMeasurable hfn

theorem ReferenceGraph.memLp_two {D : ReferenceData}
    (hab : D.a ≤ D.b) (hpart : RadialPartition D)
    (hchi : ContDiff ℝ ∞ D.chiLeft) {γ M₀ M₁ : ℝ} (hγ : 0 < γ)
    (hcore : ReferenceSmoothCoreClosure D γ M₀ M₁)
    {U : RadialUnknown} {F : RadialSource} (hgraph : ReferenceGraph D γ M₀ M₁ U F) :
    MemLp U.1 2 (radialPhysicalMeasure D) := by
  have hm := hgraph.aestronglyMeasurable hab hpart hchi hγ hcore
  obtain ⟨aL, hreal⟩ := hgraph.1
  obtain ⟨C, hC, hb⟩ := exists_output_physical_square_bound hab hpart hγ M₁
  have hrem : MemLp (outputRemainder D aL U) 2 (radialPhysicalMeasure D) :=
    (memLp_two_iff_integrable_sq
      (hm.sub (continuous_const.mul (hchi.continuous.comp continuous_fst)).aestronglyMeasurable)).mpr
        (hb U aL hreal).1
  have hleft : MemLp (fun p : PolarPoint => aL * D.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    continuous_memLp_radialPhysicalMeasure
      (continuous_const.mul (hchi.continuous.comp continuous_fst))
  convert hrem.add hleft using 1
  funext p
  simp only [Pi.add_apply, outputRemainder, sub_add_cancel]

end ContinuousFlexibility.Statements
