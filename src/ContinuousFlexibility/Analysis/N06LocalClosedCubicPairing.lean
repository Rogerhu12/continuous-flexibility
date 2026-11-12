import ContinuousFlexibility.Analysis.N06ClosedCubicPairing
import ContinuousFlexibility.Analysis.N06CanonicalTestOperator
import ContinuousFlexibility.Radial.MatchingCutoffTests

/-!
# Closed cubic pairings from a genuine smooth neighborhood

A radial cutoff equal to one near the closed unit interval turns a
locally smooth periodic coefficient or test into a globally smooth
periodic function. Its actual germs on the closed cylinder are unchanged.
The closed cubic pairing therefore applies to the original local data.

The test need not be even. Its angular condition is exactly period `pi`,
as in the original canonical test class.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Local smoothness and periodicity on an open radial neighborhood of
the closed unit cylinder admit one global smooth periodic representative
with the same actual germ at every point of the closed cylinder. -/
theorem n06_exists_smooth_periodic_closed_strip_extension
    {l r : ℝ} (hl : l < 0) (hr : 1 < r) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ univ))
    (hp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), f (p + (0, Real.pi)) = f p) :
    ∃ g : PolarPoint → ℝ, ContDiff ℝ ∞ g ∧
      Function.Periodic g (0, Real.pi) ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), g =ᶠ[𝓝 p] f := by
  obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
    exists_matching_interval_cutoff hl (by norm_num : (0 : ℝ) ≤ 1) hr
  refine ⟨fun p => χ p.1 * f p, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hpt : p.1 ∈ tsupport χ
    · exact (hχ.comp contDiff_fst).contDiffAt.mul
        (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
          ⟨hχs hpt, mem_univ p.2⟩))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [(continuous_fst.tendsto p).eventually
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hpt)] with q hq
      change χ q.1 * f q = 0
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]
  · intro p
    change χ (p + (0, Real.pi)).1 * f (p + (0, Real.pi)) = χ p.1 * f p
    simp only [Prod.fst_add, add_zero]
    by_cases hpr : p.1 ∈ Ioo l r
    · rw [hp p ⟨hpr, mem_univ p.2⟩]
    · have hzero : χ p.1 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hpr (hχs h))
      rw [hzero, zero_mul, zero_mul]
  · intro p hpt
    filter_upwards [(continuous_fst.tendsto p).eventually (hχone p.1 hpt.1)] with q hq
    change χ q.1 = 1 at hq
    change χ q.1 * f q = f q
    rw [hq, one_mul]

/-- The five actual graph multipliers depend only on the coefficient
germs, including their first radial and angular derivatives. -/
theorem n06_cubicGraphMultipliers_congr_germ
    (d e : ℝ → ℝ) {A B C A' B' C' : PolarPoint → ℝ} {p : PolarPoint}
    (hA : A =ᶠ[𝓝 p] A') (hB : B =ᶠ[𝓝 p] B') (hC : C =ᶠ[𝓝 p] C')
    (i : Fin 5) :
    n06CubicGraphMultipliers d e A B C i p =
      n06CubicGraphMultipliers d e A' B' C' i p := by
  have hAr : radialPartial A p = radialPartial A' p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (1, 0)) (hA.fderiv_eq (𝕜 := ℝ))
  have hBr : radialPartial B p = radialPartial B' p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (1, 0)) (hB.fderiv_eq (𝕜 := ℝ))
  have hBt : angularPartial B p = angularPartial B' p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (0, 1)) (hB.fderiv_eq (𝕜 := ℝ))
  have hCt : angularPartial C p = angularPartial C' p :=
    congrArg (fun T : PolarPoint →L[ℝ] ℝ => T (0, 1)) (hC.fderiv_eq (𝕜 := ℝ))
  fin_cases i <;>
    simp only [n06CubicGraphMultipliers, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq,
      hA.eq_of_nhds, hB.eq_of_nhds, hC.eq_of_nhds, hAr, hBr, hBt, hCt]

/-- The original graph package satisfies the genuine closed cubic
pairing for coefficients and tests smooth only on a neighborhood of the
closed unit cylinder. No reflection condition is imposed on the test. -/
theorem N06UnitWeakGraphData.local_closed_cubic_pairing
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    {a c V : ℝ → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)} {K : ℝ}
    (P : N06UnitWeakGraphData a c V U F K) (D : ReferenceData)
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    {l r : ℝ} (hl₀ : l < 0) (hr₁ : 1 < r)
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo l r ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (Ioo l r ×ˢ univ))
    (hC : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ univ))
    (hpA : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), A (p + (0, Real.pi)) = A p)
    (hpB : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), B (p + (0, Real.pi)) = B p)
    (hpC : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), C (p + (0, Real.pi)) = C p)
    (hφ : ContDiffOn ℝ ∞ φ (Ioo l r ×ˢ univ))
    (hφp : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), φ (p + (0, Real.pi)) = φ p) :
    (∫ p, U 0 p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂canonicalMeasure S Kc m) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun s => 1 - 2 * s) A B C i p *
          P.field i 0 p) * φ p ∂canonicalMeasure S Kc m := by
  obtain ⟨A', hA', hpA', heA⟩ :=
    n06_exists_smooth_periodic_closed_strip_extension hl₀ hr₁ hA hpA
  obtain ⟨B', hB', hpB', heB⟩ :=
    n06_exists_smooth_periodic_closed_strip_extension hl₀ hr₁ hB hpB
  obtain ⟨C', hC', hpC', heC⟩ :=
    n06_exists_smooth_periodic_closed_strip_extension hl₀ hr₁ hC hpC
  obtain ⟨φ', hφ', hpφ', heφ⟩ :=
    n06_exists_smooth_periodic_closed_strip_extension hl₀ hr₁ hφ hφp
  have hstrip : ∀ᵐ p ∂canonicalMeasure S Kc m,
      p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    rw [canonicalMeasure, hl, hr]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
    exact ⟨Ioo_subset_Icc_self hp.1, mem_univ p.2⟩
  have hdiv (p : PolarPoint) (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
      divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A' B' C') φ' p =
      divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p := by
    have hcoeff : divergenceOperator
        (n06CubicCoefficients (fun q => cylinderWeight q.1) A' B' C') φ' p =
        divergenceOperator
          (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ' p := by
      apply n06_divergenceOperator_congr_germ φ'
      · filter_upwards [heA p hp] with q hq
        change cylinderWeight q.1 ^ 3 * A' q = cylinderWeight q.1 ^ 3 * A q
        rw [hq]
      · filter_upwards [heB p hp] with q hq
        change cylinderWeight q.1 ^ 3 * B' q = cylinderWeight q.1 ^ 3 * B q
        rw [hq]
      · filter_upwards [heC p hp] with q hq
        change cylinderWeight q.1 ^ 3 * C' q = cylinderWeight q.1 ^ 3 * C q
        rw [hq]
    exact hcoeff.trans (n06_divergenceOperator_input_congr_germ _ (heφ p hp))
  calc
    _ = ∫ p, U 0 p *
        divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A' B' C') φ' p
          ∂canonicalMeasure S Kc m := by
      apply integral_congr_ae
      filter_upwards [hstrip] with p hp
      exact congrArg (fun t : ℝ => U 0 p * t) (hdiv p hp).symm
    _ = ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun s => 1 - 2 * s) A' B' C' i p *
          P.field i 0 p) * φ' p ∂canonicalMeasure S Kc m :=
      P.closed_cubic_pairing D hl hr hUeven hUjets hA' hB' hC' hpA' hpB' hpC' hφ' hpφ'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hstrip] with p hp
      apply congrArg₂ (fun x y : ℝ => x * y)
      · exact Finset.sum_congr rfl (fun i _ =>
          congrArg (fun t : ℝ => t * P.field i 0 p)
            (n06_cubicGraphMultipliers_congr_germ cylinderWeight (fun s => 1 - 2 * s)
              (heA p hp) (heB p hp) (heC p hp) i))
      · exact (heφ p hp).eq_of_nhds

end ContinuousFlexibility.Analysis
