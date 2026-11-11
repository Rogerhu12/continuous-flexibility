import ContinuousFlexibility.Radial.OuterWholeGreenOperator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual whole operator in integral coordinates

The compact-subtype construction is identified with integrals on the
original core interval.  Both restrictions of the assembled operator
therefore have explicit representatives on the original weighted measure.
These identities hold for every L² source.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Analysis

variable (μ : Measure ℝ) {a c : ℝ} (hac : a ≤ c)
  [IsFiniteMeasure (compactIntervalMeasure μ a c)]

/-- A continuous core function on the actual compact interval. -/
def outerCoreRestriction (U : ℝ → ℝ) (hU : ContinuousOn U (Icc a c)) :
    C(Icc a c, ℝ) := ⟨fun x => U x, hU.domRestrict⟩

theorem outerCoreRestriction_apply (U : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (x : Icc a c) :
    outerCoreRestriction U hU x = U x := rfl

theorem outer_compact_source_coeFn (f : Lp ℝ 2 μ) :
    (l2CompactIntervalEquiv μ hac (l2Restrict μ (Icc a c) f) : Icc a c → ℝ) =ᵐ[
      compactIntervalMeasure μ a c] fun x => f x := by
  have hv := measurePreserving_compactInterval_val μ a c
  filter_upwards [l2CompactIntervalEquiv_coeFn μ hac (l2Restrict μ (Icc a c) f),
    hv.quasiMeasurePreserving.ae (l2Restrict_coeFn μ (Icc a c) f)] with x hx hfx
  exact hx.trans hfx

theorem outer_compact_inner_eq_integral (U : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (f : Lp ℝ 2 μ) :
    inner ℝ (ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ
      (outerCoreRestriction U hU))
      (l2CompactIntervalEquiv μ hac (l2Restrict μ (Icc a c) f)) =
      ∫ x in Icc a c, U x * f x ∂μ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x : Icc a c, U x * f x ∂compactIntervalMeasure μ a c := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
        (compactIntervalMeasure μ a c) (outerCoreRestriction U hU),
        outer_compact_source_coeFn μ hac f] with x hx hfx
      rw [Real.inner_apply, hx, hfx, outerCoreRestriction_apply]
    _ = _ := integral_subtype_comap measurableSet_Icc _

/-- The core product is integrable, even for an arbitrary L² source. -/
theorem integrable_outer_core_product (U : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (f : Lp ℝ 2 μ) :
    Integrable (fun x => U x * f x) (μ.restrict (Icc a c)) := by
  have hv := measurePreserving_compactInterval_val μ a c
  apply (hv.integrable_comp_emb (MeasurableEmbedding.subtype_coe measurableSet_Icc)).mp
  have h := L2.integrable_inner (𝕜 := ℝ)
    (ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ (outerCoreRestriction U hU))
    (l2CompactIntervalEquiv μ hac (l2Restrict μ (Icc a c) f))
  refine h.congr ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
    (compactIntervalMeasure μ a c) (outerCoreRestriction U hU),
    outer_compact_source_coeFn μ hac f] with x hx hfx
  simp only [Function.comp_apply, Real.inner_apply, hx, hfx, outerCoreRestriction_apply]

theorem outerGreenKernel_core_restriction (lam : ℝ) (U V : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (x y : Icc a c) :
    outerGreenKernel lam (outerCoreRestriction U hU) (outerCoreRestriction V hV) x y =
      outerGreenKernel lam U V (x : ℝ) (y : ℝ) := by
  rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
  · rw [outerGreenKernel_of_le (show x ≤ y from hxy), outerGreenKernel_of_le hxy]
    rfl
  · rw [outerGreenKernel_symm lam (outerCoreRestriction U hU) (outerCoreRestriction V hV) x y,
      outerGreenKernel_symm lam U V (x : ℝ) (y : ℝ),
      outerGreenKernel_of_le (show y ≤ x from hyx), outerGreenKernel_of_le hyx]
    rfl

theorem outer_compact_kernelRepresentative_eq_integral (lam : ℝ) (U V : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (f : Lp ℝ 2 μ) (x : Icc a c) :
    outerKernelRepresentative (compactIntervalMeasure μ a c)
      (outerContinuousGreenKernel lam (outerCoreRestriction U hU) (outerCoreRestriction V hV))
      (l2CompactIntervalEquiv μ hac (l2Restrict μ (Icc a c) f)) x =
      ∫ y in Icc a c, outerGreenKernel lam U V (x : ℝ) y * f y ∂μ := by
  rw [outerKernelRepresentative_eq_integral]
  calc
    _ = ∫ y : Icc a c, outerGreenKernel lam U V (x : ℝ) (y : ℝ) * f y
        ∂compactIntervalMeasure μ a c := by
      apply integral_congr_ae
      filter_upwards [outer_compact_source_coeFn μ hac f] with y hy
      rw [outerContinuousGreenKernel_apply, outerGreenKernel_core_restriction, hy]
    _ = _ := integral_subtype_comap measurableSet_Icc _

theorem outer_compact_toLp_symm_coeFn (W : C(Icc a c, ℝ)) :
    ((l2CompactIntervalEquiv μ hac).symm
      (ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ W) : ℝ → ℝ) =ᵐ[
      μ.restrict (Icc a c)] fun x => W (projIcc a c hac x) := by
  have hp := measurePreserving_compactInterval_proj μ hac
  filter_upwards [l2CompactIntervalEquiv_symm_coeFn μ hac
    (ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ W),
    hp.quasiMeasurePreserving.ae (ContinuousMap.coeFn_toLp
      (p := 2) (𝕜 := ℝ) (compactIntervalMeasure μ a c) W)] with x hx hW
  exact hx.trans hW

/-- The already constructed whole operator, specialized to its actual interval core. -/
def outerIntervalGreenOperator (lam : ℝ) (U V : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (D : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  outerWholeGreenOperator μ (Icc a c) measurableSet_Icc (compactIntervalMeasure μ a c)
    (l2CompactIntervalEquiv μ hac) lam ⟨c, hac, le_rfl⟩
    (outerCoreRestriction U hU) (outerCoreRestriction V hV) D p

/-- The actual whole inverse has this core representative for every L² source. -/
theorem outerIntervalGreenOperator_core_rep (lam : ℝ) (U V P : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (D : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P) (f : Lp ℝ 2 μ) :
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f : ℝ → ℝ) =ᵐ[
      μ.restrict (Icc a c)] fun x =>
      (∫ y in Icc a c, outerGreenKernel lam U V x y * f y ∂μ) +
        (V c / lam) * U x * (∫ y in (Icc a c)ᶜ, P y * f y ∂μ) := by
  let ν := compactIntervalMeasure μ a c
  let e := l2CompactIntervalEquiv μ hac
  let Uc := outerCoreRestriction U hU
  let Vc := outerCoreRestriction V hV
  let fc := e (l2Restrict μ (Icc a c) f)
  let ft := l2Restrict μ (Icc a c)ᶜ f
  let W := outerKernelRepresentative ν (outerContinuousGreenKernel lam Uc Vc) fc +
    ((V c / lam) * inner ℝ p ft) • Uc
  have hpair : inner ℝ p ft = ∫ y in (Icc a c)ᶜ, P y * f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hp, l2Restrict_coeFn μ (Icc a c)ᶜ f] with y hy hfy
    rw [Real.inner_apply, hy, hfy]
  have hcoordinates := outerWholeGreenOperator_coordinates μ (Icc a c) measurableSet_Icc
    ν e lam ⟨c, hac, le_rfl⟩ Uc Vc D p f
  rw [outerCoreCoordinates_apply, outerCoreCoordinates_apply] at hcoordinates
  have hcore := congrArg Prod.fst hcoordinates
  change e (l2Restrict μ (Icc a c)
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f)) =
      (outerActualGreenOperator ν lam ⟨c, hac, le_rfl⟩ Uc Vc D p (fc, ft)).1 at hcore
  rw [outerActualGreenOperator_core_rep] at hcore
  have hrestriction : l2Restrict μ (Icc a c)
      (outerIntervalGreenOperator μ hac lam U V hU hV D p f) =
      e.symm (ContinuousMap.toLp 2 ν ℝ W) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact hcore
  have hrep := outer_compact_toLp_symm_coeFn μ hac W
  filter_upwards [l2Restrict_coeFn μ (Icc a c)
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f), hrep,
    ae_restrict_mem measurableSet_Icc] with x hx hWx hxs
  rw [hrestriction] at hx
  rw [← hx, hWx]
  dsimp only [W, ν, e, Uc, Vc, fc, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [outer_compact_kernelRepresentative_eq_integral μ hac lam U V hU hV f,
    outerCoreRestriction_apply, projIcc_of_mem hac hxs, hpair]
  ring


/-- The tail restriction of the same whole operator contains exactly the
deep inverse and the two Poisson couplings. -/
theorem outerIntervalGreenOperator_tail_rep (lam : ℝ) (U V P : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (D : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P) (f : Lp ℝ 2 μ) :
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f : ℝ → ℝ) =ᵐ[
      μ.restrict (Icc a c)ᶜ] fun x =>
      (V c / lam) * P x * (∫ y in Icc a c, U y * f y ∂μ) +
        (D (l2Restrict μ (Icc a c)ᶜ f)) x +
        (U c * V c / lam) * P x * (∫ y in (Icc a c)ᶜ, P y * f y ∂μ) := by
  let ν := compactIntervalMeasure μ a c
  let e := l2CompactIntervalEquiv μ hac
  let Uc := outerCoreRestriction U hU
  let Vc := outerCoreRestriction V hV
  let fc := e (l2Restrict μ (Icc a c) f)
  let ft := l2Restrict μ (Icc a c)ᶜ f
  let A := (V c / lam) * inner ℝ (ContinuousMap.toLp 2 ν ℝ Uc) fc
  let B := (U c * V c / lam) * inner ℝ p ft
  have hpair : inner ℝ p ft = ∫ y in (Icc a c)ᶜ, P y * f y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hp, l2Restrict_coeFn μ (Icc a c)ᶜ f] with y hy hfy
    rw [Real.inner_apply, hy, hfy]
  have hcoordinates := outerWholeGreenOperator_coordinates μ (Icc a c) measurableSet_Icc
    ν e lam ⟨c, hac, le_rfl⟩ Uc Vc D p f
  rw [outerCoreCoordinates_apply, outerCoreCoordinates_apply] at hcoordinates
  have htail := congrArg Prod.snd hcoordinates
  change l2Restrict μ (Icc a c)ᶜ
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f) =
      (outerActualGreenOperator ν lam ⟨c, hac, le_rfl⟩ Uc Vc D p (fc, ft)).2 at htail
  rw [outerActualGreenOperator, outerBlockOperator_apply] at htail
  have hrestriction : l2Restrict μ (Icc a c)ᶜ
      (outerIntervalGreenOperator μ hac lam U V hU hV D p f) =
      A • p + D ft + B • p := by
    simpa only [smul_smul] using htail
  have hrep : (A • p + D ft + B • p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ)) =ᵐ[
      μ.restrict (Icc a c)ᶜ] fun x => A * P x + D ft x + B * P x := by
    filter_upwards [Lp.coeFn_add (A • p + D ft) (B • p),
      Lp.coeFn_add (A • p) (D ft), Lp.coeFn_smul A p, Lp.coeFn_smul B p,
      hp] with x hx hadd hA hB hpx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hadd hA hB
    rw [hx, hadd, hA, hB, hpx]
  filter_upwards [l2Restrict_coeFn μ (Icc a c)ᶜ
    (outerIntervalGreenOperator μ hac lam U V hU hV D p f), hrep] with x hx hrep
  rw [hrestriction] at hx
  rw [← hx, hrep]
  dsimp only [A, B, ν, Uc, fc, e]
  rw [outer_compact_inner_eq_integral μ hac U hU f, hpair]
  ring

end ContinuousFlexibility.Radial
