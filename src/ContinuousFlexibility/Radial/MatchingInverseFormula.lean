import ContinuousFlexibility.Statements.RadialTargets
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The bounded operator in the matched inverse formula

The source fields in the matching data are genuine restrictions in L2.
This identifies them with continuous linear contractions, including the
scalar coordinate. The finite-rank matching formula consequently defines
a bounded linear map before any differential graph identity is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators RealInnerProductSpace

private def modeSourceRestrictionLinear (D : ReferenceData) (s : Set ℝ)
    (keepScalar : Bool) (T : RadialModePair D → RadialModePair D)
    (hfield : ∀ F, ((T F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      s.indicator (fun r => F.1 r))
    (hscalar : ∀ F, (T F).2 = if keepScalar then F.2 else 0) :
    RadialModePair D →ₗ[ℝ] RadialModePair D where
  toFun := T
  map_add' F H := by
    classical
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [hfield (F + H), hfield F, hfield H,
        Lp.coeFn_add F.1 H.1, Lp.coeFn_add (T F).1 (T H).1]
        with r hsum hF hH hFH hTH
      change (T (F + H)).1 r = ((T F).1 + (T H).1) r
      rw [hTH, Pi.add_apply, hsum, hF, hH]
      by_cases hr : r ∈ s
      · simpa only [Set.indicator_of_mem hr, Pi.add_apply, Prod.fst_add] using hFH
      · simp only [Set.indicator_of_notMem hr, add_zero]
    · change (T (F + H)).2 = (T F).2 + (T H).2
      simp only [hscalar]
      cases keepScalar <;> simp
  map_smul' c F := by
    classical
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [hfield (c • F), hfield F,
        Lp.coeFn_smul c F.1, Lp.coeFn_smul c (T F).1]
        with r hprod hF hcF hcT
      change (T (c • F)).1 r = (c • (T F).1) r
      rw [hcT, Pi.smul_apply, hprod, hF]
      by_cases hr : r ∈ s
      · simpa only [Set.indicator_of_mem hr, Pi.smul_apply, Prod.fst_smul] using hcF
      · simp only [Set.indicator_of_notMem hr, smul_zero]
    · change (T (c • F)).2 = c • (T F).2
      simp only [hscalar]
      cases keepScalar <;> simp

private theorem modeSourceRestriction_norm (D : ReferenceData) (s : Set ℝ)
    (keepScalar : Bool) (T : RadialModePair D → RadialModePair D)
    (hfield : ∀ F, ((T F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      s.indicator (fun r => F.1 r))
    (hscalar : ∀ F, (T F).2 = if keepScalar then F.2 else 0)
    (F : RadialModePair D) : ‖T F‖ ≤ 1 * ‖F‖ := by
  classical
  have hfirst : ‖(T F).1‖ ≤ ‖F.1‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hfield F] with r hr
    rw [hr]
    by_cases hs : r ∈ s
    · simp only [Set.indicator_of_mem hs, le_refl]
    · simpa only [Set.indicator_of_notMem hs, norm_zero] using norm_nonneg (F.1 r)
  have hsecond : ‖(T F).2‖ ≤ ‖F.2‖ := by
    rw [hscalar]
    cases keepScalar <;> simp
  simpa only [Prod.norm_def, one_mul] using max_le_max hfirst hsecond

private def modeSourceRestrictionCLM (D : ReferenceData) (s : Set ℝ)
    (keepScalar : Bool) (T : RadialModePair D → RadialModePair D)
    (hfield : ∀ F, ((T F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      s.indicator (fun r => F.1 r))
    (hscalar : ∀ F, (T F).2 = if keepScalar then F.2 else 0) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  (modeSourceRestrictionLinear D s keepScalar T hfield hscalar).mkContinuous 1
    (modeSourceRestriction_norm D s keepScalar T hfield hscalar)

private theorem modeSourceRestrictionCLM_apply (D : ReferenceData) (s : Set ℝ)
    (keepScalar : Bool) (T : RadialModePair D → RadialModePair D)
    (hfield : ∀ F, ((T F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      s.indicator (fun r => F.1 r))
    (hscalar : ∀ F, (T F).2 = if keepScalar then F.2 else 0)
    (F : RadialModePair D) :
    modeSourceRestrictionCLM D s keepScalar T hfield hscalar F = T F :=
  LinearMap.mkContinuous_apply _ _ _ _

/-- Inner restriction, retaining the border source. -/
def matchingSourceInnerCLM (D : ReferenceData) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) :
    RadialModePair D →L[ℝ] RadialModePair D := by
  classical
  refine modeSourceRestrictionCLM D (Ioo M.innerLeft M.innerRight) true
    M.sourceInner ?_ ?_
  · intro F
    filter_upwards [(hM.2.2.2.1 F).2.2.1] with r hr
    simpa only [Set.indicator_apply] using hr
  · intro F
    simpa using (hM.2.2.2.1 F).1

/-- Outer restriction, with zero border source. -/
def matchingSourceOuterCLM (D : ReferenceData) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) :
    RadialModePair D →L[ℝ] RadialModePair D := by
  classical
  refine modeSourceRestrictionCLM D (Ioo M.innerLeft M.innerRight)ᶜ false
    M.sourceOuter ?_ ?_
  · intro F
    filter_upwards [(hM.2.2.2.1 F).2.2.2] with r hr
    simpa only [Set.indicator_apply, Set.mem_compl_iff, ite_not] using hr
  · intro F
    simpa using (hM.2.2.2.1 F).2.1

@[simp] theorem matchingSourceInnerCLM_apply (D : ReferenceData)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (F : RadialModePair D) : matchingSourceInnerCLM D M hM F = M.sourceInner F := by
  unfold matchingSourceInnerCLM
  exact modeSourceRestrictionCLM_apply _ _ _ _ _ _ F

@[simp] theorem matchingSourceOuterCLM_apply (D : ReferenceData)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (F : RadialModePair D) : matchingSourceOuterCLM D M hM F = M.sourceOuter F := by
  unfold matchingSourceOuterCLM
  exact modeSourceRestrictionCLM_apply _ _ _ _ _ _ F

/-- Pairing with a fixed mode pair; the product itself retains its max norm. -/
def modePairingCLM (D : ReferenceData) (U : RadialModePair D) :
    RadialModePair D →L[ℝ] ℝ :=
  (innerSL ℝ U.1).comp (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ) +
    U.2 • ContinuousLinearMap.snd ℝ (RadialModeL2 D) ℝ

@[simp] theorem modePairingCLM_apply (D : ReferenceData)
    (U F : RadialModePair D) : modePairingCLM D U F = modePairing D U F := by
  simp only [modePairingCLM, modePairing, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul]

/-- The full expression in ActualMatchedRepresentation is bounded and
linear for every source, including the inactive scalar at frequencies other
than two. -/
theorem exists_matchingFormulaCLM (D : ReferenceData) (M : RadialMatchingData D)
    (hM : MatchingLocalRealizations D M) :
    ∃ G : RadialModePair D →L[ℝ] RadialModePair D, ∀ F,
      let fh := M.sourceInner F
      let fo := M.sourceOuter F
      let h := fun i => modePairing D (M.innerPoisson i) fh
      let o := fun i => modePairing D (M.outerPoisson i) fo
      let x := radialMatrixApply M.Kinv (fun i => o i + radialMatrixApply M.A h i)
      let y := fun i => radialMatrixApply
        (fun a b => M.A a b + radialMatrixProduct M.B M.Db a b) x i -
          radialMatrixApply M.B h i
      G F = M.innerInverse fh + M.outerInverse fo +
        (∑ i, x i • M.innerPoisson i) + (∑ i, y i • M.outerPoisson i) := by
  classical
  let Si := matchingSourceInnerCLM D M hM
  let So := matchingSourceOuterCLM D M hM
  let h : Fin 2 → (RadialModePair D →L[ℝ] ℝ) := fun i =>
    (modePairingCLM D (M.innerPoisson i)).comp Si
  let o : Fin 2 → (RadialModePair D →L[ℝ] ℝ) := fun i =>
    (modePairingCLM D (M.outerPoisson i)).comp So
  let x : Fin 2 → (RadialModePair D →L[ℝ] ℝ) := fun i =>
    ∑ k, M.Kinv i k • (o k + ∑ l, M.A k l • h l)
  let y : Fin 2 → (RadialModePair D →L[ℝ] ℝ) := fun i =>
    (∑ k, (M.A i k + radialMatrixProduct M.B M.Db i k) • x k) -
      ∑ k, M.B i k • h k
  let G : RadialModePair D →L[ℝ] RadialModePair D :=
    M.innerInverse.comp Si + M.outerInverse.comp So +
      (∑ i, (x i).smulRight (M.innerPoisson i)) +
      (∑ i, (y i).smulRight (M.outerPoisson i))
  refine ⟨G, ?_⟩
  intro F
  dsimp only
  simp only [G, x, y, h, o, Si, So, radialMatrixApply,
    add_apply, sub_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, matchingSourceInnerCLM_apply,
    matchingSourceOuterCLM_apply, modePairingCLM_apply, smul_eq_mul]

end ContinuousFlexibility.Statements
