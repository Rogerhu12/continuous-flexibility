import ContinuousFlexibility.Radial.OuterGreenAssembly

/-!
# The normalized natural solution in the whole Hilbert space

The core restriction and the exact deep Poisson multiple give one actual
L² vector.  This proves both full square integrability and the quantitative
norm used in the complementary Robin trace.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

variable (μ : Measure ℝ) {a c b : ℝ} (hac : a ≤ c)
  [IsFiniteMeasure (compactIntervalMeasure μ a c)]
  {alpha beta P ZP Q ZQ : ℝ → ℝ}
  (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)

def OuterFundamentalStatePair.naturalVector (hcb : c < b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ)) : Lp ℝ 2 μ :=
  outerCoreAssemble μ (Icc a c) measurableSet_Icc (compactIntervalMeasure μ a c)
    (l2CompactIntervalEquiv μ hac)
    (ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ
      (outerCoreRestriction H.V (H.continuousOn_core hcb).2), H.V c • p)

theorem OuterFundamentalStatePair.naturalVector_ae (hcb : c < b) (hPc : P c = 1)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P) :
    (H.naturalVector μ hac hcb p : ℝ → ℝ) =ᵐ[μ] H.V := by
  let W := outerCoreRestriction H.V (H.continuousOn_core hcb).2
  let v := ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ W
  have hc := outer_compact_toLp_symm_coeFn μ hac W
  have ht := Lp.coeFn_smul (H.V c) p
  rw [OuterFundamentalStatePair.naturalVector, outerCoreAssemble_apply]
  apply (l2Glue_coeFn μ (Icc a c) measurableSet_Icc
    ((l2CompactIntervalEquiv μ hac).symm v, H.V c • p)).trans
  filter_upwards [ae_imp_of_ae_restrict hc, ae_imp_of_ae_restrict ht,
    ae_imp_of_ae_restrict hp, hμ] with x hcx htx hpx hx
  by_cases hxs : x ∈ Icc a c
  · rw [indicator_of_mem hxs, indicator_of_notMem (not_not.mpr hxs), add_zero,
      hcx hxs]
    dsimp only [W]
    rw [outerCoreRestriction_apply, projIcc_of_mem hac hxs]
  · rw [indicator_of_notMem hxs, indicator_of_mem hxs, zero_add, htx hxs]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hpx hxs]
    have hdeep : x ∈ Ico c b :=
      ⟨(lt_of_not_ge (fun hxc => hxs ⟨hx.1, hxc⟩)).le, hx.2⟩
    exact (H.V_tail_factor hcb hPc x hdeep).symm

include hac in
theorem OuterFundamentalStatePair.V_memLp (hcb : c < b) (hPc : P c = 1)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P) :
    MemLp H.V 2 μ :=
  (memLp_congr_ae (H.naturalVector_ae μ hac hcb hPc hμ p hp)).mp
    (Lp.memLp (H.naturalVector μ hac hcb p))

/-- The same natural vector has the manuscript's scale and core-action bound. -/
theorem OuterFundamentalStatePair.norm_naturalVector_le
    {lam A K : ℝ} (hcb : c < b) (hlam : 0 < lam) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hV : ∀ x ∈ Icc a c, |H.V x| ≤ K)
    (hmass : (measureUnivNNReal (compactIntervalMeasure μ a c) : ℝ) ≤ lam * A ^ 2)
    (hp : ‖p‖ ≤ Real.sqrt lam * A) :
    ‖H.naturalVector μ hac hcb p‖ ≤ 2 * (Real.sqrt lam * A * K) := by
  let W := outerCoreRestriction H.V (H.continuousOn_core hcb).2
  let v := ContinuousMap.toLp 2 (compactIntervalMeasure μ a c) ℝ W
  have hv : ‖v‖ ≤ Real.sqrt lam * A * K :=
    norm_outerActualCoreVector_le (compactIntervalMeasure μ a c) hlam hA hK W
      (fun x => hV x x.property) hmass
  have hc : |H.V c| ≤ K := hV c ⟨hac, le_rfl⟩
  have ht : ‖H.V c • p‖ ≤ Real.sqrt lam * A * K := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |H.V c| * ‖p‖ ≤ K * (Real.sqrt lam * A) :=
        mul_le_mul hc hp (norm_nonneg _) hK
      _ = _ := by ring
  have hpair : ‖(v, H.V c • p)‖ ≤ Real.sqrt lam * A * K := by
    rw [Prod.norm_def]
    exact max_le hv ht
  exact (norm_outerCoreAssemble_apply_le μ (Icc a c) measurableSet_Icc
    (compactIntervalMeasure μ a c) (l2CompactIntervalEquiv μ hac)
    (v, H.V c • p)).trans (mul_le_mul_of_nonneg_left hpair (by norm_num))

end ContinuousFlexibility.Radial
