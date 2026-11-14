module

public import ContinuousFlexibility.Radial.SelectedTailWeakPairing
public import ContinuousFlexibility.Radial.MatchingCutoffTests

/-!
# Assembly of the two actual exterior weak inverses

The operator is the sum of the two regional zero extensions, with zero
scalar component. A compact smooth test on the disjoint union splits
across a point in the open gap. Each part retains the original endpoint
behavior, so this proves the frozen ordinary-support weak equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem radialTailZeroExtendOperator_ae
    {D : ReferenceData} {right : Bool} {cut : ℝ}
    {R : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D right cut))}
    {f : RadialModeL2 D} {u : ℝ → ℝ}
    (h : (R (l2Restrict (radialHilbertMeasure D) (radialTailInterval D right cut) f) :
        ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict
          (radialTailInterval D right cut)] u) :
    (radialTailZeroExtendOperator D right cut R f : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (radialTailInterval D right cut).indicator u := by
  let s := radialTailInterval D right cut
  have hs : MeasurableSet s := by cases right <;> exact measurableSet_Ioo
  filter_upwards [l2ZeroExtend_coeFn (radialHilbertMeasure D) s hs
    (R (l2Restrict (radialHilbertMeasure D) s f)),
    ae_imp_of_ae_restrict h] with r he hr
  change l2ZeroExtend (radialHilbertMeasure D) s hs
    (R (l2Restrict (radialHilbertMeasure D) s f)) r = s.indicator u r
  rw [he]
  by_cases hrs : r ∈ s
  · rw [indicator_of_mem hrs, indicator_of_mem hrs, hr hrs]
  · rw [indicator_of_notMem hrs, indicator_of_notMem hrs]

def radialOuterPairOperator (D : ReferenceData) (l h : ℝ)
    (RL : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D false l)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D false l)))
    (RR : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D true h)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D true h))) :
    RadialModePair D →L[ℝ] RadialModePair D :=
  (((radialTailZeroExtendOperator D false l RL +
      radialTailZeroExtendOperator D true h RR).comp
        (ContinuousLinearMap.fst ℝ (RadialModeL2 D) ℝ)).prod 0)

private theorem outerJacobiVector_restrict_congr
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (j : ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) {ψ φ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hφ : ContDiff ℝ ∞ φ)
    (he : ∀ r ∈ s, ψ =ᶠ[𝓝 r] φ) :
    l2Restrict (radialHilbertMeasure D) s (matchingJacobiVector D hD j ψ hψ) =
      l2Restrict (radialHilbertMeasure D) s (matchingJacobiVector D hD j φ hφ) := by
  apply Lp.ext
  have hψv : (matchingJacobiVector D hD j ψ hψ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      matchingJacobiTest D j ψ := MemLp.coeFn_toLp _
  have hφv : (matchingJacobiVector D hD j φ hφ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      matchingJacobiTest D j φ := MemLp.coeFn_toLp _
  filter_upwards [l2Restrict_coeFn (radialHilbertMeasure D) s
      (matchingJacobiVector D hD j ψ hψ),
    l2Restrict_coeFn (radialHilbertMeasure D) s (matchingJacobiVector D hD j φ hφ),
    ae_restrict_of_ae hψv, ae_restrict_of_ae hφv, ae_restrict_mem hs]
    with r hrψ hrφ hψr hφr hrs
  rw [hrψ, hrφ, hψr, hφr]
  have hd : (fun t => D.w t * deriv ψ t) =ᶠ[𝓝 r]
      (fun t => D.w t * deriv φ t) := by
    filter_upwards [(he r hrs).deriv] with t ht
    rw [ht]
  unfold matchingJacobiTest radialJacobi
  rw [hd.deriv_eq, (he r hrs).eq_of_nhds]

private theorem outerTest_decomposition {a l h b : ℝ} (hlh : l < h)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : Function.support ψ ⊆ Ioo a l ∪ Ioo h b) :
    ∃ ψL ψR : ℝ → ℝ,
      ContDiff ℝ ∞ ψL ∧ HasCompactSupport ψL ∧ Function.support ψL ⊆ Ioo a l ∧
      ContDiff ℝ ∞ ψR ∧ HasCompactSupport ψR ∧ Function.support ψR ⊆ Ioo h b ∧
      (∀ r ∈ Ioo a l, ψ =ᶠ[𝓝 r] ψL) ∧
      (∀ r ∈ Ioo h b, ψ =ᶠ[𝓝 r] ψR) ∧
      ψ = fun r => ψL r + ψR r := by
  classical
  let c := (l + h) / 2
  have hlc : l < c := by dsimp only [c]; linarith only [hlh]
  have hch : c < h := by dsimp only [c]; linarith only [hlh]
  have hz : ψ =ᶠ[𝓝 c] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hlc hch] with r hr
    by_contra hn
    rcases hsψ hn with hL | hR
    · exact (not_lt_of_ge hr.1.le) hL.2
    · exact (not_lt_of_ge hr.2.le) hR.1
  let ψL := (Iio c).indicator ψ
  let ψR : ℝ → ℝ := fun r => ψ r - ψL r
  have hLsub : Function.support ψL ⊆ Function.support ψ := by
    intro r hr hz
    apply hr
    simp only [ψL, indicator_apply, hz, ite_self]
  have hLs : ContDiff ℝ ∞ ψL := matching_contDiff_indicator_Iio hψ hz
  have hLc : HasCompactSupport ψL := hcψ.mono hLsub
  have hLsupp : Function.support ψL ⊆ Ioo a l := by
    intro r hr
    have hrc : r < c := by
      by_contra hn
      exact hr (indicator_of_notMem (show r ∉ Iio c from hn) ψ)
    rcases hsψ (hLsub hr) with hL | hR
    · exact hL
    · exact False.elim ((not_lt_of_ge hR.1.le) (hrc.trans hch))
  have hRs : ContDiff ℝ ∞ ψR := hψ.sub hLs
  have hRc : HasCompactSupport ψR := hcψ.sub hLc
  have hRsupp : Function.support ψR ⊆ Ioo h b := by
    intro r hr
    have hrψ : ψ r ≠ 0 := by
      intro hn
      apply hr
      simp only [ψR, ψL, indicator_apply, hn, ite_self, sub_self]
    have hrc : c ≤ r := by
      by_contra hn
      have hlt : r < c := lt_of_not_ge hn
      apply hr
      simp only [ψR, ψL, indicator_of_mem (show r ∈ Iio c from hlt), sub_self]
    rcases hsψ hrψ with hL | hR
    · exact False.elim ((not_lt_of_ge hrc) (hL.2.trans hlc))
    · exact hR
  refine ⟨ψL, ψR, hLs, hLc, hLsupp, hRs, hRc, hRsupp, ?_, ?_, ?_⟩
  · intro r hr
    filter_upwards [isOpen_Iio.mem_nhds (hr.2.trans hlc)] with t ht
    exact (indicator_of_mem ht ψ).symm
  · intro r hr
    filter_upwards [isOpen_Ioi.mem_nhds (hch.trans hr.1)] with t ht
    change ψ t = ψ t - (Iio c).indicator ψ t
    have htc : c < t := ht
    have hn : t ∉ Iio c := not_lt.mpr htc.le
    rw [indicator_of_notMem hn, sub_zero]
  · funext r
    dsimp only [ψR]
    ring

theorem radialOuterPairOperator_weak {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (_hB : RadialTrueBorder D)
    {l h : ℝ} {j : ℕ} (_ha : D.a < l) (hlh : l < h) (_hb : h < D.b)
    {RL : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D false l)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D false l))}
    {RR : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D true h)) →L[ℝ]
      Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D true h))}
    (hL : RadialTailWeakPairing D hD false l j RL)
    (hR : RadialTailWeakPairing D hD true h j RR) (F : RadialModePair D) :
    ModeLocalEquation D j (Ioo D.a l ∪ Ioo h D.b)
      (radialOuterPairOperator D l h RL RR F) F := by
  apply (modeLocalEquation_iff_inner hD j _ _ _).mpr
  intro ψ hψ hcψ hsψ
  obtain ⟨ψL, ψR, hLs, hLc, hLsupp, hRs, hRc, hRsupp, hLg, hRg, he⟩ :=
    outerTest_decomposition hlh hψ hcψ hsψ
  let zL := radialTailZeroExtendOperator D false l RL F.1
  let zR := radialTailZeroExtendOperator D true h RR F.1
  have hleft := (modeLocalEquation_iff_inner hD j _ _ _).mp
    (hL.zeroExtend_equation F) ψL hLs hLc hLsupp
  have hright := (modeLocalEquation_iff_inner hD j _ _ _).mp
    (hR.zeroExtend_equation F) ψR hRs hRc hRsupp
  simp only [Prod.fst, Prod.snd, zero_mul, sub_zero] at hleft hright
  have hJL : ⟪zL, matchingJacobiVector D hD j ψ hψ⟫_ℝ =
      ⟪zL, matchingJacobiVector D hD j ψL hLs⟫_ℝ := by
    let v : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D false l)) :=
      RL (l2Restrict (radialHilbertMeasure D) (radialTailInterval D false l) F.1)
    have hs : MeasurableSet (radialTailInterval D false l) := measurableSet_Ioo
    have h₁ := outer_l2ZeroExtend_inner (radialHilbertMeasure D) hs v
      (matchingJacobiVector D hD j ψ hψ)
    have h₂ := outer_l2ZeroExtend_inner (radialHilbertMeasure D) hs v
      (matchingJacobiVector D hD j ψL hLs)
    exact h₁.trans ((congrArg (fun g => ⟪v, g⟫_ℝ)
      (outerJacobiVector_restrict_congr hD j hs hψ hLs hLg)).trans h₂.symm)
  have hJR : ⟪zR, matchingJacobiVector D hD j ψ hψ⟫_ℝ =
      ⟪zR, matchingJacobiVector D hD j ψR hRs⟫_ℝ := by
    let v : Lp ℝ 2 ((radialHilbertMeasure D).restrict (radialTailInterval D true h)) :=
      RR (l2Restrict (radialHilbertMeasure D) (radialTailInterval D true h) F.1)
    have hs : MeasurableSet (radialTailInterval D true h) := measurableSet_Ioo
    have h₁ := outer_l2ZeroExtend_inner (radialHilbertMeasure D) hs v
      (matchingJacobiVector D hD j ψ hψ)
    have h₂ := outer_l2ZeroExtend_inner (radialHilbertMeasure D) hs v
      (matchingJacobiVector D hD j ψR hRs)
    exact h₁.trans ((congrArg (fun g => ⟪v, g⟫_ℝ)
      (outerJacobiVector_restrict_congr hD j hs hψ hRs hRg)).trans h₂.symm)
  have htest : matchingSmoothVector D hD ψ hψ =
      matchingSmoothVector D hD ψL hLs + matchingSmoothVector D hD ψR hRs := by
    apply Lp.ext
    filter_upwards [(show (matchingSmoothVector D hD ψ hψ : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        ψ from MemLp.coeFn_toLp _),
      (show (matchingSmoothVector D hD ψL hLs : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        ψL from MemLp.coeFn_toLp _),
      (show (matchingSmoothVector D hD ψR hRs : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        ψR from MemLp.coeFn_toLp _),
      Lp.coeFn_add (matchingSmoothVector D hD ψL hLs) (matchingSmoothVector D hD ψR hRs)]
      with r hr hrl hrr ha
    rw [hr, ha, Pi.add_apply, hrl, hrr]
    exact congrFun he r
  change ⟪zL + zR, matchingJacobiVector D hD j ψ hψ⟫_ℝ -
    0 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -⟪F.1, matchingSmoothVector D hD ψ hψ⟫_ℝ
  rw [zero_mul, sub_zero, inner_add_left, hJL, hJR, hleft, hright, htest, inner_add_right]
  ring

end ContinuousFlexibility.Radial
