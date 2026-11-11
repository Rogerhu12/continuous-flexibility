import ContinuousFlexibility.Radial.ModeCoreSource

/-!
# Linear algebra of the bordered modal graph

The ordinary border row is a Hilbert pairing, so its additivity and scalar
linearity are genuine integral identities. The full graph and inner
Dirichlet graph inherit the corresponding algebraic closure properties.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingModeRow_zero {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (j : ℕ) :
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (0 : RadialModeL2 D) r) = 0
    else (0 : ℝ) = 0 ∧ (0 : ℝ) = 0 := by
  split_ifs
  · rw [matchingColumn_integral_eq_inner hD hB]
    exact inner_zero_left _
  · exact ⟨rfl, rfl⟩

theorem matchingModeRow_add {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F V H : RadialModePair D}
    (hU : if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
      else U.2 = 0 ∧ F.2 = 0)
    (hV : if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * V.1 r) = H.2
      else V.2 = 0 ∧ H.2 = 0) :
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (U + V).1 r) = (F + H).2
      else (U + V).2 = 0 ∧ (F + H).2 = 0 := by
  by_cases hj : j = 2
  · simp only [hj, if_pos, ite_true, Prod.fst_add, Prod.snd_add,
      matchingColumn_integral_eq_inner hD hB, inner_add_left] at hU hV ⊢
    exact congrArg₂ (fun a b : ℝ => a + b) hU hV
  · simp only [hj, if_neg, ite_false, Prod.snd_add] at hU hV ⊢
    simp only [hU.1, hU.2, hV.1, hV.2, add_zero, and_self]

theorem matchingModeRow_smul {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F : RadialModePair D}
    (hU : if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * U.1 r) = F.2
      else U.2 = 0 ∧ F.2 = 0) (c : ℝ) :
    if j = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (c • U).1 r) = (c • F).2
      else (c • U).2 = 0 ∧ (c • F).2 = 0 := by
  by_cases hj : j = 2
  · simp only [hj, if_pos, ite_true, Prod.smul_fst, Prod.smul_snd,
      matchingColumn_integral_eq_inner hD hB, real_inner_smul_left, smul_eq_mul] at hU ⊢
    exact congrArg (fun a : ℝ => c * a) hU
  · simp only [hj, if_neg, ite_false, Prod.smul_snd, smul_eq_mul] at hU ⊢
    simp only [hU.1, hU.2, mul_zero, and_self]

theorem modeFullGraph_zero {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (j : ℕ) : ModeFullGraph D j 0 0 := by
  refine ⟨modeLocalEquation_zero hD j (radialCore D), ?_⟩
  simpa only [Prod.fst_zero, Prod.snd_zero] using matchingModeRow_zero hD hB j

theorem modeFullGraph_add {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F V H : RadialModePair D}
    (hU : ModeFullGraph D j U F) (hV : ModeFullGraph D j V H) :
    ModeFullGraph D j (U + V) (F + H) :=
  ⟨modeLocalEquation_add hD hU.1 hV.1, matchingModeRow_add hD hB hU.2 hV.2⟩

theorem modeFullGraph_smul {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F : RadialModePair D}
    (hU : ModeFullGraph D j U F) (c : ℝ) :
    ModeFullGraph D j (c • U) (c • F) :=
  ⟨modeLocalEquation_smul hD hU.1 c, matchingModeRow_smul hD hB hU.2 c⟩

theorem modeFullGraph_neg {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F : RadialModePair D}
    (hU : ModeFullGraph D j U F) : ModeFullGraph D j (-U) (-F) := by
  simpa only [neg_one_smul] using modeFullGraph_smul hD hB hU (-1)

theorem modeFullGraph_sub {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {j : ℕ} {U F V H : RadialModePair D}
    (hU : ModeFullGraph D j U F) (hV : ModeFullGraph D j V H) :
    ModeFullGraph D j (U - V) (F - H) := by
  simpa only [sub_eq_add_neg] using
    modeFullGraph_add hD hB hU (modeFullGraph_neg hD hB hV)

theorem modeInnerDirichletGraph_zero {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) (M : RadialMatchingData D) :
    ModeInnerDirichletGraph D M 0 0 := by
  refine ⟨modeLocalEquation_zero hD M.frequency (Ioo M.innerLeft M.innerRight),
    ?_, 0, ?_, contDiffOn_const, ?_, ?_, ?_⟩
  · simpa only [Prod.fst_zero, Prod.snd_zero] using
      matchingModeRow_zero hD hB M.frequency
  · simpa only [Prod.fst_zero] using
      (Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D) : ⇑(0 : RadialModeL2 D) =ᵐ[radialHilbertMeasure D] 0)
  · intro r hr
    rfl
  · rfl
  · rfl

theorem modeInnerDirichletGraph_add {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {M : RadialMatchingData D} {U F V H : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) (hV : ModeInnerDirichletGraph D M V H) :
    ModeInnerDirichletGraph D M (U + V) (F + H) := by
  rcases hU.2.2 with ⟨u, hu, hcu, hou, hlu, hru⟩
  rcases hV.2.2 with ⟨v, hv, hcv, hov, hlv, hrv⟩
  refine ⟨modeLocalEquation_add hD hU.1 hV.1,
    matchingModeRow_add hD hB hU.2.1 hV.2.1,
    (fun r => u r + v r), ?_, hcu.add hcv, ?_, ?_, ?_⟩
  · simp only [Prod.fst_add]
    filter_upwards [Lp.coeFn_add U.1 V.1, hu, hv] with r hsum hur hvr
    simpa only [Pi.add_apply, hur, hvr] using hsum
  · intro r hr
    simp only [hou r hr, hov r hr, add_zero]
  · simp only [hlu, hlv, add_zero]
  · simp only [hru, hrv, add_zero]

theorem modeInnerDirichletGraph_smul {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {M : RadialMatchingData D} {U F : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) (c : ℝ) :
    ModeInnerDirichletGraph D M (c • U) (c • F) := by
  rcases hU.2.2 with ⟨u, hu, hcu, hou, hlu, hru⟩
  refine ⟨modeLocalEquation_smul hD hU.1 c,
    matchingModeRow_smul hD hB hU.2.1 c,
    (fun r => c * u r), ?_, contDiffOn_const.mul hcu, ?_, ?_, ?_⟩
  · simp only [Prod.smul_fst]
    filter_upwards [Lp.coeFn_smul c U.1, hu] with r hsmul hur
    simpa only [Pi.smul_apply, smul_eq_mul, hur] using hsmul
  · intro r hr
    simp only [hou r hr, mul_zero]
  · simp only [hlu, mul_zero]
  · simp only [hru, mul_zero]

theorem modeInnerDirichletGraph_neg {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {M : RadialMatchingData D} {U F : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) :
    ModeInnerDirichletGraph D M (-U) (-F) := by
  simpa only [neg_one_smul] using modeInnerDirichletGraph_smul hD hB hU (-1)

theorem modeInnerDirichletGraph_sub {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hB : RadialTrueBorder D) {M : RadialMatchingData D} {U F V H : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) (hV : ModeInnerDirichletGraph D M V H) :
    ModeInnerDirichletGraph D M (U - V) (F - H) := by
  simpa only [sub_eq_add_neg] using
    modeInnerDirichletGraph_add hD hB hU (modeInnerDirichletGraph_neg hD hB hV)

end ContinuousFlexibility.Radial
