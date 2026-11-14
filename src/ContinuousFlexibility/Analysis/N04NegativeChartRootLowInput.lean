import ContinuousFlexibility.Analysis.N04NegativeChartRootLowCoefficients
import ContinuousFlexibility.Analysis.N04NegativeChartRootLowFlow
import ContinuousFlexibility.Analysis.N04NegativeChartRootPositiveBand
import ContinuousFlexibility.Analysis.N01RootLabelUniformJets
import ContinuousFlexibility.Analysis.RootFieldLocalization
import ContinuousFlexibility.Analysis.RootRescaledFieldJets

/-! The genuine same-family input bound for the actual positive root band. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

namespace N04RealizationStart

theorem negativeRootLabel_low_displacement (W : N04RealizationStart) :
    ∃ b : ℕ, ∃ ε L : ℝ, W.base ≤ b ∧ 0 < ε ∧ ε ≤ W.ε ∧ 1 ≤ L ∧
      ∀ z ∈ stateNeighborhood W.S W.C b ε, stateSector W.S z.1 →
      ∀ m side j, j ≤ 2 → ∀ θ,
        ‖iteratedFDeriv ℝ j (fun η => n01RootLabel W.S W.C z m side η - η) θ‖ ≤ L := by
  have hflowData := exists_ordinaryFlowJacobianBounds_of_n01 W.hT W.through03.1.1
  let b₀ := hflowData.choose
  let ε₀ := hflowData.choose_spec.choose
  have hs := hflowData.choose_spec.choose_spec
  have hb₀ := hs.1
  have hε₀ := hs.2.1
  have hεold := hs.2.2.1
  have hflow := hs.2.2.2
  have hN := n01Properties_mono W.hT W.through03.1.1 hb₀ le_rfl hεold hε₀
  have hlabels := n01_rootLabels_displacement_uniform W.hS W.hT hN hflow
  let low := hlabels.choose
  let loss := hlabels.choose_spec.choose
  let B := hlabels.choose_spec.choose_spec.choose
  have hB := hlabels.choose_spec.choose_spec.choose_spec.1
  have hb := hlabels.choose_spec.choose_spec.choose_spec.2
  let b := max b₀ (max low (2 + loss))
  let ε := min ε₀ (1 / 2 : ℝ)
  let L := 1 + 2 * ∑ j : Fin 3, B j.val
  have hsum : 0 ≤ ∑ j : Fin 3, B j.val := Finset.sum_nonneg (fun j _ => (hB j.val).le)
  refine ⟨b, ε, L, hb₀.trans (le_max_left _ _), lt_min hε₀ (by norm_num),
    (min_le_left _ _).trans hεold, by dsimp only [L]; linarith only [hsum], ?_⟩
  intro z hz hs m side j hj θ
  have hgrade {n : ℕ} (hn : n ≤ b) :
      pairGrading (stateGrading W.S) realGrading n (z - (W.C.referenceState, 0)) ≤ 1 := by
    have hh := stateNeighborhood_pairGrading_lt W.S W.C hn hz
    have he : ε ≤ 1 / 2 := min_le_right _ _
    linarith only [hh, he]
  have hh := hb m z (stateNeighborhood_mono W.S W.C (le_max_left _ _) (min_le_left _ _) hz)
    hs (hgrade ((le_max_left _ _).trans (le_max_right _ _))) side j θ
  have hBj : B j ≤ ∑ i : Fin 3, B i.val :=
    Finset.single_le_sum (fun i _ => (hB i.val).le)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin 3))
  have hg := hgrade (n := j + loss)
    ((Nat.add_le_add_right hj loss).trans ((le_max_right _ _).trans (le_max_right _ _)))
  exact hh.trans ((mul_le_mul_of_nonneg_left (by linarith only [hg] :
    1 + pairGrading (stateGrading W.S) realGrading (j + loss)
      (z - (W.C.referenceState, 0)) ≤ 2) (hB j).le).trans
      (by dsimp only [L]; linarith only [hBj]))

namespace NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : NegativeOpticalFactors W e} {base loss : ℕ}

/-- The actual root input has a sampled material C² bound. The sole
scale inequality concerns the already proved original coefficient bound. -/
theorem FullHalfFieldPowerControl.root_low_input
    (Q : F.FullHalfFieldPowerControl base loss) :
    ∃ b : ℕ, ∃ ε C B p : ℝ,
      W.base ≤ b ∧ base ≤ b ∧ 0 < ε ∧ ε ≤ W.ε ∧ 1 ≤ C ∧ 0 < B ∧ 0 < p ∧
      ∀ z ∈ stateNeighborhood W.S W.C b ε, stateSector W.S z.1 →
      ∀ m side, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ W.negativeOpticalWidth m side →
        4 * δ * (C * W.T.E0 (W.negativeHalfSample e m side) ^ C) ≤ 1 →
      ∀ n : ℕ, ∀ d c : (Fin n → ℝ) × PolarPoint → ℝ,
        ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
        (∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi) →
        (∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi) →
      ∀ A : NegativeChartRootFlowData d c δ, ∀ y,
        (∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
          d (y, q) = F.fullHalfDrift z m side q ∧ c (y, q) = F.fullHalfSpeed z m side q) →
        (∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox → 0 ≤ q.1.1 →
          ∀ t ∈ Icc (0 : ℝ) 1,
            |deriv (fun η => rootRescaledField (fun p => d (y, p))
              (fun p => c (y, p)) δ (t, (q.1, η))) q.2| ≤ 1) ∧
        CSBound 2 (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi)
          (W.negativeRootInverseCoordinate A z m side y)
          (B * W.T.E0 (W.negativeHalfSample e m side) ^ p) := by
  have hcoefficients := Q.root_low_coefficients
  let C₀ := hcoefficients.choose
  have hC₀ := hcoefficients.choose_spec.1
  have hcoef := hcoefficients.choose_spec.2
  have hlabels := W.negativeRootLabel_low_displacement
  let bL := hlabels.choose
  let εL := hlabels.choose_spec.choose
  let L := hlabels.choose_spec.choose_spec.choose
  have hs := hlabels.choose_spec.choose_spec.choose_spec
  have hbL := hs.1
  have hεL := hs.2.1
  have hεLW := hs.2.2.1
  have hL := hs.2.2.2.1
  have hlabel := hs.2.2.2.2
  have hflowData := n04NegativeChart_normalized_flow_low
  let Cf := hflowData.choose
  let ef := hflowData.choose_spec.choose
  have hCf := hflowData.choose_spec.choose_spec.1
  let K : ℝ := 1 + ∑ j : Fin 3, 4 * linearWeightedCompositionJetConstant j.val
  have hKn (j : ℕ) : 0 ≤ 4 * linearWeightedCompositionJetConstant j :=
    mul_nonneg (by norm_num) (zero_le_one.trans (one_le_linearWeightedCompositionJetConstant j))
  have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hKn j.val))
  have hjK (j : ℕ) (hj : j ≤ 2) : 4 * linearWeightedCompositionJetConstant j ≤ K :=
    (Finset.single_le_sum (fun i _ => hKn i.val)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin 3))).trans (le_add_of_nonneg_left zero_le_one)
  let E : ℕ × Bool → ℝ := fun i => W.T.E0 (W.negativeHalfSample e i.1 i.2)
  let M : ℕ × Bool → ℝ := fun i => (K * C₀ + L + 1) * E i ^ C₀
  have hE (i) : 1 ≤ E i := W.floor _
  have hM (i) : 1 ≤ M i := by
    have he := Real.one_le_rpow (hE i) (zero_le_one.trans hC₀)
    have hc : 1 ≤ K * C₀ + L + 1 := by
      have hh := one_le_mul_of_one_le_of_one_le hK hC₀
      linarith only [hh, hL]
    exact one_le_mul_of_one_le_of_one_le hc he
  have henv : HasPositiveEnvelope E M :=
    ⟨K * C₀ + L + 1, C₀, by have hc := hC₀; have hk := hK; have hl := hL; positivity,
      zero_lt_one.trans_le hC₀, fun _ => le_rfl⟩
  have hbound := negativeChartLowInputBound_envelope hE hM henv Cf hCf ef
  let B := hbound.choose
  let p := hbound.choose_spec.choose
  have hB := hbound.choose_spec.choose_spec.1
  have hp := hbound.choose_spec.choose_spec.2.1
  have hpack := hbound.choose_spec.choose_spec.2.2
  let b := max bL (max base (2 + loss))
  let ε := min εL W.negativeHalfStateRadius
  have hε : 0 < ε := lt_min hεL (lt_min (by linarith only [W.ε_pos]) (by norm_num))
  refine ⟨b, ε, C₀, B, p, hbL.trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _), hε,
    (min_le_left _ _).trans hεLW, hC₀, hB, hp, ?_⟩
  intro z hz hs m side δ hδ hδone hδw hsmall n d c hd hc hdp hcp A y heq
  have hdz : ContDiff ℝ ∞ (fun q => d (y, q)) := hd.comp (contDiff_const.prodMk contDiff_id)
  have hcz : ContDiff ℝ ∞ (fun q => c (y, q)) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hzbase := stateNeighborhood_mono W.S W.C
    ((le_max_left _ _).trans (le_max_right _ _)) (min_le_right _ _) hz
  have hlow : pairGrading (stateGrading W.S) realGrading (max base (2 + loss))
      (z - (W.C.referenceState, 0)) ≤ 1 := by
    have hg := stateNeighborhood_pairGrading_lt W.S W.C (le_max_right _ _) hz
    have he : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hg, he]
  have hbcoef := hcoef z hzbase hlow m side (fun q => d (y, q)) (fun q => c (y, q))
    hdz hcz (fun q hq => (heq q (Ioo_subset_Icc_self hq.1)).1)
      (fun q hq => (heq q (Ioo_subset_Icc_self hq.1)).2)
  let R := rootRescaledField (fun q => d (y, q)) (fun q => c (y, q)) δ
  have hR : ContDiff ℝ ∞ R := contDiff_rootRescaledField hdz hcz δ
  have hRp := rootRescaledField_periodic (d := fun p => d (y, p))
    (c := fun p => c (y, p)) (T := Real.pi) (hdp y) (hcp y) δ
  have hpoint {q : N04FlowPoint} (hq : q.1 ∈ n04FlowParameterBox) (hx : 0 ≤ q.1.1)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      δ * q.1.1 * t ^ 2 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) := by
    refine ⟨mul_nonneg (mul_nonneg hδ.le hx) (sq_nonneg t), ?_⟩
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    exact ((mul_le_mul (mul_le_mul_of_nonneg_left hq.1.2 hδ.le) ht2
      (sq_nonneg t) (by positivity)).trans_eq (by ring : δ * 1 * 1 = δ)).trans hδw
  have hmat : 0 ≤ C₀ * E (m, side) ^ C₀ := mul_nonneg (zero_le_one.trans hC₀)
    (Real.rpow_nonneg (zero_le_one.trans (hE _)) _)
  have hraw (j : ℕ) (hj : j ≤ 2) (q : N04FlowPoint)
      (hq : q.1 ∈ n04FlowParameterBox) (hx : 0 ≤ q.1.1) (t : ℝ) (ht : t ∈ Icc 0 1) :
      ‖iteratedFDeriv ℝ j (fun v => R (t, v)) q‖ ≤ M (m, side) := by
    have hb := rootRescaledField_jet_le hdz hcz hδ.le hδone hmat ht hq j
      (fun k hk => (hbcoef k (hk.trans hj) _ (hpoint hq hx ht)).1)
      (fun k hk => (hbcoef k (hk.trans hj) _ (hpoint hq hx ht)).2)
    apply hb.trans ((mul_le_mul_of_nonneg_right (hjK j hj) hmat).trans ?_)
    calc
      _ = (K * C₀) * E (m, side) ^ C₀ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hL])
        (Real.rpow_nonneg (zero_le_one.trans (hE _)) _)
  have hangle (q : N04FlowPoint) (hq : q.1 ∈ n04FlowParameterBox) (hx : 0 ≤ q.1.1)
      (t : ℝ) (ht : t ∈ Icc 0 1) : |deriv (fun η => R (t, (q.1, η))) q.2| ≤ 1 :=
    (rootRescaledField_angular_deriv_le_at hdz hcz hδ.le hmat ht hq q.2
      ((abs_deriv_angular_le_first_frechet hdz _ _).trans
        (hbcoef 1 (by omega) _ (hpoint hq hx ht)).1)
      ((abs_deriv_angular_le_first_frechet hcz _ _).trans
        (hbcoef 1 (by omega) _ (hpoint hq hx ht)).2)).trans hsmall
  have hzL := stateNeighborhood_mono W.S W.C (le_max_left _ _) (min_le_left _ _) hz
  have hzold := stateNeighborhood_mono W.S W.C hbL hεLW hzL
  have hb := hflowData.choose_spec.choose_spec.2 (M := M (m, side))
    (hM (m, side)) (n04FlowReverseField R)
    (n04FlowReverseField_contDiff hR) (n04FlowReverseField_periodic hRp)
    (fun q hq hx t ht => by
      change |deriv (fun η => -R (1 - t, (q.1, η))) q.2| ≤ 1
      rw [deriv.fun_neg, abs_neg]
      exact hangle q hq hx (1 - t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩)
    (fun j hj q hq hx t ht => by
      change ‖iteratedFDeriv ℝ j (-(fun v => R (1 - t, v))) q‖ ≤ _
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hraw j hj q hq hx (1 - t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩)
    (A.inverse y) (A.inverse_equations y) (n01RootLabel W.S W.C z m side)
    (n01RootLabel_contDiff W.hS W.hT W.through03.1.1 hzold hs m side)
    (fun j hj θ => (hlabel z hzL hs m side j hj θ).trans (by
      have hk := mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hC₀)
      exact (show L ≤ K * C₀ + L + 1 by linarith only [hk]).trans
        (le_mul_of_one_le_right (by positivity)
          (Real.one_le_rpow (hE (m, side)) (zero_le_one.trans hC₀)))))
    (Real.sqrt δ) (by simpa only [one_mul] using
      abs_signed_sqrt_le_one hδ.le hδone (Or.inl (rfl : (1 : ℝ) = 1)))
  have he : W.negativeRootInverseCoordinate A z m side y =
      n01RootLabel W.S W.C z m side ∘
        ((fun q : N04FlowPoint => A.inverse y q.1 1 q.2) ∘
          rootFlowNormalizedArgument (Real.sqrt δ)) := by
    funext q
    simp only [negativeRootInverseCoordinate, Function.comp_apply, rootFlowNormalizedArgument_apply]
  refine ⟨hangle, ?_⟩
  rw [he]
  exact hb.mono_bound (hpack (m, side))

end NegativeOpticalFactors
end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.root_low_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.root_low_input
