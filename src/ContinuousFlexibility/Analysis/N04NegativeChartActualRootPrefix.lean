import ContinuousFlexibility.Analysis.N04NegativeChartRootFieldBounds

/-!
# Fixed-base raw prefixes of the actual root flow

Every bound below concerns the retained physical half and the exact
representatives used by the flow factory. The closed time zero is
handled by the zero vector field. No coefficient estimate outside the
positive half or on an arbitrary extension is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private theorem fraction_rpow_eq {R : ℝ} (hR : 0 ≤ R) (n N : ℕ) :
    R ^ ((n : ℝ) / ((N : ℝ) + 1)) =
      (R ^ ((1 : ℝ) / ((N : ℝ) + 1))) ^ n := by
  rw [← Real.rpow_mul_natCast hR ((1 : ℝ) / ((N : ℝ) + 1)) n]
  congr 1
  ring

private theorem envelope_mono {a b E : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) (hE : 1 ≤ E) :
    a * E ^ a ≤ b * E ^ b :=
  mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le hE hab)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hb

namespace N04RealizationStart.NegativeOpticalFactors

set_option backward.isDefEq.respectTransparency true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
  {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : NegativeOpticalFactors W e} {base loss : ℕ}

/-- The genuine root speed has a single low order before all state and
spatial orders. A positive state order retains exactly one height weight. -/
theorem FullHalfFieldPowerControl.actualRootField_prefix
    (A : F.FullHalfFieldPowerControl base loss) :
    ∃ b : ℕ, base ≤ b ∧ ∀ K : ℕ, ∃ shift : ℕ, ∀ s : ℕ,
    ∃ B : ℝ, 0 < B ∧ ∀ m side k, k ≤ K → ∀ j, j ≤ s + 1 →
      ∀ x ∈ stateNeighborhood W.S W.C base W.negativeHalfStateRadius,
        pairGrading (stateGrading W.S) realGrading b (x - (W.C.referenceState, 0)) ≤ 1 →
      ∀ L : P →L[ℝ] (AnnularState W.S × ℝ),
      ∀ d c : P × PolarPoint → ℝ, ContDiff ℝ ∞ d → ContDiff ℝ ∞ c →
      ∀ V : Set P, IsOpen V → (0 : P) ∈ V →
        (∀ y ∈ V, ∀ p ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ,
          d (y, p) = F.fullHalfDrift (x + L y) m side p ∧
          c (y, p) = F.fullHalfSpeed (x + L y) m side p) →
      ∀ v : Fin k → P,
        (∀ a, pairGrading (stateGrading W.S) realGrading b (L (v a)) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
        pairGrading (stateGrading W.S) realGrading (b + s + shift * K + 1)
          (x - (W.C.referenceState, 0)) ≤ R →
        (∀ a, pairGrading (stateGrading W.S) realGrading (b + s + shift * K + 1)
          (L (v a)) ≤ R) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ < W.negativeOpticalWidth m side →
      ∀ q : N04FlowPoint, q.1 ∈ n04FlowParameterBox → 0 < q.1.1 →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
          flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
            (fun a => (v a, (0 : PolarPoint))) (t, y.2)) q‖ ≤
          B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
            parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
            R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  classical
  have hprefix := A.finiteRepresentative_prefix (P := P)
  let b := hprefix.choose
  refine ⟨b, hprefix.choose_spec.1, fun K => ?_⟩
  have hshift := hprefix.choose_spec.2 K
  let shift := hshift.choose
  refine ⟨shift, fun s => ?_⟩
  have hdB := hshift.choose_spec.1 s
  let Cd := hdB.choose
  have hCd := hdB.choose_spec.1
  have hdb := hdB.choose_spec.2
  have hcB := hshift.choose_spec.2 s
  let Cc := hcB.choose
  have hCc := hcB.choose_spec.1
  have hcb := hcB.choose_spec.2
  let C : ℝ := max Cd Cc
  have hC : 0 < C := hCd.trans_le (le_max_left _ _)
  let Croot : ℝ := ∑ i : Fin (s + 2), 4 * linearWeightedCompositionJetConstant i.val
  have hterm (i : Fin (s + 2)) : 0 ≤ 4 * linearWeightedCompositionJetConstant i.val :=
    mul_nonneg (by norm_num) (zero_le_one.trans (one_le_linearWeightedCompositionJetConstant _))
  have hroot (j : ℕ) (hj : j ≤ s + 1) :
      4 * linearWeightedCompositionJetConstant j ≤ Croot :=
    Finset.single_le_sum (f := fun i : Fin (s + 2) =>
      4 * linearWeightedCompositionJetConstant i.val) (fun i _ => hterm i)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (s + 2)))
  have henv := coefficientEnvelope_pack (Croot * C) C
  let B := henv.choose
  have hB := henv.choose_spec.1
  have hpack := henv.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m side k hk j hj x hx hlow L d c hd hc V hV h0 heq v hv R hR hxR hvR
    δ hδ hδone hδwidth q hq hqx t ht
  let E : ℝ := W.T.E0 (W.negativeHalfSample e m side)
  let H : ℝ := parameterHeightWeight
    (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := parameterHeightWeight_nonneg
    (Real.rpow_nonneg (W.hT.2.1 _
      (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _) k
  have hbound0 : 0 ≤ B * E ^ B * H *
      R ^ (((j - 1 + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hB.le
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  by_cases ht0 : t = 0
  · subst t
    have hz : (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootPlotField d c δ) k (0, y.1)
          (fun a => (v a, (0 : PolarPoint))) (0, y.2)) = fun _ => 0 := by
      funext y
      rw [negativeChartRootPlotField_stateJet hd hc]
      simp only [rootRescaledField, rootRegularizedField, zero_pow (by omega : 2 ≠ 0),
        mul_zero, zero_mul, zero_add]
    rw [hz]
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using hbound0
    | succ j => simpa only [iteratedFDeriv_succ_const, norm_zero] using hbound0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
  have hrad : δ * q.1.1 * t ^ 2 < W.negativeOpticalWidth m side := by
    calc
      _ ≤ δ * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hq.1.2 hδ.le) ht2 (sq_nonneg t) (by positivity)
      _ = δ := by ring
      _ < _ := hδwidth
  let p : PolarPoint := (δ * q.1.1 * t ^ 2, q.2)
  have hp : p ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ×ˢ univ :=
    ⟨⟨by dsimp only [p]; positivity, hrad⟩, mem_univ _⟩
  let ρ : ℝ := R ^ ((1 : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hρ : 1 ≤ ρ := Real.one_le_rpow hR (by positivity)
  have hcoefD (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l (negativeChartCoefficientJet d k v) p‖ ≤
        (C * E ^ C) * H * ρ ^ (l - 1 + shift * k) := by
    have h := hdb m side k hk l (hl.trans hj) x hx hlow L d hd V hV h0
      (fun y hy q hq => (heq y hy q hq).1) v hv R hR hxR hvR p hp
    have hh := h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (envelope_mono (le_max_left Cd Cc) hC.le hE) hH)
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
    rw [fraction_rpow_eq (zero_le_one.trans hR) (l - 1 + shift * k) (s + shift * K)] at hh
    exact hh
  have hcoefC (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l (negativeChartCoefficientJet c k v) p‖ ≤
        (C * E ^ C) * H * ρ ^ (l - 1 + shift * k) := by
    have h := hcb m side k hk l (hl.trans hj) x hx hlow L c hc V hV h0
      (fun y hy q hq => (heq y hy q hq).2) v hv R hR hxR hvR p hp
    have hh := h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (envelope_mono (le_max_right Cd Cc) hC.le hE) hH)
      (Real.rpow_nonneg (zero_le_one.trans hR) _))
    rw [fraction_rpow_eq (zero_le_one.trans hR) (l - 1 + shift * k) (s + shift * K)] at hh
    exact hh
  have hraw := negativeChartRootPlotField_stateJet_spatial_le hd hc hδ.le hδone
    (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH hρ
    k j (shift * k) v ht hq hcoefD hcoefC
  have hcost : (4 * linearWeightedCompositionJetConstant j) * (C * E ^ C) ≤ B * E ^ B :=
    (mul_le_mul_of_nonneg_right (hroot j hj)
      (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hE) _))).trans
      ((mul_assoc Croot C (E ^ C)).symm.trans_le (hpack E hE))
  have hh := hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost hH) (pow_nonneg (zero_le_one.trans hρ) _))
  rw [fraction_rpow_eq (zero_le_one.trans hR) (j - 1 + shift * k) (s + shift * K)]
  exact hh

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.actualRootField_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.actualRootField_prefix
