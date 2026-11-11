import ContinuousFlexibility.Radial.InnerRadialWeakTranspose
import ContinuousFlexibility.Radial.ModeInnerHilbertProjection
import ContinuousFlexibility.Radial.ModeInnerSourcePairing
import ContinuousFlexibility.Radial.ModeWeakRegularity
import ContinuousFlexibility.Radial.ModeWeakGreen
import ContinuousFlexibility.Radial.ModeCoreGraph

/-!
# Classical endpoint values of the actual finite weak graph

The transposed identity already proved for actual matched H¹ fields
allows smooth tests with zero endpoint values and arbitrary endpoint
derivatives. Applied to the C¹ representative furnished by the weak
equation, Green's formula forces both actual endpoint values to vanish.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

theorem innerRadialChain_piece_subset {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (k : Fin (n + 1)) :
    Ioo (G.left k) (G.right k) ⊆ Ioo (G.left 0) (G.right (Fin.last n)) := by
  intro r hr
  exact ⟨(G.increasing.monotone (show (0 : Fin (n + 1)).castSucc ≤ k.castSucc by
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_zero]; omega)).trans_lt hr.1,
    hr.2.trans_le (G.increasing.monotone (show k.succ ≤ (Fin.last n).succ by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_last]; omega))⟩

theorem innerRadialChain_sum_supported {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) (q : Fin (n + 1) → RadialModeL2 D)
    (hq : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → q k r = 0) :
    ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left 0) (G.right (Fin.last n)) → (∑ k, q k) r = 0 := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq]
    with r hsum hr hout
  rw [hsum]
  exact Finset.sum_eq_zero (fun k _ => hr k
    (fun hk => hout (innerRadialChain_piece_subset G k hk)))

private theorem zero_trace_of_transposed {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) {j : ℕ} {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ radialCore D) {U F : RadialModePair D}
    (heq : ModeLocalEquation D j (Ioo a b) U F)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Icc a b))
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → ψ a = 0 → ψ b = 0 →
      (∫ r in a..b, u r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r -
        (U.2 * referenceColumn D r - matchingDensity D r * F.1 r) * ψ r) = 0)
    (i : Fin 2) : u (if i = 0 then a else b) = 0 := by
  let H := innerIntervalAffineLift a b (innerEndpointValues i)
  have hH : ContDiff ℝ ∞ H := innerIntervalAffineLift_contDiff a b (innerEndpointValues i)
  let ψ : ℝ → ℝ := fun x => (x - a) * (b - x) * H x
  have hψ : ContDiff ℝ ∞ ψ :=
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).mul hH
  have hψa : ψ a = 0 := by simp only [ψ, sub_self, zero_mul]
  have hψb : ψ b = 0 := by simp only [ψ, sub_self, mul_zero, zero_mul]
  have hd (x : ℝ) : HasDerivAt ψ
      ((1 * (b - x) + (x - a) * (0 - 1)) * H x +
        ((x - a) * (b - x)) * deriv H x) x :=
    (((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_const x b).sub (hasDerivAt_id x))).mul
        (hH.differentiable (by simp) x).hasDerivAt
  have hends := innerIntervalAffineLift_endpoints hab (innerEndpointValues i)
  have hda : deriv ψ a = (b - a) * innerEndpointValues i 0 := by
    simpa only [sub_self, zero_mul, mul_zero, one_mul, add_zero, H, hends.1] using (hd a).deriv
  have hdb : deriv ψ b = -(b - a) * innerEndpointValues i 1 := by
    simpa only [sub_self, zero_mul, mul_zero, zero_add, sub_zero, zero_sub,
      mul_neg_one, H, hends.2] using (hd b).deriv
  have hg := modeLocalEquation_green_on_compact hD hB heq hrep hab hsub
    (fun _ hx => hx) hu (hψ.of_le (by simp)).contDiffOn
  rw [htest ψ hψ hψa hψb, hψa, hψb,
    (hψ.differentiable (by simp) a).derivWithin (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le)),
    (hψ.differentiable (by simp) b).derivWithin (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le)),
    hda, hdb] at hg
  have hwpos := (matchingProfileGeometry hD).2.2.2.2.1
  have hlen : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  fin_cases i
  · norm_num only [innerEndpointValues, ite_true, ite_false, mul_one, mul_zero,
      zero_mul, sub_zero, zero_sub] at hg ⊢
    have hz : (u a * D.w a) * (b - a) = 0 := by nlinarith only [hg]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hlen)).resolve_right
      (hwpos a (hsub (left_mem_Icc.mpr hab.le))).ne'
  · norm_num only [innerEndpointValues, ite_true, ite_false, mul_one, mul_zero,
      zero_mul, sub_zero, zero_sub] at hg ⊢
    have hz : (u b * D.w b) * (b - a) = 0 := by nlinarith only [hg]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hlen)).resolve_right
      (hwpos b (hsub (right_mem_Icc.mpr hab.le))).ne'

/-- The actual matched weak graph supplies a C¹ representative and the
two ordinary zero boundary values. Neither the frozen equation nor
endpoint values are hypotheses of this theorem. -/
theorem innerRadialChainWeakGraph_dirichlet_representative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n j : ℕ} (G : InnerRadialChainGeometry D n)
    (hab : G.left 0 < G.right (Fin.last n))
    (hsub : Icc (G.left 0) (G.right (Fin.last n)) ⊆ radialCore D)
    {bordered : Bool} {central : Fin (n + 1)} {column : RadialModeL2 D}
    {q : Fin (n + 1) → InnerRadialH1Pair D} {v f : Fin (n + 1) → RadialModeL2 D}
    {c d : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G bordered (j : ℝ)
      central column q v f c d)
    (hf : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → f k r = 0)
    (hcs : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left central) (G.right central) → column r = 0)
    (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r)
    (hg : Function.support (referenceColumn D) ⊆ Ioo (G.left 0) (G.right (Fin.last n))) :
    ∃ u : ℝ → ℝ,
      ((∑ k, (q k).1 : RadialModeL2 D) : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u ∧
      ContDiffOn ℝ 1 u (Icc (G.left 0) (G.right (Fin.last n))) ∧
      (∀ r, r ∉ Icc (G.left 0) (G.right (Fin.last n)) → u r = 0) ∧
      u (G.left 0) = 0 ∧ u (G.right (Fin.last n)) = 0 := by
  let a := G.left 0
  let b := G.right (Fin.last n)
  let U : RadialModePair D := (∑ k, (q k).1, c)
  let F : RadialModePair D := (∑ k, f k, d)
  have heq : ModeLocalEquation D j (Ioo a b) U F :=
    innerRadialChainWeakGraph_modeLocalEquation hD hw G hgraph hf hcs hc
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw.continuous G q).mp hgraph.1
  have hsU : ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → U.1 r = 0 :=
    innerRadialChain_sum_supported G (fun k => (q k).1) (fun k =>
      innerRadialH1Domain_supported D hw.continuous (G.left_pos k) (G.in_core k)
        (G.weight_pos k) (hξ k).1)
  have hsF : ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → F.1 r = 0 :=
    innerRadialChain_sum_supported G f hf
  have hfixU : modeInnerSource D a b U = U :=
    Prod.ext ((modeRegionVector_eq_self_iff D _ measurableSet_Ioo U.1).mpr hsU) rfl
  have hfixF : modeInnerSource D a b F = F :=
    Prod.ext ((modeRegionVector_eq_self_iff D _ measurableSet_Ioo F.1).mpr hsF) rfl
  obtain ⟨r, C, hr, hUr, _, _, _⟩ :=
    modeLocalEquation_contDiff_representative_on_compact hD hB heq hab hsub (fun _ hx => hx)
  have hUrμ : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo a b)] r := by
    rw [innerRadialHilbertMeasure_restrict D measurableSet_Ioo (Ioo_subset_Icc_self.trans hsub)]
    exact (withDensity_absolutelyContinuous _ _).ae_eq hUr
  let u := (Icc a b).indicator r
  have hu : ContDiffOn ℝ 1 u (Icc a b) :=
    hr.contDiffOn.congr (fun x hx => indicator_of_mem hx r)
  have hrep : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u := by
    filter_upwards [ae_imp_of_ae_restrict hUrμ, hsU, matching_ae_ne hD a,
      matching_ae_ne hD b] with x hur hx hxa hxb
    by_cases hxi : x ∈ Icc a b
    · rw [show u x = r x from indicator_of_mem hxi r]
      exact hur ⟨lt_of_le_of_ne hxi.1 hxa.symm, lt_of_le_of_ne hxi.2 hxb⟩
    · rw [show u x = 0 from indicator_of_notMem hxi r]
      exact hx (fun h => hxi (Ioo_subset_Icc_self h))
  have htest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψa : ψ a = 0) (hψb : ψ b = 0) :
      (∫ x in a..b, u x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x -
        (U.2 * referenceColumn D x - matchingDensity D x * F.1 x) * ψ x) = 0 := by
    have he := innerRadialChainWeakGraph_jacobi_integral hD hw G hgraph hf hcs hc hψ hψa hψb
    have hIU : (∫ x in D.a..D.b, U.1 x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x) =
        ∫ x in a..b, u x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x := by
      calc
        _ = ∫ x in a..b, U.1 x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x := by
          simpa only [mul_comm] using modeInnerSource_integral_fixed hD hab.le hsub U hfixU
            (radialJacobi ((j : ℝ) ^ 2) D.w ψ)
        _ = _ := by
          apply matchingSubinterval_congr_ae hD hab.le hsub
          filter_upwards [hrep] with x hx
          rw [hx]
    have hIF : (∫ x in D.a..D.b, matchingDensity D x * F.1 x * ψ x) =
        ∫ x in a..b, matchingDensity D x * F.1 x * ψ x := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        modeInnerSource_integral_fixed hD hab.le hsub F hfixF (fun x => matchingDensity D x * ψ x)
    have hIC : (∫ x in D.a..D.b, referenceColumn D x * ψ x) =
        ∫ x in a..b, referenceColumn D x * ψ x :=
      matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub)
        (fun x hx => hg (mul_ne_zero_iff.mp hx).1)
    change (∫ x in D.a..D.b, U.1 x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x) -
      U.2 * (∫ x in D.a..D.b, referenceColumn D x * ψ x) =
      -(∫ x in D.a..D.b, matchingDensity D x * F.1 x * ψ x) at he
    rw [hIU, hIF, hIC] at he
    have hsub' : Icc a b ⊆ Icc D.a D.b := hsub.trans Ioo_subset_Icc_self
    have hiU := (hu.continuousOn.mul
      ((matchingJacobi_continuousOn hD hψ j).mono hsub')).intervalIntegrable_of_Icc hab.le
    have hiC := (((matchingColumn_continuousOn hD hB).mono hsub').mul
      hψ.continuous.continuousOn).intervalIntegrable_of_Icc hab.le
    have hdens : ContinuousOn (matchingDensity D) (uIcc a b) := by
      rw [uIcc_of_le hab.le]
      exact (matchingDensity_continuousOn hD).mono hsub'
    have hiF := ((matchingMode_intervalIntegrable hD F.1 hab.le hsub).continuousOn_mul
      hdens).mul_continuousOn hψ.continuous.continuousOn
    have hefun : (fun x => u x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x -
        (U.2 * referenceColumn D x - matchingDensity D x * F.1 x) * ψ x) =
      fun x => u x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x -
        (U.2 * (referenceColumn D x * ψ x) - matchingDensity D x * F.1 x * ψ x) := by
      funext x
      ring
    rw [hefun, intervalIntegral.integral_sub hiU ((hiC.const_mul U.2).sub hiF),
      intervalIntegral.integral_sub (hiC.const_mul U.2) hiF, intervalIntegral.integral_const_mul]
    linarith only [he]
  have hends := zero_trace_of_transposed hD hB hab hsub heq hu hrep htest
  refine ⟨u, hrep, hu, (fun x hx => indicator_of_notMem hx r), ?_, ?_⟩
  · simpa only [ite_true] using hends 0
  · simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hends 1

/-- One actual finite weak graph gives the frozen Dirichlet graph for
the same matching data. The only identifications are the physical cuts,
frequency, support geometry, and actual column density. -/
theorem innerRadialChainWeakGraph_frozen {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {M : RadialMatchingData D} {n : ℕ}
    (G : InnerRadialChainGeometry D n)
    (hleft : G.left 0 = M.innerLeft) (hright : G.right (Fin.last n) = M.innerRight)
    (hab : M.innerLeft < M.innerRight)
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (hdis : Pairwise (fun i k : Fin (n + 1) =>
      Disjoint (Ioo (G.left i) (G.right i)) (Ioo (G.left k) (G.right k))))
    {central : Fin (n + 1)} {column : RadialModeL2 D}
    {q : Fin (n + 1) → InnerRadialH1Pair D} {v f : Fin (n + 1) → RadialModeL2 D}
    {c d : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G (decide (M.frequency = 2))
      (M.frequency : ℝ) central column q v f c d)
    (hf : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → f k r = 0)
    (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r)
    (hgs : Function.support (referenceColumn D) ⊆ Ioo (G.left central) (G.right central)) :
    ModeInnerDirichletGraph D M (∑ k, (q k).1, c) (∑ k, f k, d) := by
  have hcs : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left central) (G.right central) → column r = 0 := by
    filter_upwards [hc] with r hr hout
    have hg : referenceColumn D r = 0 := by
      by_contra hn
      exact hout (hgs hn)
    rw [hr, hg, zero_div]
  have habG : G.left 0 < G.right (Fin.last n) := by simpa only [hleft, hright] using hab
  have hsubG : Icc (G.left 0) (G.right (Fin.last n)) ⊆ radialCore D := by
    simpa only [hleft, hright] using hsub
  have hgsG := hgs.trans (innerRadialChain_piece_subset G central)
  obtain ⟨u, hrep, hu, hout, hzeroLeft, hzeroRight⟩ :=
    innerRadialChainWeakGraph_dirichlet_representative hD hB hw G habG hsubG
      hgraph hf hcs hc hgsG
  have heq := innerRadialChainWeakGraph_modeLocalEquation hD hw G hgraph hf hcs hc
  have hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * (∑ k, (q k).1) r) = d
      else c = 0 ∧ d = 0 := by
    have hraw : if M.frequency = 2 then ⟪column, (q central).1⟫_ℝ = d
        else c = 0 ∧ d = 0 := by
      simpa only [decide_eq_true_eq] using hgraph.2.2.1
    by_cases hj : M.frequency = 2
    · rw [if_pos hj]
      obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw.continuous G q).mp hgraph.1
      have hp (k : Fin (n + 1)) (hk : k ≠ central) : ⟪column, (q k).1⟫_ℝ = 0 := by
        rw [L2.inner_def]
        apply integral_eq_zero_of_ae
        filter_upwards [hcs, innerRadialH1Domain_supported D hw.continuous
          (G.left_pos k) (G.in_core k) (G.weight_pos k) (hξ k).1] with r hcol hq
        by_cases hr : r ∈ Ioo (G.left central) (G.right central)
        · have hkr : r ∉ Ioo (G.left k) (G.right k) :=
            fun h => (Set.disjoint_left.mp (hdis hk)) h hr
          rw [hq hkr, inner_zero_right]
        · rw [hcol hr, inner_zero_left]
      calc
        _ = ⟪column, ∑ k, (q k).1⟫_ℝ := (innerRadialColumn_inner_eq hD hc _).symm
        _ = ⟪column, (q central).1⟫_ℝ := by
          rw [inner_sum]
          exact Finset.sum_eq_single central (fun k _ hk => hp k hk)
            (fun hc => (hc (Finset.mem_univ central)).elim)
        _ = d := by simpa only [if_pos hj] using hraw
    · rw [if_neg hj]
      simpa only [if_neg hj] using hraw
  refine ⟨?_, hrow, u, hrep, ?_, ?_, ?_, ?_⟩
  · simpa only [hleft, hright] using heq
  · simpa only [hleft, hright] using hu
  · intro r hr
    apply hout r
    rw [hleft, hright]
    intro hri
    rcases hr with hl | hr
    · exact (not_lt_of_ge hri.1) hl.2
    · exact (not_lt_of_ge hri.2) hr.1
  · simpa only [hleft] using hzeroLeft
  · simpa only [hright] using hzeroRight

end ContinuousFlexibility.Radial
