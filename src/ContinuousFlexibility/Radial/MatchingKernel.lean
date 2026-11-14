module

public import ContinuousFlexibility.Radial.MatchingOuterDecomposition
public import ContinuousFlexibility.Radial.MatchingBoundaryAlgebra
public import ContinuousFlexibility.Radial.MatchingInverseFormula
public import ContinuousFlexibility.Radial.ModeWeakRegularity
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Triviality of the full matched modal kernel

A homogeneous full graph has a single C1 representative on the positive
radial core. The exact local inverse decompositions express its two
restrictions in the Poisson columns. Continuity and the common flux at
the cuts give the homogeneous matching matrix equation. A left inverse
of that matrix therefore forces the full mode pair to vanish.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem matching_restrict_ae_iff {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {J : Set ℝ}
    (hJ : MeasurableSet J) (hsub : J ⊆ radialCore D) {p : ℝ → Prop} :
    (∀ᵐ r ∂(radialHilbertMeasure D).restrict J, p r) ↔
      ∀ᵐ r ∂volume.restrict J, p r := by
  constructor
  · intro h
    have hc := (radialHilbertMeasure_ae_iff hD).mp (ae_imp_of_ae_restrict h)
    have hj := ae_restrict_of_ae_restrict_of_subset hsub hc
    filter_upwards [hj, ae_restrict_mem hJ] with r hp hr
    exact hp hr
  · intro h
    have hc : ∀ᵐ r ∂volume.restrict (radialCore D), r ∈ J → p r :=
      ae_restrict_of_ae (ae_imp_of_ae_restrict h)
    have hμ := (radialHilbertMeasure_ae_iff hD).mpr hc
    filter_upwards [ae_restrict_of_ae hμ, ae_restrict_mem hJ] with r hp hr
    exact hp hr

theorem matching_inner_eqOn_of_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Icc M.innerLeft M.innerRight))
    (hv : ContinuousOn v (Icc M.innerLeft M.innerRight))
    (h : u =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] v) :
    EqOn u v (Icc M.innerLeft M.innerRight) := by
  have hvol := (matching_restrict_ae_iff hD measurableSet_Ioo
    (matchingInnerRegion_subset_radialCore ha hb)).mp h
  have heq := Measure.eqOn_open_of_ae_eq hvol isOpen_Ioo
    (hu.mono Ioo_subset_Icc_self) (hv.mono Ioo_subset_Icc_self)
  exact heq.of_subset_closure hu hv Ioo_subset_Icc_self (closure_Ioo hm.ne).symm.subset

theorem matching_outer_eqOn_of_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {M : RadialMatchingData D}
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) {u v : ℝ → ℝ}
    (hu : ContinuousOn u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (hv : ContinuousOn v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    (h : u =ᵐ[(radialHilbertMeasure D).restrict (matchingOuterRegion D M)] v) :
    EqOn u v (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
  have hmeas : MeasurableSet (matchingOuterRegion D M) :=
    measurableSet_Ioo.union measurableSet_Ioo
  have hopen : IsOpen (matchingOuterRegion D M) := isOpen_Ioo.union isOpen_Ioo
  have hsub : matchingOuterRegion D M ⊆ Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b := by
    rintro r (hL | hR)
    · exact Or.inl ⟨hL.1, hL.2.le⟩
    · exact Or.inr ⟨hR.1.le, hR.2⟩
  have hclosure : Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b ⊆
      closure (matchingOuterRegion D M) := by
    rw [matchingOuterRegion_closure ha hb]
    rintro r (hL | hR)
    · exact Or.inl ⟨hL.1.le, hL.2⟩
    · exact Or.inr ⟨hR.1, hR.2.le⟩
  have hvol := (matching_restrict_ae_iff hD hmeas
    (matchingOuterRegion_subset_radialCore ha hm hb)).mp h
  have heq := Measure.eqOn_open_of_ae_eq hvol hopen (hu.mono hsub) (hv.mono hsub)
  exact heq.of_subset_closure hu hv hsub hclosure

theorem matching_modeFullGraph_kernel_eq_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b) (hscale : ∀ i, 0 < M.boundaryScale i)
    (hdiag : ∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0)
    (hnorm : ∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1)
    (hcolumn : Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight)
    (Kinv : RadialMatrix)
    (hKleft : radialMatrixProduct Kinv
      (fun i j => radialMatrixProduct M.A M.Db i j - M.B i j) = radialMatrixIdentity)
    {U : RadialModePair D} (hU : ModeFullGraph D M.frequency U 0) :
    U = 0 := by
  classical
  obtain ⟨u, hreg, _, hu⟩ := modeLocalEquation_contDiffOn_representative hD hB hU.1
  let x : Fin 2 → ℝ := fun i => Real.sqrt (M.boundaryScale i) * u (matchingCut D M i)
  let y : Fin 2 → ℝ := fun i =>
    M.A i i * Real.sqrt (M.boundaryScale i) * u (matchingCut D M i) +
      M.B i i * matchingOuterFlux D M u i
  let P : RadialModePair D := ∑ i, x i • M.innerPoisson i
  let Q : RadialModePair D := ∑ i, y i • M.outerPoisson i
  let p : ℝ → ℝ := fun r => ∑ i, x i * M.innerFunction i r
  let q : ℝ → ℝ := fun r => ∑ i, y i * M.outerFunction i r
  have hdata := hM.2.2.2.2.2
  have hI0 : M.sourceInner (0 : RadialModePair D) = 0 := by
    simpa only [matchingSourceInnerCLM_apply] using (matchingSourceInnerCLM D M hM).map_zero
  have hO0 : M.sourceOuter (0 : RadialModePair D) = 0 := by
    simpa only [matchingSourceOuterCLM_apply] using (matchingSourceOuterCLM D M hM).map_zero
  have hUI : M.sourceInner U = P := by
    have hi := matching_innerInverse_source_eq_sub_poisson hD hB hM ha hm hb hscale
      hcolumn hU hreg hu
    have hz : (0 : RadialModePair D) = M.sourceInner U - P := by
      simpa only [hI0, map_zero] using hi
    exact sub_eq_zero.mp hz.symm
  have hUO : M.sourceOuter U = Q := by
    have ho := matching_outerInverse_source_eq_sub_poisson hD hM ha hm hb hscale hdiag hnorm
      hcolumn hU hreg hu
    have hz : (0 : RadialModePair D) = M.sourceOuter U - Q := by
      simpa only [hO0, map_zero] using ho
    exact sub_eq_zero.mp hz.symm
  have hpi : ∀ i, ContDiffOn ℝ 1 (M.innerFunction i) (Icc M.innerLeft M.innerRight) :=
    fun i => (hdata i).2.2.2.2.1.of_le (by norm_num)
  have hqi : ∀ i, ContDiffOn ℝ 1 (M.outerFunction i)
      (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) :=
    fun i => (hdata i).2.2.2.2.2.1.of_le (by norm_num)
  have hp : ContDiffOn ℝ 1 p (Icc M.innerLeft M.innerRight) :=
    ContDiffOn.sum (fun i _ => contDiffOn_const.mul (hpi i))
  have hq : ContDiffOn ℝ 1 q (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) :=
    ContDiffOn.sum (fun i _ => contDiffOn_const.mul (hqi i))
  have huI : ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight) :=
    hreg.mono (fun r hr => ⟨lt_of_lt_of_le ha hr.1, lt_of_le_of_lt hr.2 hb⟩)
  have huO : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b) := by
    apply hreg.mono
    rintro r (hL | hR)
    · exact ⟨hL.1, lt_of_le_of_lt hL.2 (lt_trans hm hb)⟩
    · exact ⟨lt_of_lt_of_le (lt_trans ha hm) hR.1, hR.2⟩
  have hIp : u =ᵐ[(radialHilbertMeasure D).restrict (Ioo M.innerLeft M.innerRight)] p := by
    have hi := (matching_sourceInner_representative hM hu).1
    rw [hUI] at hi
    exact hi.symm.trans (matching_pair_sum_ae_restrict M.innerPoisson M.innerFunction x
      (fun i => (hdata i).1.restrict))
  have hOq : u =ᵐ[(radialHilbertMeasure D).restrict (matchingOuterRegion D M)] q := by
    have ho := (matching_sourceOuter_representative hM hu).1
    rw [hUO] at ho
    exact ho.symm.trans (matching_pair_sum_ae_restrict M.outerPoisson M.outerFunction y
      (fun i => (hdata i).2.1.restrict))
  have hIpClosed := matching_inner_eqOn_of_ae hD ha hm hb huI.continuousOn hp.continuousOn hIp
  have hOqClosed := matching_outer_eqOn_of_ae hD ha hm hb huO.continuousOn hq.continuousOn hOq
  have hzI : ∀ i, matchingInnerFlux D M u i = radialMatrixApply M.Db x i := by
    intro i
    calc
      matchingInnerFlux D M u i = matchingInnerFlux D M p i :=
        matchingInnerFlux_congr hm hIpClosed i
      _ = ∑ k, x k * matchingInnerFlux D M (M.innerFunction k) i :=
        matchingInnerFlux_fun_sum hm x M.innerFunction hpi i
      _ = radialMatrixApply M.Db x i := by
        unfold radialMatrixApply
        apply Finset.sum_congr rfl
        intro k hk
        rw [← ((hdata k).2.2.2.2.2.2.2.2.2.2 i).2.1]
        ring
  have hxA : ∀ i, x i = M.A i i * y i := by
    intro i
    have hsqrt : Real.sqrt (M.boundaryScale i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hscale i))
    calc
      x i = Real.sqrt (M.boundaryScale i) * q (matchingCut D M i) := by
        dsimp only [x]
        rw [hOqClosed (matchingCut_mem_outerOneSided ha hb i)]
      _ = ∑ k, Real.sqrt (M.boundaryScale i) *
          (y k * M.outerFunction k (matchingCut D M i)) := by
        dsimp only [q]
        rw [Finset.mul_sum]
      _ = radialMatrixApply M.A y i := by
        unfold radialMatrixApply
        apply Finset.sum_congr rfl
        intro k hk
        rw [((hdata k).2.2.2.2.2.2.2.2.2.2 i).2.2.1]
        field_simp [hsqrt] <;> ring
      _ = M.A i i * y i :=
        matchedBoundary_apply_diagonal M.A (fun k l h => (hdiag k l h).1) y i
  have hzB : ∀ i, radialMatrixApply M.Db x i = M.B i i * y i := by
    intro i
    calc
      radialMatrixApply M.Db x i = matchingInnerFlux D M u i := (hzI i).symm
      _ = matchingOuterFlux D M u i := matchingInnerFlux_eq_outerFlux ha hm hb hreg i
      _ = matchingOuterFlux D M q i := matchingOuterFlux_congr ha hm hb hOqClosed i
      _ = ∑ k, y k * matchingOuterFlux D M (M.outerFunction k) i :=
        matchingOuterFlux_fun_sum ha hm hb y M.outerFunction hqi i
      _ = radialMatrixApply M.B y i := by
        unfold radialMatrixApply
        apply Finset.sum_congr rfl
        intro k hk
        rw [((hdata k).2.2.2.2.2.2.2.2.2.2 i).2.2.2]
        ring
      _ = M.B i i * y i :=
        matchedBoundary_apply_diagonal M.B (fun k l h => (hdiag k l h).2) y i
  let K : RadialMatrix := fun i j => radialMatrixProduct M.A M.Db i j - M.B i j
  have hKx : ∀ i, radialMatrixApply K x i = 0 := by
    intro i
    change radialMatrixApply (fun k l => radialMatrixProduct M.A M.Db k l - M.B k l) x i = 0
    rw [matchedBoundary_system_apply M.A M.B M.Db hdiag, hzB i, hxA i]
    ring
  have hx0 : x = fun _ => 0 := by
    funext i
    calc
      x i = radialMatrixApply (radialMatrixProduct Kinv K) x i := by
        rw [show radialMatrixProduct Kinv K = radialMatrixIdentity from hKleft,
          matchedBoundary_apply_identity]
      _ = radialMatrixApply Kinv (radialMatrixApply K x) i :=
        matchedBoundary_apply_product Kinv K x i
      _ = 0 := by
        change (∑ k, Kinv i k * radialMatrixApply K x k) = 0
        simp only [hKx, mul_zero, Finset.sum_const_zero]
  have hz0 : ∀ i, matchingOuterFlux D M u i = 0 := by
    intro i
    rw [← matchingInnerFlux_eq_outerFlux ha hm hb hreg i, hzI i, hx0]
    simp only [radialMatrixApply, mul_zero, Finset.sum_const_zero]
  have hy0 : y = fun _ => 0 := by
    funext i
    calc
      y i = M.A i i * x i + M.B i i * matchingOuterFlux D M u i := by
        dsimp only [x, y]
        ring
      _ = 0 := by rw [congrFun hx0 i, hz0 i]; ring
  have hUI0 : M.sourceInner U = 0 := by
    rw [hUI]
    change (∑ i, x i • M.innerPoisson i) = 0
    simp only [hx0, zero_smul, Finset.sum_const_zero]
  have hUO0 : M.sourceOuter U = 0 := by
    rw [hUO]
    change (∑ i, y i • M.outerPoisson i) = 0
    simp only [hy0, zero_smul, Finset.sum_const_zero]
  have hsum := matching_sources_add hM U
  rw [hUI0, hUO0, add_zero] at hsum
  exact hsum.symm

/-- A proved matched representation carries all the hypotheses needed
for uniqueness of the frozen global graph. -/
theorem actualMatchedRepresentation_kernel_eq_zero {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {M : RadialMatchingData D}
    (hA : ActualMatchedRepresentation D G M)
    {U : RadialModePair D} (hU : ModeFullGraph D M.frequency U 0) :
    U = 0 := by
  rcases hA with ⟨ha, hm, hb, hcolumn, _, hscale, _, _, hM, _, hdiag, hnorm,
    hleft, _, _⟩
  exact matching_modeFullGraph_kernel_eq_zero hD hB hM ha hm hb
    (fun i => (hscale i).1) hdiag hnorm hcolumn M.Kinv hleft hU

end ContinuousFlexibility.Radial
