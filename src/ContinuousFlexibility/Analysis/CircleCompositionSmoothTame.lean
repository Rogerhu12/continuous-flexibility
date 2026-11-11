import ContinuousFlexibility.Analysis.CircleCompositionLocalTame

/-!
# Joint smooth tame chart composition in the actual circle space

The genuine projective directional tower is already constructed.
Every one of its actual finite-product expressions is locally tame as
a joint function of the base point and all increments. Homogeneous
multilinear normalization gives precisely the frozen SmoothTameOn
definition with a loss fixed before the output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleCompositionSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem smoothTameOn_circleChartComposition
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) := by
  classical
  let p := pairGrading S.grading S.grading
  have hmono := gradedSeminorm_monotone (fun j => S.level j) S.bond
  have hp : Monotone p := tamePairGrading_monotone hmono hmono
  have ht : WithSeminorms p := withSeminorms_pairGrading
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
  obtain ⟨J, hdecode⟩ := exists_circleChartComposition_smoothDirections
    hS hT hD hγ hinterp travel
  apply smoothTameOn_of_locallyTameOn_jets hp ht J
  intro n
  have hpj : Monotone (jetGrading p n) := jetGrading_monotone hp n
  have hbase := locallyTameOn_jet_base p n
  have hdir (i : Fin n) := locallyTameOn_jet_direction p n i
  have hbaseChart := (locallyTameOn_pair_fst S.grading S.grading).comp hbase
    (fun z hz => mem_univ _)
  have hchart (i : Fin n) := (locallyTameOn_pair_fst S.grading S.grading).comp (hdir i)
    (fun z hz => mem_univ _)
  have hfield (i : Fin n) := (locallyTameOn_pair_snd S.grading S.grading).comp (hdir i)
    (fun z hz => mem_univ _)
  have hmain :
      LocallyTameOn (jetGrading p n) S.grading univ
        (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
          circleFiniteProductWith hS hT hD hγ
            (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n z.1.1 z.1.2)
            (fun i => (z.2 i).1) Finset.univ) := by
    apply locallyTameOn_circleFiniteProductWith hpj hS hT hD hγ hinterp Finset.univ
    · exact (locallyTameOn_circleOuterJetCompose hS hT hD hγ hinterp travel n).comp hbase
        (fun z hz => mem_univ _)
    · intro i hi
      exact hchart i
  have hterm (i : Fin n) :
      LocallyTameOn (jetGrading p n) S.grading univ
        (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
          circleFiniteProductWith hS hT hD hγ
            (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) z.1.1 (z.2 i).2)
            (fun j => (z.2 j).1) (Finset.univ.erase i)) := by
    apply locallyTameOn_circleFiniteProductWith hpj hS hT hD hγ hinterp (Finset.univ.erase i)
    · exact (locallyTameOn_circleOuterJetCompose hS hT hD hγ hinterp travel (n - 1)).comp
        (hbaseChart.prodMk hpj (hfield i)) (fun z hz => mem_univ _)
    · intro j hj
      exact hchart j
  have hsum := LocallyTameOn.finset_sum hpj Finset.univ (fun i hi => hterm i)
  have hvalue := hmain.add hpj hsum
  change LocallyTameOn (jetGrading p n) S.grading univ
    (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
      circleChartCompositionJetValue hS hT hD hγ travel n z.1 z.2) at hvalue
  have hactual :
      LocallyTameOn (jetGrading p n) S.grading univ
        (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
          J.D n z.1 z.2) := by
    apply hvalue.congr
    intro z hz
    apply hS.2.2.2.2.2.1
    exact (hdecode n z.1 z.2).trans
      (circleChartCompositionJetValue_decode hS hT hD hγ travel n z.1 z.2).symm
  simpa only [Set.univ_prod_univ] using hactual

theorem smoothTameOn_circleShiftedChartComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeLinear hS hT hD hγ travel x.1 x.2) := by
  apply smoothTameOn_congr (smoothTameOn_circleChartComposition hS hT hD hγ hinterp travel)
  intro x hx
  exact circleShiftedChartComposeContinuousLinear_apply hS hT hD hγ travel x.1 x.2

end ContinuousFlexibility.Statements
