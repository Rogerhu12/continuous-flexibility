import ContinuousFlexibility.Analysis.TameUniformGrowth
import ContinuousFlexibility.Analysis.CircleOuterCompositionBounds
import ContinuousFlexibility.Analysis.CircleFiniteProductBounds
import ContinuousFlexibility.Analysis.CircleCompositionSmoothDirections

/-!
# Uniform bounded-set estimates for the actual composition tower

The genuine parameter jets are finite sums of actual outer-jet
compositions and products. Their fixed-order estimates retain a low
order and a loss chosen before the size of the bounded low-seminorm
set. Multilinear normalization then gives a homogeneous bound for
arbitrary directions, on the same bounded set of base points.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

local instance circleCompositionUniformBoundsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem uniformLowGrowth_circleOuterJetCompose
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (n : ℕ) :
    HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space =>
        circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2) := by
  let h := circleOuterJetCompose_grading_uniform_low_order hS hT hD hγ hinterp travel 0
  let base : ℕ := h.choose
  let hn := h.choose_spec.2 n
  let loss : ℕ := hn.choose
  have hb := hn.choose_spec
  refine ⟨base, loss, fun K hK s => ?_⟩
  let hc := hb K hK s
  refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
  intro x hx
  have hu := hc.choose_spec.2 x.1 x.2
    ((circleGrading_fst_le_pair le_rfl x).trans hx)
    ((circleGrading_snd_le_pair le_rfl x).trans hx)
  simpa only [pairGrading_apply, add_assoc] using hu

theorem uniformLowGrowth_circleProduct
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space => circleProductBilinear hS hT hD hγ x.1 x.2) := by
  let h := circleFiniteProductWith_local_growth hS hT hD hγ hinterp ({()} : Finset Unit)
  let base : ℕ := h.choose
  let loss : ℕ := h.choose_spec.choose
  have hb := h.choose_spec.choose_spec
  refine ⟨base, loss, fun K hK s => ?_⟩
  let hc := hb K hK s
  refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
  intro x hx
  have heq : circleFiniteProductWith hS hT hD hγ x.1 (fun _ : Unit => x.2) {()} =
      circleProductBilinear hS hT hD hγ x.1 x.2 := by
    apply hS.2.2.2.2.2.1
    rw [circleFiniteProductWith_decode, circleProductBilinear_decode]
    simp only [Finset.prod_singleton]
  have hu := hc.choose_spec.2 x.1 (fun _ : Unit => x.2)
    ((circleGrading_fst_le_pair le_rfl x).trans hx)
    (fun i hi => (circleGrading_snd_le_pair le_rfl x).trans hx)
  simpa only [heq, Finset.sum_singleton, pairGrading_apply, add_assoc] using hu

theorem uniformLowGrowth_circleFiniteProductWith
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p)
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (I : Finset ι)
    {f : X → S.Space} {g : ι → X → S.Space}
    (hf : HasUniformLowGrowth p S.grading f)
    (hg : ∀ i ∈ I, HasUniformLowGrowth p S.grading (g i)) :
    HasUniformLowGrowth p S.grading
      (fun x => circleFiniteProductWith hS hT hD hγ (f x) (fun i => g i x) I) := by
  classical
  revert hg
  induction I using Finset.induction_on with
  | empty =>
      intro hg
      simpa only [circleFiniteProductWith_empty] using hf
  | @insert i I hi ih =>
      intro hg
      have hprev := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have hpair := (hg i (Finset.mem_insert_self i I)).prodMk hp hprev
      have hprod := (uniformLowGrowth_circleProduct hS hT hD hγ hinterp).comp hp hpair
      apply hprod.congr
      intro x
      exact circleFiniteProductWith_insert hS hT hD hγ (f x) (fun j => g j x) I i hi

theorem uniformLowGrowth_circleChartCompositionJetValue
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (n : ℕ) :
    HasUniformLowGrowth (jetGrading (pairGrading S.grading S.grading) n) S.grading
      (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
        circleChartCompositionJetValue hS hT hD hγ travel n z.1 z.2) := by
  classical
  let p := pairGrading S.grading S.grading
  have hm := gradedSeminorm_monotone (fun j => S.level j) S.bond
  have hp : Monotone p := tamePairGrading_monotone hm hm
  have hpj : Monotone (jetGrading p n) := jetGrading_monotone hp n
  have hbase := uniformLowGrowth_jet_base p n
  have hdir (i : Fin n) := uniformLowGrowth_jet_direction p n i
  have hbaseChart := (uniformLowGrowth_pair_fst S.grading S.grading).comp hpj hbase
  have hchart (i : Fin n) :=
    (uniformLowGrowth_pair_fst S.grading S.grading).comp hpj (hdir i)
  have hfield (i : Fin n) :=
    (uniformLowGrowth_pair_snd S.grading S.grading).comp hpj (hdir i)
  have hmain : HasUniformLowGrowth (jetGrading p n) S.grading
      (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
        circleFiniteProductWith hS hT hD hγ
          (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n z.1.1 z.1.2)
          (fun i => (z.2 i).1) Finset.univ) := by
    apply uniformLowGrowth_circleFiniteProductWith hpj hS hT hD hγ hinterp Finset.univ
    · exact (uniformLowGrowth_circleOuterJetCompose hS hT hD hγ hinterp travel n).comp hpj hbase
    · intro i hi
      exact hchart i
  have hterm (i : Fin n) : HasUniformLowGrowth (jetGrading p n) S.grading
      (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
        circleFiniteProductWith hS hT hD hγ
          (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) z.1.1 (z.2 i).2)
          (fun j => (z.2 j).1) (Finset.univ.erase i)) := by
    apply uniformLowGrowth_circleFiniteProductWith hpj hS hT hD hγ hinterp (Finset.univ.erase i)
    · exact (uniformLowGrowth_circleOuterJetCompose hS hT hD hγ hinterp travel (n - 1)).comp
        hpj (hbaseChart.prodMk hpj (hfield i))
    · intro j hj
      exact hchart j
  exact hmain.add hpj (HasUniformLowGrowth.finset_sum hpj Finset.univ (fun i hi => hterm i))

/-- The tower is the actual composition tower. For each parameter order,
its low order and loss work on every bounded low-seminorm set. -/
theorem exists_circleChartComposition_uniform_oneHigh
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2),
      (∀ n x (v : Fin n → S.Space × S.Space),
        S.decode (J.D n x v) = circleChartCompositionJets hS travel n x v) ∧
      ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, pairGrading S.grading S.grading base x ≤ K →
          ∀ v : Fin n → S.Space × S.Space,
            S.grading s (J.D n x v) ≤
              C * tameJetSize (pairGrading S.grading S.grading) n s loss base x v := by
  let h := exists_circleChartComposition_smoothDirections hS hT hD hγ hinterp travel
  let J := h.choose
  have hdecode := h.choose_spec
  refine ⟨J, hdecode, ?_⟩
  intro n
  apply uniformLowGrowth_multilinear_oneHigh (J.D n)
  apply (uniformLowGrowth_circleChartCompositionJetValue hS hT hD hγ hinterp travel n).congr
  intro z
  apply hS.2.2.2.2.2.1
  exact (hdecode n z.1 z.2).trans
    (circleChartCompositionJetValue_decode hS hT hD hγ travel n z.1 z.2).symm

end ContinuousFlexibility.Statements
