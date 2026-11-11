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

private theorem uniformLowGrowth_of_pair_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (f : E → E → E) (base loss : ℕ)
    (hb : ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p base u ≤ K → p base v ≤ K →
      p s (f u v) ≤ C * (1 + p (s + loss) u + p (s + loss) v)) :
    HasUniformLowGrowth (pairGrading p p) p (fun x : E × E => f x.1 x.2) := by
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb K hK s
  refine ⟨C, hC, fun x hx => ?_⟩
  have hx' : p base x.1 + p base x.2 ≤ K := by
    simpa only [pairGrading_apply] using hx
  have hfst : p base x.1 ≤ K :=
    (le_add_of_nonneg_right (apply_nonneg (p base) x.2)).trans hx'
  have hsnd : p base x.2 ≤ K :=
    (le_add_of_nonneg_left (apply_nonneg (p base) x.1)).trans hx'
  simpa only [pairGrading_apply, add_assoc] using hc x.1 x.2 hfst hsnd

private theorem uniformLowGrowth_outer_of_bounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (outer : ℕ → E → E → E)
    (hb : ∃ base : ℕ, 0 ≤ base ∧ ∀ n : ℕ, ∃ loss : ℕ,
      ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
        p base u ≤ K → p base v ≤ K →
        p s (outer n u v) ≤ C * (1 + p (s + loss) u + p (s + loss) v))
    (n : ℕ) :
    HasUniformLowGrowth (pairGrading p p) p (fun x : E × E => outer n x.1 x.2) := by
  obtain ⟨base, _, hn⟩ := hb
  obtain ⟨loss, hl⟩ := hn n
  exact uniformLowGrowth_of_pair_bounds p (outer n) base loss hl

private theorem uniformLowGrowth_product_of_oneHigh
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (product : E → E → E)
    (hb : ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      p s (product u v) ≤ C * (p (s + loss) u * p base v +
        p base u * p (s + loss) v)) :
    HasUniformLowGrowth (pairGrading p p) p (fun x : E × E => product x.1 x.2) := by
  obtain ⟨base, loss, hb⟩ := hb
  refine ⟨base, loss, fun K hK s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hb s
  have hCK : 0 ≤ C * K := mul_nonneg hC hK
  refine ⟨C * K, hCK, fun x hx => ?_⟩
  have hx' : p base x.1 + p base x.2 ≤ K := by
    simpa only [pairGrading_apply] using hx
  have hfst : p base x.1 ≤ K :=
    (le_add_of_nonneg_right (apply_nonneg (p base) x.2)).trans hx'
  have hsnd : p base x.2 ≤ K :=
    (le_add_of_nonneg_left (apply_nonneg (p base) x.1)).trans hx'
  calc
    p s (product x.1 x.2) ≤ C * (p (s + loss) x.1 * p base x.2 +
        p base x.1 * p (s + loss) x.2) := hc x.1 x.2
    _ ≤ C * (p (s + loss) x.1 * K + K * p (s + loss) x.2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hsnd (apply_nonneg _ _))
        (mul_le_mul_of_nonneg_right hfst (apply_nonneg _ _))) hC
    _ = (C * K) * (p (s + loss) x.1 + p (s + loss) x.2) := by ring
    _ ≤ (C * K) * (1 + pairGrading p p (s + loss) x) := by
      rw [pairGrading_apply]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hCK

private theorem uniformLowGrowth_finiteProduct_of_product
    {X E ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [DecidableEq ι]
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (product : E → E → E) (finiteProduct : E → (ι → E) → Finset ι → E)
    (hempty : ∀ u v, finiteProduct u v ∅ = u)
    (hinsert : ∀ u v I i, i ∉ I →
      finiteProduct u v (insert i I) = product (v i) (finiteProduct u v I))
    (hproduct : HasUniformLowGrowth (pairGrading q q) q
      (fun x : E × E => product x.1 x.2))
    (I : Finset ι) (f : X → E) (g : ι → X → E)
    (hf : HasUniformLowGrowth p q f)
    (hg : ∀ i ∈ I, HasUniformLowGrowth p q (g i)) :
    HasUniformLowGrowth p q (fun x => finiteProduct (f x) (fun i => g i x) I) := by
  classical
  revert hg
  induction I using Finset.induction_on with
  | empty =>
      intro hg
      exact hf.congr (fun x => hempty (f x) (fun i => g i x))
  | @insert i I hi ih =>
      intro hg
      have hprev := ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have hpair := (hg i (Finset.mem_insert_self i I)).prodMk hp hprev
      exact (hproduct.comp hp hpair).congr
        (fun x => hinsert (f x) (fun j => g j x) I i hi)

private theorem uniformLowGrowth_compositionJet_expression
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (q : ℕ → Seminorm ℝ E) (hq : Monotone q)
    (outer : ℕ → E → E → E) (product : E → E → E)
    (finiteProduct : ∀ n : ℕ, E → (Fin n → E) → Finset (Fin n) → E)
    (hempty : ∀ n u v, finiteProduct n u v ∅ = u)
    (hinsert : ∀ n u v I i, i ∉ I →
      finiteProduct n u v (insert i I) = product (v i) (finiteProduct n u v I))
    (houter : ∀ n, HasUniformLowGrowth (pairGrading q q) q
      (fun x : E × E => outer n x.1 x.2))
    (hproduct : HasUniformLowGrowth (pairGrading q q) q
      (fun x : E × E => product x.1 x.2))
    (value : ∀ n : ℕ, E × E → (Fin n → E × E) → E)
    (hvalue : ∀ n x v, value n x v =
      finiteProduct n (outer n x.1 x.2) (fun i => (v i).1) Finset.univ +
        ∑ i : Fin n, finiteProduct n (outer (n - 1) x.1 (v i).2)
          (fun j => (v j).1) (Finset.univ.erase i))
    (n : ℕ) :
    HasUniformLowGrowth (jetGrading (pairGrading q q) n) q
      (fun z : (E × E) × (Fin n → E × E) => value n z.1 z.2) := by
  classical
  let p := pairGrading q q
  have hp : Monotone p := tamePairGrading_monotone hq hq
  have hpj : Monotone (jetGrading p n) := jetGrading_monotone hp n
  have hbase := uniformLowGrowth_jet_base p n
  have hdir (i : Fin n) := uniformLowGrowth_jet_direction p n i
  have hbaseChart := (uniformLowGrowth_pair_fst q q).comp hpj hbase
  have hchart (i : Fin n) := (uniformLowGrowth_pair_fst q q).comp hpj (hdir i)
  have hfield (i : Fin n) := (uniformLowGrowth_pair_snd q q).comp hpj (hdir i)
  have hmain : HasUniformLowGrowth (jetGrading p n) q
      (fun z : (E × E) × (Fin n → E × E) =>
        finiteProduct n (outer n z.1.1 z.1.2) (fun i => (z.2 i).1) Finset.univ) := by
    apply uniformLowGrowth_finiteProduct_of_product (jetGrading p n) q hpj
      product (finiteProduct n) (hempty n) (hinsert n) hproduct Finset.univ
    · exact (houter n).comp hpj hbase
    · intro i hi
      exact hchart i
  have hterm (i : Fin n) : HasUniformLowGrowth (jetGrading p n) q
      (fun z : (E × E) × (Fin n → E × E) =>
        finiteProduct n (outer (n - 1) z.1.1 (z.2 i).2)
          (fun j => (z.2 j).1) (Finset.univ.erase i)) := by
    apply uniformLowGrowth_finiteProduct_of_product (jetGrading p n) q hpj
      product (finiteProduct n) (hempty n) (hinsert n) hproduct (Finset.univ.erase i)
    · exact (houter (n - 1)).comp hpj (hbaseChart.prodMk hpj (hfield i))
    · intro j hj
      exact hchart j
  exact (hmain.add hpj
    (HasUniformLowGrowth.finset_sum hpj Finset.univ (fun i hi => hterm i))).congr
      (fun z => hvalue n z.1 z.2)

theorem uniformLowGrowth_circleOuterJetCompose
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (n : ℕ) :
    HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space =>
        circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2) := by
  exact uniformLowGrowth_outer_of_bounds S.grading
    (fun k e u => circleOuterJetComposeContinuousLinear hS hT hD hγ travel k e u)
    (circleOuterJetCompose_grading_uniform_low_order
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel 0) n

theorem uniformLowGrowth_circleProduct
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space => circleProductBilinear hS hT hD hγ x.1 x.2) := by
  exact uniformLowGrowth_product_of_oneHigh S.grading
    (fun u v => circleProductBilinear hS hT hD hγ u v)
    (circleProduct_oneHigh_bound
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp)

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
  exact uniformLowGrowth_finiteProduct_of_product p S.grading hp
    (fun u v => circleProductBilinear hS hT hD hγ u v)
    (circleFiniteProductWith hS hT hD hγ)
    (circleFiniteProductWith_empty hS hT hD hγ)
    (circleFiniteProductWith_insert hS hT hD hγ)
    (uniformLowGrowth_circleProduct
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp) I f g hf hg

theorem uniformLowGrowth_circleChartCompositionJetValue
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (n : ℕ) :
    HasUniformLowGrowth (jetGrading (pairGrading S.grading S.grading) n) S.grading
      (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
        circleChartCompositionJetValue hS hT hD hγ travel n z.1 z.2) := by
  exact uniformLowGrowth_compositionJet_expression S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (fun k e u => circleOuterJetComposeContinuousLinear hS hT hD hγ travel k e u)
    (fun u v => circleProductBilinear hS hT hD hγ u v)
    (fun k u v I => circleFiniteProductWith hS hT hD hγ u v I)
    (fun k u v => circleFiniteProductWith_empty hS hT hD hγ u v)
    (fun k u v I i hi => circleFiniteProductWith_insert hS hT hD hγ u v I i hi)
    (fun k => uniformLowGrowth_circleOuterJetCompose
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel k)
    (uniformLowGrowth_circleProduct
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp)
    (circleChartCompositionJetValue hS hT hD hγ travel)
    (fun k x v => rfl) n

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
  let h := exists_circleChartComposition_smoothDirections
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  let J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) := h.choose
  have hdecode (n : ℕ) (x : S.Space × S.Space) (v : Fin n → S.Space × S.Space) :
      S.decode (J.D n x v) = circleChartCompositionJets hS travel n x v :=
    h.choose_spec n x v
  refine ⟨J, hdecode, ?_⟩
  intro n
  have hactual (z : (S.Space × S.Space) × (Fin n → S.Space × S.Space)) :
      J.D n z.1 z.2 = circleChartCompositionJetValue hS hT hD hγ travel n z.1 z.2 :=
    hS.2.2.2.2.2.1 ((hdecode n z.1 z.2).trans
      (circleChartCompositionJetValue_decode
        (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel n z.1 z.2).symm)
  exact uniformLowGrowth_multilinear_oneHigh
    (p := pairGrading S.grading S.grading) (q := S.grading) (J.D n)
    ((uniformLowGrowth_circleChartCompositionJetValue
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel n).congr hactual)

end ContinuousFlexibility.Statements
