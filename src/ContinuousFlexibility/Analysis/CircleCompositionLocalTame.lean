import ContinuousFlexibility.Analysis.CircleCompositionSmoothDirections
import ContinuousFlexibility.Analysis.CircleCompositionUniformBounds
import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# Local tame value calculus for actual circle composition

The low order is selected before the neighborhood radius. All maps in
the estimates are actual circle-model values; finite products are built
with the genuine pointwise multiplication operator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology BigOperators NNReal

section LowGrowth

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

theorem locallyTameOn_of_uniform_low_growth
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (ht : WithSeminorms p)
    {f : E → F} (hc : Continuous f)
    (hb : ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ K → q s (f x) ≤ C * (1 + p (s + loss) x)) :
    LocallyTameOn p q univ f := by
  obtain ⟨base, loss, hb⟩ := hb
  refine ⟨hc.continuousOn, ?_⟩
  intro x₀ hx₀
  let K : ℝ := 1 + p base x₀
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let W : Set E := {x | p base x < K}
  have hW : W ∈ 𝓝 x₀ :=
    (ht.continuous_seminorm base).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by dsimp [K]; linarith))
  refine ⟨loss, base, W, nhdsWithin_le_nhds hW, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hb K hK s
  exact ⟨C, hC, fun x hx => hbound x hx.le⟩

theorem locallyTameOn_of_grading_contraction
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (L : E →L[ℝ] F) (hL : ∀ s x, q s (L x) ≤ p s x) :
    LocallyTameOn p q univ L := by
  refine ⟨L.continuous.continuousOn, fun _ _ => ⟨0, 0, univ, univ_mem, ?_⟩⟩
  intro s hs
  refine ⟨1, zero_le_one, fun x _ => ?_⟩
  simpa only [Nat.add_zero, one_mul] using
    (hL s x).trans (le_add_of_nonneg_left zero_le_one)

theorem locallyTameOn_pair_fst
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    LocallyTameOn (pairGrading p q) p univ (fun z : E × F => z.1) := by
  apply locallyTameOn_of_grading_contraction (pairGrading p q) p
    (ContinuousLinearMap.fst ℝ E F)
  intro s z
  rw [pairGrading_apply]
  exact le_add_of_nonneg_right (apply_nonneg _ _)

theorem locallyTameOn_pair_snd
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) :
    LocallyTameOn (pairGrading p q) q univ (fun z : E × F => z.2) := by
  apply locallyTameOn_of_grading_contraction (pairGrading p q) q
    (ContinuousLinearMap.snd ℝ E F)
  intro s z
  rw [pairGrading_apply]
  exact le_add_of_nonneg_left (apply_nonneg _ _)

theorem locallyTameOn_jet_base
    (p : ℕ → Seminorm ℝ E) (n : ℕ) :
    LocallyTameOn (jetGrading p n) p univ (fun z : E × (Fin n → E) => z.1) := by
  apply locallyTameOn_of_grading_contraction (jetGrading p n) p
    (ContinuousLinearMap.fst ℝ E (Fin n → E))
  intro s z
  rw [jetGrading_apply]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => apply_nonneg _ _))

theorem locallyTameOn_jet_direction
    (p : ℕ → Seminorm ℝ E) (n : ℕ) (i : Fin n) :
    LocallyTameOn (jetGrading p n) p univ (fun z : E × (Fin n → E) => z.2 i) := by
  apply locallyTameOn_of_grading_contraction (jetGrading p n) p
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ E (Fin n → E)))
  intro s z
  rw [jetGrading_apply]
  have hi : p s (z.2 i) ≤ ∑ j : Fin n, p s (z.2 j) :=
    Finset.single_le_sum (f := fun j => p s (z.2 j))
      (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)
  exact hi.trans (le_add_of_nonneg_left (apply_nonneg _ _))

end LowGrowth

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators NNReal

local instance circleCompositionLocalTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem locallyTameOn_circleChartComposition
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    LocallyTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) := by
  let smoothData := exists_circleChartComposition_smoothDirections
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  let J : SmoothDirections univ (fun x : S.Space × S.Space =>
      circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) :=
    smoothData.choose
  have hzero (x : S.Space × S.Space) :
      circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2 =
        circleOuterJetComposeContinuousLinear hS hT hD hγ travel 0 x.1 x.2 := rfl
  have hg : HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2) :=
    (uniformLowGrowth_circleOuterJetCompose hS hT hD hγ hinterp travel 0).congr hzero
  exact locallyTameOn_of_uniform_low_growth
    (pairGrading S.grading S.grading) S.grading
    (withSeminorms_pairGrading
      (withSeminorms_graded (fun j => S.level j) S.bond)
      (withSeminorms_graded (fun j => S.level j) S.bond))
    (continuousOn_univ.mp J.continuousOn) hg

theorem locallyTameOn_circleOuterJetCompose
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (n : ℕ) :
    LocallyTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space =>
        circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2) := by
  let p := pairGrading S.grading S.grading
  let A : (S.Space × S.Space) →L[ℝ] S.Space × S.Space :=
    (ContinuousLinearMap.fst ℝ S.Space S.Space).prod
      ((circleAngularDerivativeIterate hS n).comp (ContinuousLinearMap.snd ℝ S.Space S.Space))
  have hA : IsTameLinear p p A.toLinearMap n 0 := by
    intro s hs
    refine ⟨1, ?_⟩
    intro x
    change S.grading s x.1 + S.grading s (circleAngularDerivativeIterate hS n x.2) ≤
      (1 : ℝ) * (S.grading (s + n) x.1 + S.grading (s + n) x.2)
    simp only [NNReal.coe_one, one_mul]
    exact add_le_add
      (gradedSeminorm_monotone (fun j => S.level j) S.bond (by omega) x.1)
      (circleAngularDerivativeIterate_grading hS n s x.2)
  have ha := locallyTameOn_of_isTameLinear A hA univ
  have h := (locallyTameOn_circleChartComposition hS hT hD hγ hinterp travel).comp ha
    (fun x hx => mem_univ (A x))
  exact h.congr (fun x hx => rfl)

theorem locallyTameOn_circleProduct
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) :
    LocallyTameOn (pairGrading S.grading S.grading) S.grading univ
      (fun x : S.Space × S.Space => circleProductBilinear hS hT hD hγ x.1 x.2) := by
  let smoothData := smoothTameOn_circleProduct
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp
  let J : SmoothDirections univ (fun x : S.Space × S.Space =>
      circleProductBilinear hS hT hD hγ x.1 x.2) := smoothData.choose
  exact locallyTameOn_of_uniform_low_growth
    (pairGrading S.grading S.grading) S.grading
    (withSeminorms_pairGrading
      (withSeminorms_graded (fun j => S.level j) S.bond)
      (withSeminorms_graded (fun j => S.level j) S.bond))
    (continuousOn_univ.mp J.continuousOn)
    (uniformLowGrowth_circleProduct hS hT hD hγ hinterp)

theorem locallyTameOn_circleFiniteProductWith
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) {U : Set X}
    {ι : Type*} [DecidableEq ι]
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (I : Finset ι)
    {f : X → S.Space} {g : ι → X → S.Space}
    (hf : LocallyTameOn p S.grading U f)
    (hg : ∀ i ∈ I, LocallyTameOn p S.grading U (g i)) :
    LocallyTameOn p S.grading U
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
      have hprod := (locallyTameOn_circleProduct hS hT hD hγ hinterp).comp hpair
        (fun x hx => mem_univ _)
      apply hprod.congr
      intro x hx
      exact circleFiniteProductWith_insert hS hT hD hγ (f x) (fun j => g j x) I i hi

end ContinuousFlexibility.Statements
