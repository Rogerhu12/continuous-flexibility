import ContinuousFlexibility.Analysis.CircleFiniteProductBounds
import ContinuousFlexibility.Analysis.CircleOuterCompositionBounds
import ContinuousFlexibility.Analysis.CircleJetAssembly
import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# Uniform projective bounds for the actual composition tower

One low-order box works for the entire directional tower. For each
fixed output and parameter order, a continuous seminorm bounds every
increment homogeneously. The base point enters with affine growth.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

local instance circleCompositionJetNormBoundsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circleGrading_fst_le_pair {a b : ℕ} (hab : a ≤ b) (x : S.Space × S.Space) :
    S.grading a x.1 ≤ pairGrading S.grading S.grading b x := by
  rw [pairGrading_apply]
  exact (gradedSeminorm_monotone (fun j => S.level j) S.bond hab x.1).trans
    (le_add_of_nonneg_right (apply_nonneg _ _))

theorem circleGrading_snd_le_pair {a b : ℕ} (hab : a ≤ b) (x : S.Space × S.Space) :
    S.grading a x.2 ≤ pairGrading S.grading S.grading b x := by
  rw [pairGrading_apply]
  exact (gradedSeminorm_monotone (fun j => S.level j) S.bond hab x.2).trans
    (le_add_of_nonneg_left (apply_nonneg _ _))

private theorem composition_seminorm_sum_le
    {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
    (q : Seminorm ℝ E) (I : Finset ι) (v : ι → E) :
    q (∑ i ∈ I, v i) ≤ ∑ i ∈ I, q (v i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, map_zero, le_refl]
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add q (v i) _).trans (add_le_add le_rfl ih)

private theorem circleChartCompositionJets_normBounds_of_outer_bounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) (base : ℕ)
    (houter : ∀ n : ℕ, ∃ loss : ℕ,
      ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ e u : S.Space, S.grading base e ≤ K → S.grading base u ≤ K →
          S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) ≤
            C * (1 + S.grading (s + loss) e + S.grading (s + loss) u)) ∧
        (∀ e u : S.Space, S.grading base e ≤ K →
          S.grading s (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u) ≤
            C * (1 + S.grading (s + loss) e) * S.grading (s + loss) u)) :
    ∀ K : ℝ, 0 ≤ K →
      CircleJetNormBounds (T := T) (γ := γ)
        (U := {x : S.Space × S.Space | pairGrading S.grading S.grading base x < K})
        (circleChartCompositionJets hS travel) := by
  classical
  let p := pairGrading S.grading S.grading
  have hp := gradedSeminorm_monotone (fun j => S.level j) S.bond
  have htop := withSeminorms_pairGrading
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
  intro K hK n s
  obtain ⟨ln, hln⟩ := houter n
  obtain ⟨ld, hld⟩ := houter (n - 1)
  obtain ⟨l0, hb0⟩ := circleFiniteProductWith_coarse_bound hS hT hD hγ hinterp
    (Finset.univ : Finset (Fin n))
  choose li hbi using fun i : Fin n =>
    circleFiniteProductWith_coarse_bound hS hT hD hγ hinterp (Finset.univ.erase i)
  obtain ⟨C0, hC0, hc0⟩ := hb0 s
  choose Ci hCi hci using fun i : Fin n => hbi i s
  obtain ⟨D0, hD0, hd0, _⟩ := hln K hK (s + l0)
  choose Di hDi hdiFull hdi using fun i : Fin n => hld K hK (s + li i)
  let R : ℕ := max (s + l0 + ln) (Finset.univ.sup (fun i : Fin n => s + li i + ld))
  have hR0 : s + l0 + ln ≤ R := le_max_left _ _
  have hRi (i : Fin n) : s + li i + ld ≤ R :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  let B : ℝ := C0 * D0 + ∑ i : Fin n, Ci i * Di i
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hC0 hD0)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hCi i) (hDi i)))
  refine ⟨p R, B, htop.continuous_seminorm R, hB, ?_⟩
  intro x hx v
  have hx0 : S.grading base x.1 ≤ K :=
    (circleGrading_fst_le_pair le_rfl x).trans hx.le
  have hx1 : S.grading base x.2 ≤ K :=
    (circleGrading_snd_le_pair le_rfl x).trans hx.le
  have hmain :
      S.grading s (circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2)
        (fun i => (v i).1) Finset.univ) ≤
      (C0 * D0) * (1 + p R x) * ∏ i, p R (v i) := by
    have hou :
        S.grading (s + l0)
          (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2) ≤
        D0 * (1 + p R x) := by
      apply (hd0 x.1 x.2 hx0 hx1).trans
      apply mul_le_mul_of_nonneg_left _ hD0
      change 1 + S.grading (s + l0 + ln) x.1 + S.grading (s + l0 + ln) x.2 ≤
        1 + pairGrading S.grading S.grading R x
      rw [pairGrading_apply, ← add_assoc]
      exact add_le_add (add_le_add le_rfl (hp hR0 x.1)) (hp hR0 x.2)
    have hprod : (∏ i : Fin n, S.grading (s + l0) (v i).1) ≤ ∏ i : Fin n, p R (v i) := by
      apply Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
      intro i hi
      exact circleGrading_fst_le_pair (by omega) (v i)
    calc
      _ ≤ C0 *
          S.grading (s + l0)
            (circleOuterJetComposeContinuousLinear hS hT hD hγ travel n x.1 x.2) *
          ∏ i : Fin n, S.grading (s + l0) (v i).1 := hc0 _ _
      _ ≤ C0 * (D0 * (1 + p R x)) * ∏ i : Fin n, p R (v i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hou hC0) hprod
          (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)) (by positivity)
      _ = _ := by ring
  have hterm (i : Fin n) :
      S.grading s (circleFiniteProductWith hS hT hD hγ
        (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) x.1 (v i).2)
        (fun j => (v j).1) (Finset.univ.erase i)) ≤
      (Ci i * Di i) * (1 + p R x) * ∏ j, p R (v j) := by
    have hou :
        S.grading (s + li i)
          (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) x.1 (v i).2) ≤
        Di i * (1 + p R x) * p R (v i) := by
      apply (hdi i x.1 (v i).2 hx0).trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (circleGrading_fst_le_pair (hRi i) x)) (hDi i)
      · exact circleGrading_snd_le_pair (hRi i) (v i)
      · exact apply_nonneg _ _
      · positivity
    have hprod :
        (∏ j ∈ Finset.univ.erase i, S.grading (s + li i) (v j).1) ≤
          ∏ j ∈ Finset.univ.erase i, p R (v j) := by
      apply Finset.prod_le_prod₀ (fun j _ => apply_nonneg _ _)
      intro j hj
      exact circleGrading_fst_le_pair (by have h := hRi i; omega) (v j)
    calc
      _ ≤ Ci i *
          S.grading (s + li i)
            (circleOuterJetComposeContinuousLinear hS hT hD hγ travel (n - 1) x.1 (v i).2) *
          ∏ j ∈ Finset.univ.erase i, S.grading (s + li i) (v j).1 := hci i _ _
      _ ≤ Ci i * (Di i * (1 + p R x) * p R (v i)) *
          ∏ j ∈ Finset.univ.erase i, p R (v j) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hou (hCi i)) hprod
          (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (by positivity)
      _ = (Ci i * Di i) * (1 + p R x) *
          (p R (v i) * ∏ j ∈ Finset.univ.erase i, p R (v j)) := by ring
      _ = _ := by rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hvalue :
      S.grading s (circleChartCompositionJetValue hS hT hD hγ travel n x v) ≤
        B * (1 + p R x) * ∏ i, p R (v i) := by
    unfold circleChartCompositionJetValue
    apply (map_add_le_add (S.grading s) _ _).trans
    apply (add_le_add hmain
      ((composition_seminorm_sum_le (S.grading s) Finset.univ _).trans
        (Finset.sum_le_sum (fun i _ => hterm i)))).trans_eq
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    dsimp [B]
    ring
  have hnorm :
      circleNorm T γ s (circleChartCompositionJets hS travel n x v) ≤
        S.grading s (circleChartCompositionJetValue hS hT hD hγ travel n x v) := by
    rw [← circleChartCompositionJetValue_decode hS hT hD hγ travel n x v]
    exact ((circleGrading_le_iff_circleNorm hS s _ (apply_nonneg _ _)).mp (le_refl _)) s le_rfl
  exact hnorm.trans hvalue

theorem circleChartCompositionJets_uniform_normBounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ base : ℕ, ∀ K : ℝ, 0 ≤ K →
      CircleJetNormBounds (T := T) (γ := γ)
        (U := {x : S.Space × S.Space | pairGrading S.grading S.grading base x < K})
        (circleChartCompositionJets hS travel) := by
  let data := circleOuterJetCompose_uniform_bounds
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  exact ⟨data.choose, circleChartCompositionJets_normBounds_of_outer_bounds
    hS hT hD hγ hinterp travel data.choose data.choose_spec⟩

end ContinuousFlexibility.Statements
