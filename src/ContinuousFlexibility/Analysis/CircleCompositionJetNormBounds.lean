module

public import ContinuousFlexibility.Analysis.CircleFiniteProductBounds
public import ContinuousFlexibility.Analysis.CircleOuterCompositionBounds
public import ContinuousFlexibility.Analysis.CircleJetAssembly
public import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# Uniform projective bounds for the actual composition tower

One low-order box works for the entire directional tower. For each
fixed output and parameter order, a continuous seminorm bounds every
increment homogeneously. The base point enters with affine growth.
-/

@[expose] public section

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

private theorem grading_fst_le_pair
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (q : ℕ → Seminorm ℝ E) (hq : Monotone q) {a b : ℕ} (hab : a ≤ b) (x : E × E) :
    q a x.1 ≤ pairGrading q q b x := by
  rw [pairGrading_apply]
  exact (hq hab x.1).trans (le_add_of_nonneg_right (apply_nonneg _ _))

private theorem grading_snd_le_pair
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (q : ℕ → Seminorm ℝ E) (hq : Monotone q) {a b : ℕ} (hab : a ≤ b) (x : E × E) :
    q a x.2 ≤ pairGrading q q b x := by
  rw [pairGrading_apply]
  exact (hq hab x.2).trans (le_add_of_nonneg_left (apply_nonneg _ _))

private theorem composition_jet_uniform_normBounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (q : ℕ → Seminorm ℝ E) (hmono : Monotone q) (htop0 : WithSeminorms q)
    (outer : ℕ → E → E → E)
    (product : ∀ n : ℕ, E → (Fin n → E) → Finset (Fin n) → E)
    (value : ∀ n : ℕ, E × E → (Fin n → E × E) → E)
    (measure : ∀ n : ℕ, ℕ → E × E → (Fin n → E × E) → ℝ)
    (hOuter : ∃ base : ℕ, ∀ n : ℕ, ∃ loss : ℕ,
      ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ e u : E, q base e ≤ K → q base u ≤ K →
          q s (outer n e u) ≤ C * (1 + q (s + loss) e + q (s + loss) u)) ∧
        (∀ e u : E, q base e ≤ K →
          q s (outer n e u) ≤ C * (1 + q (s + loss) e) * q (s + loss) u))
    (hProduct : ∀ n : ℕ, ∀ I : Finset (Fin n), ∃ loss : ℕ,
      ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v,
        q s (product n u v I) ≤ C * q (s + loss) u * ∏ i ∈ I, q (s + loss) (v i))
    (hFormula : ∀ n x v, value n x v =
      product n (outer n x.1 x.2) (fun i => (v i).1) Finset.univ +
        ∑ i : Fin n, product n (outer (n - 1) x.1 (v i).2)
          (fun j => (v j).1) (Finset.univ.erase i))
    (hMeasure : ∀ n s x v, measure n s x v ≤ q s (value n x v)) :
    ∃ base : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ n s : ℕ,
      ∃ p : Seminorm ℝ (E × E), ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
        ∀ x, pairGrading q q base x < K → ∀ v : Fin n → E × E,
          measure n s x v ≤ B * (1 + p x) * ∏ i, p (v i) := by
  classical
  obtain ⟨base, houter⟩ := hOuter
  let p := pairGrading q q
  have hp := hmono
  have htop := withSeminorms_pairGrading htop0 htop0
  refine ⟨base, ?_⟩
  intro K hK n s
  obtain ⟨ln, hln⟩ := houter n
  obtain ⟨ld, hld⟩ := houter (n - 1)
  obtain ⟨l0, hb0⟩ := hProduct n
    (Finset.univ : Finset (Fin n))
  choose li hbi using fun i : Fin n =>
    hProduct n (Finset.univ.erase i)
  obtain ⟨C0, hC0, hc0⟩ := hb0 s
  choose Ci hCi hci using fun i : Fin n => hbi i s
  obtain ⟨D0, hD0, hd0, _⟩ := hln K hK (s + l0)
  choose Di hDi hdiFull hdi using fun i : Fin n => hld K hK (s + li i)
  let R : ℕ := max (s + l0 + ln) (Finset.univ.sup (fun i : Fin n => s + li i + ld))
  have hR0 : s + l0 + ln ≤ R := le_max_left _ _
  have hRi (i : Fin n) : s + li i + ld ≤ R :=
    (Finset.le_sup (f := fun j : Fin n => s + li j + ld) (Finset.mem_univ i)).trans (le_max_right _ _)
  let B : ℝ := C0 * D0 + ∑ i : Fin n, Ci i * Di i
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hC0 hD0)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hCi i) (hDi i)))
  refine ⟨p R, B, htop.continuous_seminorm R, hB, ?_⟩
  intro x hx v
  have hx0 : q base x.1 ≤ K :=
    (grading_fst_le_pair q hmono le_rfl x).trans hx.le
  have hx1 : q base x.2 ≤ K :=
    (grading_snd_le_pair q hmono le_rfl x).trans hx.le
  have hmain :
      q s (product n
        (outer n x.1 x.2)
        (fun i => (v i).1) Finset.univ) ≤
      (C0 * D0) * (1 + p R x) * ∏ i, p R (v i) := by
    have hou :
        q (s + l0)
          (outer n x.1 x.2) ≤
        D0 * (1 + p R x) := by
      apply (hd0 x.1 x.2 hx0 hx1).trans
      apply mul_le_mul_of_nonneg_left _ hD0
      change 1 + q (s + l0 + ln) x.1 + q (s + l0 + ln) x.2 ≤
        1 + pairGrading q q R x
      rw [pairGrading_apply, ← add_assoc]
      exact add_le_add (add_le_add le_rfl (hp hR0 x.1)) (hp hR0 x.2)
    have hprod : (∏ i : Fin n, q (s + l0) (v i).1) ≤ ∏ i : Fin n, p R (v i) := by
      apply Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _)
      intro i hi
      exact grading_fst_le_pair q hmono (by omega) (v i)
    calc
      _ ≤ C0 *
          q (s + l0)
            (outer n x.1 x.2) *
          ∏ i : Fin n, q (s + l0) (v i).1 := hc0 _ _
      _ ≤ C0 * (D0 * (1 + p R x)) * ∏ i : Fin n, p R (v i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hou hC0) hprod
          (Finset.prod_nonneg (fun i _ => apply_nonneg _ _)) (by positivity)
      _ = _ := by ring
  have hterm (i : Fin n) :
      q s (product n
        (outer (n - 1) x.1 (v i).2)
        (fun j => (v j).1) (Finset.univ.erase i)) ≤
      (Ci i * Di i) * (1 + p R x) * ∏ j, p R (v j) := by
    have hou :
        q (s + li i)
          (outer (n - 1) x.1 (v i).2) ≤
        Di i * (1 + p R x) * p R (v i) := by
      apply (hdi i x.1 (v i).2 hx0).trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (grading_fst_le_pair q hmono (hRi i) x)) (hDi i)
      · exact grading_snd_le_pair q hmono (hRi i) (v i)
      · exact apply_nonneg _ _
      · exact mul_nonneg (hDi i)
          (add_nonneg zero_le_one (apply_nonneg (p R) x))
    have hprod :
        (∏ j ∈ Finset.univ.erase i, q (s + li i) (v j).1) ≤
          ∏ j ∈ Finset.univ.erase i, p R (v j) := by
      apply Finset.prod_le_prod₀ (fun j _ => apply_nonneg _ _)
      intro j hj
      exact grading_fst_le_pair q hmono (by have h := hRi i; omega) (v j)
    calc
      _ ≤ Ci i *
          q (s + li i)
            (outer (n - 1) x.1 (v i).2) *
          ∏ j ∈ Finset.univ.erase i, q (s + li i) (v j).1 := hci i _ _
      _ ≤ Ci i * (Di i * (1 + p R x) * p R (v i)) *
          ∏ j ∈ Finset.univ.erase i, p R (v j) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hou (hCi i)) hprod
          (Finset.prod_nonneg (fun j _ => apply_nonneg _ _))
          (mul_nonneg (hCi i) (mul_nonneg
            (mul_nonneg (hDi i) (add_nonneg zero_le_one (apply_nonneg (p R) x)))
            (apply_nonneg (p R) (v i))))
      _ = (Ci i * Di i) * (1 + p R x) *
          (p R (v i) * ∏ j ∈ Finset.univ.erase i, p R (v j)) := by ring
      _ = _ := congrArg (fun y : ℝ => (Ci i * Di i) * (1 + p R x) * y)
        (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
          (fun j : Fin n => p R (v j)) (Finset.mem_univ i))
  have hvalue :
      q s (value n x v) ≤
        B * (1 + p R x) * ∏ i, p R (v i) := by
    rw [hFormula n x v]
    apply (map_add_le_add (q s) _ _).trans
    apply (add_le_add hmain
      ((composition_seminorm_sum_le (q s) Finset.univ _).trans
        (Finset.sum_le_sum (fun i _ => hterm i)))).trans_eq
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    dsimp [B]
    ring
  exact (hMeasure n s x v).trans hvalue

theorem circleChartCompositionJets_uniform_normBounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ base : ℕ, ∀ K : ℝ, 0 ≤ K →
      CircleJetNormBounds (T := T) (γ := γ)
        (U := {x : S.Space × S.Space | pairGrading S.grading S.grading base x < K})
        (circleChartCompositionJets hS travel) := by
  exact composition_jet_uniform_normBounds S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond)
    (withSeminorms_graded (fun j => S.level j) S.bond)
    (fun n e u => circleOuterJetComposeContinuousLinear hS hT hD hγ travel n e u)
    (fun n u v I => circleFiniteProductWith hS hT hD hγ u v I)
    (circleChartCompositionJetValue hS hT hD hγ travel)
    (fun n s x v => circleNorm T γ s (circleChartCompositionJets hS travel n x v))
    (circleOuterJetCompose_uniform_bounds (D := D) (T := T) (γ := γ) (S := S)
      hS hT hD hγ hinterp travel)
    (fun n I => circleFiniteProductWith_coarse_bound
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp I)
    (fun n x v => rfl)
    (fun n s x v =>
      (congrArg (circleNorm T γ s)
        (circleChartCompositionJetValue_decode (D := D) (T := T) (γ := γ) (S := S)
          hS hT hD hγ travel n x v)).symm.trans_le
        (((circleGrading_le_iff_circleNorm hS s
          (circleChartCompositionJetValue hS hT hD hγ travel n x v)
          (apply_nonneg _ _)).mp le_rfl) s le_rfl))

end ContinuousFlexibility.Statements
