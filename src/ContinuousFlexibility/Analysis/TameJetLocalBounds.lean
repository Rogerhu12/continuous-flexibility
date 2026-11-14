module

public import ContinuousFlexibility.Analysis.TameLocalCalculus
public import ContinuousFlexibility.Analysis.TameElementaryCalculus
public import ContinuousFlexibility.Analysis.TameMultilinearNormalization

/-!
# Joint local tame growth and homogeneous jet bounds

The two formulations of tameness for a multilinear derivative are proved
equivalent. Joint local growth is convenient for composing expressions;
multilinear normalization recovers precisely the one-high-factor estimate
in `SmoothTameOn`, on one fixed low-order neighborhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section Gradings

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

def jetGrading (p : ℕ → Seminorm ℝ E) (k : ℕ) : ℕ → Seminorm ℝ (E × (Fin k → E)) :=
  pairGrading p (tupleGrading (fun _ : Fin k => p))

theorem jetGrading_apply (p : ℕ → Seminorm ℝ E) (k n : ℕ) (z : E × (Fin k → E)) :
    jetGrading p k n z = p n z.1 + ∑ i, p n (z.2 i) := by
  rw [jetGrading, pairGrading_apply, tupleGrading_apply]

theorem jetGrading_monotone {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (k : ℕ) :
    Monotone (jetGrading p k) :=
  tamePairGrading_monotone hp (tupleGrading_monotone _ (fun _ => hp))

theorem exists_seminormBall_subset_nhds {p : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (ht : WithSeminorms p) {x0 : E} {W : Set E}
    (hW : W ∈ 𝓝 x0) :
    ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, p base (x - x0) < ε → x ∈ W := by
  classical
  obtain ⟨S, ε, hε, hS⟩ := (ht.mem_nhds_iff x0 W).mp hW
  refine ⟨S.sup id, ε, hε, fun x hx => hS ?_⟩
  rw [Seminorm.mem_ball]
  exact Seminorm.finset_sup_apply_lt hε (fun i hi =>
    (hp (Finset.le_sup hi) (x - x0)).trans_lt hx)

/-- A joint neighborhood at a zero list of increments contains one common
low-seminorm box. The same base and radius work for all increments. -/
theorem exists_jetBox_subset_nhds {p : ℕ → Seminorm ℝ E}
    (hp : Monotone p) (ht : WithSeminorms p) (k : ℕ)
    {x0 : E} {W : Set (E × (Fin k → E))} (hW : W ∈ 𝓝 (x0, 0)) :
    ∃ base : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x v,
      p base (x - x0) < ε → (∀ i, p base (v i) < ε) → (x, v) ∈ W := by
  classical
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨ba, εa, hεa, ha⟩ := exists_seminormBall_subset_nhds hp ht hA
  let q : (Σ _ : Fin k, ℕ) → Seminorm ℝ (Fin k → E) :=
    fun i => (p i.2).comp (LinearMap.proj i.1)
  have hq : WithSeminorms q := withSeminorms_pi (fun _ : Fin k => ht)
  obtain ⟨S, εb, hεb, hb⟩ := (hq.mem_nhds_iff (0 : Fin k → E) B).mp hB
  let bb : ℕ := S.sup (fun i => i.2)
  refine ⟨max ba bb, min εa εb, lt_min hεa hεb, ?_⟩
  intro x v hx hv
  apply hAB
  refine ⟨ha x ((hp (le_max_left ba bb) (x - x0)).trans_lt
    (hx.trans_le (min_le_left _ _))), hb ?_⟩
  rw [Seminorm.mem_ball_zero]
  apply Seminorm.finset_sup_apply_lt hεb
  intro i hi
  dsimp only [q]
  rw [Seminorm.comp_apply, LinearMap.proj_apply]
  exact (hp ((Finset.le_sup hi).trans (le_max_right ba bb)) (v i.1)).trans_lt
    ((hv i.1).trans_le (min_le_right _ _))

end Gradings

section LocalJetBounds

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [ContinuousConstSMul ℝ F]
variable {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {f : E → F}

/-- The bounds attached to one specified genuine derivative tower. -/
def _root_.ContinuousFlexibility.Statements.SmoothDirections.TameBounds (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) : Prop :=
  ∀ k : ℕ, ∀ x0 ∈ U, ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
    ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
      p base (x - x0) < ε → ∀ v : Fin k → E,
        q s (J.D k x v) ≤ C * tameJetSize p k s loss base x v

private theorem prod_low_le {k : ℕ} (a : Fin k → ℝ) {M : ℝ}
    (hM : 1 ≤ M) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, a i ≤ M)
    (S : Finset (Fin k)) : ∏ i ∈ S, a i ≤ M ^ k := by
  calc
    ∏ i ∈ S, a i ≤ ∏ _i ∈ S, M :=
      Finset.prod_le_prod₀ (fun i _ => ha i) (fun i _ => hb i)
    _ = M ^ S.card := by simp only [Finset.prod_const]
    _ ≤ M ^ k := pow_le_pow_right₀ hM (by simpa using Finset.card_le_univ S)

/-- Every derivative evaluation is locally tame as a map of its base point
and all increments jointly. -/
theorem locallyTameOn_jetEvaluation (ht : WithSeminorms p)
    (J : SmoothDirections U f) (hJ : J.TameBounds p q) (k : ℕ) :
    LocallyTameOn (jetGrading p k) q (U ×ˢ univ)
      (fun z : E × (Fin k → E) => J.D k z.1 z.2) := by
  classical
  refine ⟨J.continuous k, ?_⟩
  intro z0 hz0
  obtain ⟨loss, base, ε, hε, hbound⟩ := hJ k z0.1 hz0.1
  let M : ℝ := 1 + ∑ i, p base (z0.2 i)
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hiM (i : Fin k) : p base (z0.2 i) < M := by
    have hi : p base (z0.2 i) ≤ ∑ j, p base (z0.2 j) :=
      Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_univ i)
    exact hi.trans_lt (lt_add_of_pos_left _ zero_lt_one)
  let W : Set (E × (Fin k → E)) :=
    {z | z.1 ∈ U ∧ p base (z.1 - z0.1) < ε ∧ ∀ i, p base (z.2 i) < M}
  have hWa : {z : E × (Fin k → E) | p base (z.1 - z0.1) < ε} ∈ 𝓝 z0 := by
    have hcont : ContinuousAt
        (fun z : E × (Fin k → E) => p base (z.1 - z0.1)) z0 :=
      ((ht.continuous_seminorm base).comp
        (continuous_fst.sub continuous_const)).continuousAt
    have hzero : p base (z0.1 - z0.1) < ε := by
      simpa only [sub_self, map_zero] using hε
    exact hcont.preimage_mem_nhds (Iio_mem_nhds hzero)
  have hWb : {z : E × (Fin k → E) | ∀ i, p base (z.2 i) < M} ∈ 𝓝 z0 := by
    apply Filter.eventually_all.mpr
    intro i
    have hcont : ContinuousAt (fun z : E × (Fin k → E) => p base (z.2 i)) z0 :=
      ((ht.continuous_seminorm base).comp
        ((continuous_apply i).comp continuous_snd)).continuousAt
    exact hcont.preimage_mem_nhds (Iio_mem_nhds (hiM i))
  have hW : W ∈ 𝓝[U ×ˢ univ] z0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (inter_mem hWa hWb)] with z hz hzw
    exact ⟨hz.1, hzw.1, hzw.2⟩
  refine ⟨loss, base, W, hW, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s hs
  refine ⟨C * M ^ k, mul_nonneg hC (pow_nonneg hM0 _), fun z hz => ?_⟩
  have hprod (S : Finset (Fin k)) : ∏ i ∈ S, p base (z.2 i) ≤ M ^ k :=
    prod_low_le _ hM (fun _ => apply_nonneg _ _) (fun i => (hz.2.2 i).le) S
  have hsize : tameJetSize p k s loss base z.1 z.2 ≤
      M ^ k * (1 + jetGrading p k (s + loss) z) := by
    unfold tameJetSize
    calc
      _ ≤ (1 + p (s + loss) z.1) * M ^ k +
          ∑ i, p (s + loss) (z.2 i) * M ^ k :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hprod Finset.univ) (by positivity))
          (Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hprod (Finset.univ.erase i)) (apply_nonneg _ _)))
      _ = _ := by rw [jetGrading_apply, ← Finset.sum_mul]; ring
  exact (hCs z.1 hz.1 hz.2.1 z.2).trans
    ((mul_le_mul_of_nonneg_left hsize hC).trans_eq (by ring))

/-- Joint local tame growth of all genuine jets yields exactly the frozen
smooth-tame definition, including its homogeneous increment factors. -/
theorem smoothTameOn_of_locallyTameOn_jets (hp : Monotone p) (ht : WithSeminorms p)
    (J : SmoothDirections U f)
    (hJ : ∀ k, LocallyTameOn (jetGrading p k) q (U ×ˢ univ)
      (fun z : E × (Fin k → E) => J.D k z.1 z.2)) :
    SmoothTameOn p q U f := by
  refine ⟨J, ?_⟩
  intro k x0 hx0
  obtain ⟨loss, base, W, hW, hbound⟩ := (hJ k).2 (x0, 0) ⟨hx0, mem_univ _⟩
  have hW' : W ∈ 𝓝 (x0, (0 : Fin k → E)) := by
    rwa [nhdsWithin_eq_nhds.mpr ((J.open_domain.prod isOpen_univ).mem_nhds
      ⟨hx0, mem_univ _⟩)] at hW
  obtain ⟨b, ε, hε, hbox⟩ := exists_jetBox_subset_nhds hp ht k hW'
  refine ⟨loss, max base b, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hCs⟩ := hbound s ((le_max_left base b).trans hs)
  refine ⟨multilinearNormalizationConstant k ε C,
    multilinearNormalizationConstant_nonneg k hε hC, ?_⟩
  intro x hx hnear v
  have hlocal : ∀ w : Fin k → E, (∀ i, p (max base b) (w i) < ε) →
      q s (J.D k x w) ≤ C * ((1 + p (s + loss) x) + ∑ i, p (s + loss) (w i)) := by
    intro w hw
    have hz : (x, w) ∈ W := hbox x w
      ((hp (le_max_right base b) (x - x0)).trans_lt hnear)
      (fun i => (hp (le_max_right base b) (w i)).trans_lt (hw i))
    simpa only [jetGrading_apply, add_assoc] using hCs (x, w) hz
  exact multilinear_oneHighFactor_of_local (J.D k x) (q s) (p (max base b))
    (p (s + loss)) hε hC hlocal v

end LocalJetBounds

end ContinuousFlexibility.Analysis
