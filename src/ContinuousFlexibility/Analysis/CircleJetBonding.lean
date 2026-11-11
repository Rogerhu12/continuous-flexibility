import ContinuousFlexibility.Analysis.CircleJetClosedGraph

open scoped BigOperators ENNReal

namespace ContinuousFlexibility.Statements

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Inclusion of the lower order pairs, preserving both exponents. -/
def circleJetIndexOfLE {s t : ℕ} (hst : s ≤ t) : CircleJetIndex s ↪ CircleJetIndex t where
  toFun j := ⟨fun i => Fin.castLE (Nat.succ_le_succ hst) (j.val i), j.property.trans hst⟩
  inj' := by
    intro j k hjk
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun z : CircleJetIndex t => (z.val i).val) hjk

@[simp] theorem circleJetIndexOfLE_val {s t : ℕ} (hst : s ≤ t) (j : CircleJetIndex s)
    (i : Fin 2) : ((circleJetIndexOfLE hst j).val i).val = (j.val i).val := rfl

@[simp] theorem circleJetIndexOfLE_zero {s t : ℕ} (hst : s ≤ t) :
    circleJetIndexOfLE hst (zeroCircleJetIndex s) = zeroCircleJetIndex t := by
  apply Subtype.ext
  funext i
  exact Fin.castLE_zero (Nat.succ_le_succ hst)

/-- Restrict the actual finite Hilbert product at one sample. -/
def circleJetPiRestrict {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : CircleJetIndex t => AngleL2)) :
    PiLp 2 (fun _ : CircleJetIndex s => AngleL2) :=
  WithLp.toLp 2 (fun j => v (circleJetIndexOfLE hst j))

@[simp] theorem circleJetPiRestrict_apply {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : CircleJetIndex t => AngleL2)) (j : CircleJetIndex s) :
    circleJetPiRestrict hst v j = v (circleJetIndexOfLE hst j) := rfl

theorem circleJetPiRestrict_norm_sq_le {s t : ℕ} (hst : s ≤ t)
    (v : PiLp 2 (fun _ : CircleJetIndex t => AngleL2)) :
    ‖circleJetPiRestrict hst v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : CircleJetIndex s, ‖circleJetPiRestrict hst v j‖ ^ 2) =
        ∑ j ∈ Finset.univ.map (circleJetIndexOfLE hst), ‖v j‖ ^ 2 := by
          simp only [Finset.sum_map, circleJetPiRestrict_apply]
    _ ≤ ∑ j : CircleJetIndex t, ‖v j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

private theorem circleJet_rpow_two (x : ℝ) : x ^ (2 : ℝ≥0∞).toReal = x ^ (2 : ℕ) := by
  norm_cast

theorem circleJetHilbert_summable_sq {s : ℕ} (z : CircleJetHilbert s) :
    Summable (fun m : ℕ => ‖z m‖ ^ 2) := by
  have h₂ : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  simpa only [circleJet_rpow_two] using (memℓp_gen_iff h₂).mp (lp.memℓp z)

theorem circleJetHilbert_norm_sq {s : ℕ} (z : CircleJetHilbert s) :
    ‖z‖ ^ 2 = ∑' m : ℕ, ‖z m‖ ^ 2 := by
  have h₂ : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  simpa only [circleJet_rpow_two] using lp.norm_rpow_eq_tsum h₂ z

private def circleJetHilbertRestrictFun {s t : ℕ} (hst : s ≤ t)
    (z : CircleJetHilbert t) : CircleJetHilbert s :=
  ⟨fun m => circleJetPiRestrict hst (z m), memℓp_gen (by
    simp only [circleJet_rpow_two]
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun m => circleJetPiRestrict_norm_sq_le hst (z m)) (circleJetHilbert_summable_sq z))⟩

private theorem circleJetHilbertRestrictFun_norm_le {s t : ℕ} (hst : s ≤ t)
    (z : CircleJetHilbert t) : ‖circleJetHilbertRestrictFun hst z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [circleJetHilbert_norm_sq, circleJetHilbert_norm_sq]
  exact Summable.tsum_le_tsum (fun m => circleJetPiRestrict_norm_sq_le hst (z m))
    (circleJetHilbert_summable_sq (circleJetHilbertRestrictFun hst z))
    (circleJetHilbert_summable_sq z)

/-- Continuous linear restriction in the prescribed outer ℓ² and inner PiLp norm. -/
def circleJetHilbertRestrict {s t : ℕ} (hst : s ≤ t) :
    CircleJetHilbert t →L[ℝ] CircleJetHilbert s :=
  (show CircleJetHilbert t →ₗ[ℝ] CircleJetHilbert s from
    { toFun := circleJetHilbertRestrictFun hst
      map_add' := by
        intro x y
        apply lp.ext
        funext m
        apply (WithLp.ext_iff 2).mpr
        funext j
        rfl
      map_smul' := by
        intro c x
        apply lp.ext
        funext m
        apply (WithLp.ext_iff 2).mpr
        funext j
        rfl }).mkContinuous 1 (by
    intro z
    change ‖circleJetHilbertRestrictFun hst z‖ ≤ 1 * ‖z‖
    rw [one_mul]
    exact circleJetHilbertRestrictFun_norm_le hst z)

@[simp] theorem circleJetHilbertRestrict_apply {s t : ℕ} (hst : s ≤ t)
    (z : CircleJetHilbert t) (m : ℕ) (j : CircleJetIndex s) :
    circleJetHilbertRestrict hst z m j = z m (circleJetIndexOfLE hst j) := rfl

theorem circleJetHilbertRestrict_norm_le {s t : ℕ} (hst : s ≤ t) (z : CircleJetHilbert t) :
    ‖circleJetHilbertRestrict hst z‖ ≤ ‖z‖ :=
  circleJetHilbertRestrictFun_norm_le hst z

theorem circleJetHilbertRestrict_mem_circleJetGraph {T : MaterialData} {s t : ℕ}
    (hst : s ≤ t) {z : CircleJetHilbert t} (hz : z ∈ circleJetGraph T t) :
    circleJetHilbertRestrict hst z ∈ circleJetGraph T s := by
  intro m j
  simpa only [circleJetHilbertRestrict_apply, circleJetIndexOfLE_zero, circleJetIndexOfLE_val] using
    hz m (circleJetIndexOfLE hst j)

/-- The same restriction on the closed graph levels. -/
def circleJetGraphRestrict (T : MaterialData) (hM : ∀ m, 0 < T.M (T.sample m)) {s t : ℕ}
    (hst : s ≤ t) : circleJetClosedSubmodule T t →L[ℝ] circleJetClosedSubmodule T s :=
  ((circleJetHilbertRestrict hst).comp (circleJetClosedSubmodule T t).subtypeL).codRestrict
    (circleJetClosedSubmodule T s) (by
      intro z
      rw [← SetLike.mem_coe, circleJetClosedSubmodule_carrier hM]
      have hz : z.val ∈ circleJetGraph T t := by
        rw [← circleJetClosedSubmodule_carrier hM]
        exact z.property
      exact circleJetHilbertRestrict_mem_circleJetGraph hst hz)

@[simp] theorem circleJetGraphRestrict_apply (T : MaterialData)
    (hM : ∀ m, 0 < T.M (T.sample m)) {s t : ℕ} (hst : s ≤ t)
    (z : circleJetClosedSubmodule T t) (m : ℕ) (j : CircleJetIndex s) :
    (circleJetGraphRestrict T hM hst z).val m j = z.val m (circleJetIndexOfLE hst j) := rfl

theorem circleJetGraphRestrict_norm_le (T : MaterialData)
    (hM : ∀ m, 0 < T.M (T.sample m)) {s t : ℕ} (hst : s ≤ t)
    (z : circleJetClosedSubmodule T t) :
    ‖circleJetGraphRestrict T hM hst z‖ ≤ ‖z‖ :=
  circleJetHilbertRestrict_norm_le hst z.val

def circleJetBond (T : MaterialData) (hM : ∀ m, 0 < T.M (T.sample m)) (s : ℕ) :
    circleJetClosedSubmodule T (s + 1) →L[ℝ] circleJetClosedSubmodule T s :=
  circleJetGraphRestrict T hM (Nat.le_succ s)

/-- The actual closed projective carrier of compatible circle jets. -/
abbrev CircleJetProjectiveLimit (T : MaterialData) (hM : ∀ m, 0 < T.M (T.sample m)) :=
  Analysis.ProjectiveLimit (fun s => ↥(circleJetClosedSubmodule T s)) (circleJetBond T hM)

theorem isClosed_circleJetProjectiveCarrier (T : MaterialData)
    (hM : ∀ m, 0 < T.M (T.sample m)) :
    IsClosed (Analysis.compatibleSubmodule (fun s => ↥(circleJetClosedSubmodule T s)) (circleJetBond T hM) :
      Set (∀ s, circleJetClosedSubmodule T s)) :=
  Analysis.isClosed_compatibleSubmodule _ _

theorem circleJetProjectiveLimit_complete (T : MaterialData)
    (hM : ∀ m, 0 < T.M (T.sample m)) : CompleteSpace (CircleJetProjectiveLimit T hM) :=
  Analysis.projectiveLimit_completeSpace _ _

theorem circleJetProjective_level_norm_mono {T : MaterialData}
    {hM : ∀ m, 0 < T.M (T.sample m)} (u : CircleJetProjectiveLimit T hM) :
    Monotone (fun s => ‖u.val s‖) := by
  apply monotone_nat_of_le_succ
  intro s
  rw [← u.property s]
  exact circleJetGraphRestrict_norm_le T hM (Nat.le_succ s) (u.val (s + 1))

theorem circleJetProjective_zero_eq {T : MaterialData}
    {hM : ∀ m, 0 < T.M (T.sample m)} (u : CircleJetProjectiveLimit T hM) (s m : ℕ) :
    (u.val s).val m (zeroCircleJetIndex s) = (u.val 0).val m (zeroCircleJetIndex 0) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h : (circleJetGraphRestrict T hM (Nat.le_succ s) (u.val (s + 1))).val m
        (zeroCircleJetIndex s) = (u.val s).val m (zeroCircleJetIndex s) :=
      congrArg (fun z : circleJetClosedSubmodule T s =>
        z.val m (zeroCircleJetIndex s)) (u.property s)
    simpa only [circleJetGraphRestrict_apply, circleJetIndexOfLE_zero] using h.trans ih

end

end ContinuousFlexibility.Statements
