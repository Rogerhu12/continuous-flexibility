module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryOperatorBounds
public import ContinuousFlexibility.Analysis.N04RealizationInverseBoundaryDirections

/-!
# A quantitative step for genuine finite boundary inverse jets

The ordinary local inverse formula determines the actual higher inverse
jet. Its parameter and angular tower is assembled from the first inverse
differential, the forward jets at the actual inverse point, and lower
actual inverse jets. Every operation preserves the finite angular reserve.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04PositiveGeometry_boundaryInverse_first_bound
    {U : Set X} {f : X × ℝ → E → F} {g : X × ℝ → F → E}
    {q : X × ℝ → F} {L : X × ℝ → F →L[ℝ] E}
    (hf : ∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f z) (g z (q z)))
    (hg : ∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g z) (q z))
    (hfg : ∀ z ∈ U ×ˢ univ, f z ∘ g z =ᶠ[𝓝 (q z)] (id : F → F))
    (hL : ∀ z ∈ U ×ˢ univ,
      (L z).comp (fderiv ℝ (f z) (g z (q z))) = ContinuousLinearMap.id ℝ E)
    (JL : SmoothDirections (U ×ˢ univ) L)
    {K s d : ℕ} {x : X} (hx : x ∈ U) {θ : ℝ} {P : X → Prop}
    {M H t : ℝ} {shift : ℕ}
    (hJL : N04BoundaryWordBounds JL K s d x θ P M H t shift)
    (v : Fin 1 → F) (hv : ∀ i, ‖v i‖ ≤ 1)
    (Q : SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ 1 (g z) (q z) v)) :
    N04BoundaryWordBounds Q K s d x θ P M H t shift := by
  let A : (F →L[ℝ] E) →L[ℝ] E :=
    { toFun := fun B => B (v 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_id.clm_apply continuous_const }
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro B
    change ‖B (v 0)‖ ≤ 1 * ‖B‖
    exact (B.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (hv 0)
        (ContinuousLinearMap.opNorm_nonneg B)).trans_eq (by ring))
  have hbound := hJL.postcompCLM A hA
  apply hbound.congr (Q := Q) hx
  intro z hz
  rw [iteratedFDeriv_one_apply,
    nonlinearInverse_fderiv_eq (hf z hz) (hg z hz) (hfg z hz) (L z) (hL z hz)]
  rfl

theorem n04PositiveGeometry_boundaryInverse_step_bound (N n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
      ∀ {U : Set X}, IsOpen U →
      ∀ (f : X × ℝ → E → F) (g : X × ℝ → F → E)
        (q : X × ℝ → F) (L : X × ℝ → F →L[ℝ] E),
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f z) (g z (q z))) →
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g z) (q z)) →
      (∀ z ∈ U ×ˢ univ, f z ∘ g z =ᶠ[𝓝 (q z)] (id : F → F)) →
      (∀ z ∈ U ×ˢ univ,
        (L z).comp (fderiv ℝ (f z) (g z (q z))) = ContinuousLinearMap.id ℝ E) →
      ∀ JL : SmoothDirections (U ×ˢ univ) L,
      ∀ JF : ∀ j, 2 ≤ j → j ≤ n →
        SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (f z) (g z (q z))),
      ∀ JG : ∀ j, 1 ≤ j → j < n → ∀ v : Fin j → F,
        SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (g z) (q z) v),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      N04BoundaryWordBounds JL K s d x θ P M H t shift →
      (∀ j hj hjn, N04BoundaryWordBounds (JF j hj hjn) K s d x θ P M H t shift) →
      (∀ j hj hjn v, (∀ i, ‖v i‖ ≤ 1) →
        N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
      ∀ v : Fin n → F, (∀ i, ‖v i‖ ≤ 1) →
      ∀ Q : SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ n (g z) (q z) v),
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  classical
  choose a ha hbound using fun c : OrderedFinpartition n =>
    n04PositiveGeometry_boundary_multilinearApply_bound (X := X) (E := E) (F := F)
      c.length N
  obtain ⟨b, hb, hneg⟩ := n04PositiveGeometry_boundary_negClmApply_bound
    (X := X) (E := F) (F := E) N
  let A : ℝ := 1 + ∑ c : OrderedFinpartition n, a c
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun c _ => zero_le_one.trans (ha c)))
  have haA (c : OrderedFinpartition n) : a c ≤ A :=
    (Finset.single_le_sum (fun c _ => zero_le_one.trans (ha c))
      (Finset.mem_univ c)).trans (le_add_of_nonneg_left zero_le_one)
  let B : ℝ := 1 + (Fintype.card (OrderedFinpartition n) : ℝ) * A
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hA))
  let D := n + 1 + 2 * N
  let e := 2 + 2 * N
  refine ⟨b * B ^ e, one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ hB),
    D * e, by
      apply Nat.succ_le_of_lt
      apply Nat.mul_pos <;> dsimp [D, e] <;> omega, ?_⟩
  intro U hU f g q L hf hg hfg hL JL JF JG K s d hN x hx θ P
    M H t hM hH hHM ht shift hJL hJF hJG v hv Q
  let term : OrderedFinpartition n → X × ℝ → F := fun c z =>
    if 2 ≤ c.length then
      iteratedFDeriv ℝ c.length (f z) (g z (q z))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (g z) (q z) (v ∘ c.emb i))
    else 0
  have hterms (c : OrderedFinpartition n) :
      ∃ JT : SmoothDirections (U ×ˢ univ) (term c),
        N04BoundaryWordBounds JT K s d x θ P (A * M ^ D) H t shift := by
    by_cases hc : 2 ≤ c.length
    · let JV : ∀ i : Fin c.length, SmoothDirections (U ×ˢ univ)
          (fun z => iteratedFDeriv ℝ (c.partSize i) (g z) (q z) (v ∘ c.emb i)) :=
        fun i => JG (c.partSize i) (c.partSize_pos i)
          (flowJet_partition_partSize_lt c hc i) (v ∘ c.emb i)
      let Jtuple := smoothDirections_vectorTuple (hU.prod isOpen_univ) JV
      let Jpair := smoothDirectionsProd (JF c.length hc c.length_le) Jtuple
      let JT := smoothDirections_contDiff_comp Jpair isOpen_univ
        (contDiff_multilinearEvaluation c.length).contDiffOn (fun _ _ => mem_univ _)
      have htuple : N04BoundaryWordBounds Jtuple K s d x θ P M H t shift :=
        N04BoundaryWordBounds.vectorTuple hU JV (zero_le_one.trans hM) hH
          (zero_le_one.trans ht) (fun i => hJG _ _ _ _ (fun j => hv (c.emb i j)))
      have hterm := hbound c (JF c.length hc c.length_le) Jtuple JT
        K s d hN x hx θ P M H t hM hH hHM ht shift (hJF _ _ _) htuple
      let JT' : SmoothDirections (U ×ˢ univ) (term c) :=
        JT.congr (fun z _ => by simp only [term, if_pos hc]; rfl)
      refine ⟨JT', (hterm.enlarge hH (zero_le_one.trans ht) ?_).congr hx
        (fun z _ => by simp only [term, if_pos hc])⟩
      exact mul_le_mul (haA c) (pow_le_pow_right₀ hM (Nat.add_le_add_right
          (Nat.add_le_add_right c.length_le 1) (2 * N)))
        (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hA)
    · let Jzero : SmoothDirections (U ×ˢ univ) (fun _ : X × ℝ => (0 : F)) :=
        smoothDirections_postcompCLM JL (0 : (F →L[ℝ] E) →L[ℝ] F)
      have hzbound : N04BoundaryWordBounds Jzero K s d x θ P (A * M ^ D) H t shift := by
        intro j w hk hs u hu hp
        rw [smoothDirections_postcompCLM_D_apply]
        simp only [ContinuousLinearMap.zero_apply, norm_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hA)
          (pow_nonneg (zero_le_one.trans hM) _)) (parameterHeightWeight_nonneg hH _))
          (pow_nonneg (zero_le_one.trans ht) _)
      exact ⟨Jzero.congr (fun z _ => by simp only [term, if_neg hc]),
        hzbound.congr hx (fun z _ => by simp only [term, if_neg hc])⟩
  choose JT hJT using hterms
  let Jsum := smoothDirections_finiteSum (hU.prod isOpen_univ) JT
  have hsum := N04BoundaryWordBounds.finiteSum hU JT hJT
  let R := B * M ^ D
  have hMR : M ≤ R := by
    calc
      M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ D := pow_le_pow_right₀ hM (by dsimp [D]; omega)
      _ ≤ B * M ^ D := le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hM) _) hB
  have hsumR : N04BoundaryWordBounds Jsum K s d x θ P R H t shift :=
    hsum.enlarge hH (zero_le_one.trans ht) (by
      dsimp only [R, B]
      have hp : 0 ≤ M ^ D := pow_nonneg (zero_le_one.trans hM) _
      nlinarith)
  let Jpair := smoothDirectionsProd JL Jsum
  let JO := smoothDirections_contDiff_comp Jpair isOpen_univ
    (contDiff_fst.clm_apply contDiff_snd).neg.contDiffOn (fun _ _ => mem_univ _)
  have hJO := hneg JL Jsum JO K s d hN x hx θ P R H t
    (hM.trans hMR) hH (hHM.trans hMR) ht shift
    (hJL.enlarge hH (zero_le_one.trans ht) hMR) hsumR
  have he : ∀ z ∈ U ×ˢ univ,
      -L z (∑ c, term c z) = iteratedFDeriv ℝ n (g z) (q z) v := by
    intro z hz
    exact (n04Realization_inverse_higherJet_apply (hf z hz) (hg z hz)
      (hfg z hz) (L z) (hL z hz) hn v).symm
  have hout := hJO.congr (Q := Q) hx he
  simpa only [R, e, mul_pow, ← pow_mul, mul_assoc] using hout

end ContinuousFlexibility.Analysis
