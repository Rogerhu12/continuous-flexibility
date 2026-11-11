import ContinuousFlexibility.Analysis.N07aVolumeCell
import ContinuousFlexibility.Analysis.N07aTwoWeightNumerics

/-!
# Off-diagonal blocks of the actual reference inverse

The three estimates in N05 refer to one `globalInverse`. A source supported
on one cell belongs to all three weighted spaces after the explicit change
of weight. Comparing the two output representations gives the logarithmic
height decay for that same inverse, with no additional operator assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

local instance (γ t : ℝ) (s : ℕ) : NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _

local instance (γ t : ℝ) (s : ℕ) : NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _

private def n07aReferenceWeightBound (γ t : ℝ) (s : ℕ) (A : ℝ) : Prop :=
  ∀ F : V.level γ t s, ∃ W : V.level γ (t - B.lossMaterial) s,
    V.forget γ (t - B.lossMaterial) s W =
      (fun m => (B.globalInverse (V.forget γ t s F)).1 m) ∧
    ‖W‖ + canonicalUnknownScalars S K (B.globalInverse (V.forget γ t s F)) ≤ A * ‖F‖

private theorem n07a_reference_weight_zero
    (γ : ℝ) (s : ℕ) (A : ℝ)
    (h : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B) γ 0 s A) :
    ∀ F : V.level γ 0 s, ∃ W : V.level γ (-B.lossMaterial) s,
      V.forget γ (-B.lossMaterial) s W =
        (fun m => (B.globalInverse (V.forget γ 0 s F)).1 m) ∧
      ‖W‖ + canonicalUnknownScalars S K (B.globalInverse (V.forget γ 0 s F)) ≤ A * ‖F‖ := by
  unfold n07aReferenceWeightBound at h
  rwa [zero_sub] at h

private def n07aReferenceThreeWeights (δ : ℝ) : Prop :=
  ∀ γ : ℝ,
    (γ = (3 / 4 : ℝ) - δ ∨ γ = (3 / 4 : ℝ) ∨ γ = (3 / 4 : ℝ) + δ) →
    ∀ t : ℝ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧
      n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B) γ t s A

private theorem n07a_reference_three_weights
    (h05 : N05Properties D T S C K V b B) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (1 / 4 : ℝ) ∧
      n07aReferenceThreeWeights (S := S) (K := K) (V := V) (B := B) δ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.1

private theorem n07a_reference_block_from_weight
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ : ℝ) (s : ℕ) (A : ℝ)
    (hbound : ∀ Q : V.level γ 0 s,
      ∃ Y : V.level γ (-B.lossMaterial) s,
        V.forget γ (-B.lossMaterial) s Y =
          (fun k => (B.globalInverse (V.forget γ 0 s Q)).1 k) ∧
        ‖Y‖ + canonicalUnknownScalars S K (B.globalInverse (V.forget γ 0 s Q)) ≤ A * ‖Q‖)
    (m : ℕ) (F : V.level (3 / 4 : ℝ) 0 s)
    (W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s)
    (hW : V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
      (fun k => (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))).1 k))
    (k : ℕ) :
    ‖n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W‖ ≤
      A * (n07aVolumeWeight T K γ (-B.lossMaterial) k /
        n07aVolumeWeight T K (3 / 4 : ℝ) 0 k) *
        (n07aVolumeWeight T K (3 / 4 : ℝ) 0 m / n07aVolumeWeight T K γ 0 m) *
        ‖F.val m‖ := by
  let Q : V.level γ 0 s := n07aVolumeCellReweight hV γ 0 m F
  have hQ : V.forget γ 0 s Q = Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m) :=
    n07aVolumeCellReweight_forget hV γ 0 m F (n07aVolumeWeight_pos hD hT γ 0 m).ne'
  obtain ⟨Y, hY, hnorm⟩ := hbound Q
  rw [hQ] at hY
  have hcell : n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W =
      n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k Y :=
    n07aVolumeCellReweight_eq_of_forget hV (3 / 4 : ℝ) 0 k W Y
      (n07aVolumeWeight_pos hD hT (3 / 4 : ℝ) 0 k).ne' (hW.trans hY.symm)
  have hscalars : 0 ≤ canonicalUnknownScalars S K (B.globalInverse (V.forget γ 0 s Q)) :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hYnorm : ‖Y‖ ≤ A * ‖Q‖ := (le_add_of_nonneg_right hscalars).trans hnorm
  have hpiece : ‖Y.val k‖ ≤ ‖Y‖ := by
    rw [← Submodule.norm_coe Y]
    exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) Y.val k
  have hk : 0 < n07aVolumeWeight T K γ (-B.lossMaterial) k /
      n07aVolumeWeight T K (3 / 4 : ℝ) 0 k :=
    div_pos (n07aVolumeWeight_pos hD hT γ (-B.lossMaterial) k)
      (n07aVolumeWeight_pos hD hT (3 / 4 : ℝ) 0 k)
  have hm : 0 < n07aVolumeWeight T K (3 / 4 : ℝ) 0 m /
      n07aVolumeWeight T K γ 0 m :=
    div_pos (n07aVolumeWeight_pos hD hT (3 / 4 : ℝ) 0 m)
      (n07aVolumeWeight_pos hD hT γ 0 m)
  rw [hcell, n07aVolumeCellReweight_norm, abs_of_pos hk]
  calc
    _ ≤ (n07aVolumeWeight T K γ (-B.lossMaterial) k /
        n07aVolumeWeight T K (3 / 4 : ℝ) 0 k) * (A * ‖Q‖) :=
      mul_le_mul_of_nonneg_left (hpiece.trans hYnorm) hk.le
    _ = _ := by
      rw [show ‖Q‖ = _ from n07aVolumeCellReweight_norm hV γ 0 m F, abs_of_pos hm]
      ring

private theorem n07a_reference_cell_scalars
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (δ : ℝ) (s : ℕ) (Am : ℝ)
    (hminus : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      ((3 / 4 : ℝ) - δ) 0 s Am)
    (m : ℕ) (F : V.level (3 / 4 : ℝ) 0 s) :
    canonicalUnknownScalars S K
      (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))) ≤
        Am * T.H (T.sample (K.cell m)) ^ δ * ‖F.val m‖ := by
  unfold n07aReferenceWeightBound at hminus
  let Qm : V.level ((3 / 4 : ℝ) - δ) 0 s :=
    n07aVolumeCellReweight hV ((3 / 4 : ℝ) - δ) 0 m F
  have hQm : V.forget ((3 / 4 : ℝ) - δ) 0 s Qm =
      Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m) :=
    n07aVolumeCellReweight_forget hV ((3 / 4 : ℝ) - δ) 0 m F
      (n07aVolumeWeight_pos hD hT ((3 / 4 : ℝ) - δ) 0 m).ne'
  obtain ⟨Ym, _, hnorm⟩ := hminus Qm
  have hs := (le_add_of_nonneg_left (norm_nonneg Ym)).trans hnorm
  rw [hQm] at hs
  have hm := spaces_trace_sample_mem hD hT (K.cell m)
  have hH := (hT.2.1 _ hm).2.1
  have hratio : n07aVolumeWeight T K (3 / 4 : ℝ) 0 m /
      n07aVolumeWeight T K ((3 / 4 : ℝ) - δ) 0 m =
      T.H (T.sample (K.cell m)) ^ δ := by
    simp only [n07aVolumeWeight, neg_zero, Real.rpow_zero, one_mul]
    rw [← Real.rpow_sub hH]
    congr 1
    ring
  have hQnorm : ‖Qm‖ = T.H (T.sample (K.cell m)) ^ δ * ‖F.val m‖ := by
    rw [show ‖Qm‖ = _ from n07aVolumeCellReweight_norm hV
      ((3 / 4 : ℝ) - δ) 0 m F, hratio, abs_of_pos (Real.rpow_pos_of_pos hH δ)]
  rw [hQnorm] at hs
  simpa only [mul_assoc] using hs

private theorem n07a_reference_cell_output_decay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (δ : ℝ) (hδ : 0 < δ) (s : ℕ)
    (Am Ap : ℝ) (hAm : 0 < Am) (hAp : 0 < Ap)
    (hminus : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      ((3 / 4 : ℝ) - δ) 0 s Am)
    (hplus : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      ((3 / 4 : ℝ) + δ) 0 s Ap)
    (m : ℕ) (F : V.level (3 / 4 : ℝ) 0 s)
    (W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s)
    (hW : V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
      (fun k => (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))).1 k))
    (k : ℕ) :
    ‖n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W‖ ≤
      (Am + Ap) * T.M (T.sample (K.cell k)) ^ B.lossMaterial *
        Real.exp (-δ * |Real.log (T.H (T.sample (K.cell k))) -
          Real.log (T.H (T.sample (K.cell m)))|) * ‖F.val m‖ := by
  unfold n07aReferenceWeightBound at hminus hplus
  rw [zero_sub] at hminus hplus
  have hm := spaces_trace_sample_mem hD hT (K.cell m)
  have hk := spaces_trace_sample_mem hD hT (K.cell k)
  have hHm := (hT.2.1 _ hm).2.1
  have hHk := (hT.2.1 _ hk).2.1
  have hMk : 0 < T.M (T.sample (K.cell k)) :=
    lt_of_lt_of_le zero_lt_one (hT.2.1 _ hk).2.2.2
  let rm : ℝ :=
    (T.M (T.sample (K.cell k)) ^ B.lossMaterial *
      T.H (T.sample (K.cell k)) ^ ((3 / 4 : ℝ) - δ) /
      T.H (T.sample (K.cell k)) ^ (3 / 4 : ℝ)) *
      (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) /
        T.H (T.sample (K.cell m)) ^ ((3 / 4 : ℝ) - δ))
  let rp : ℝ :=
    (T.M (T.sample (K.cell k)) ^ B.lossMaterial *
      T.H (T.sample (K.cell k)) ^ ((3 / 4 : ℝ) + δ) /
      T.H (T.sample (K.cell k)) ^ (3 / 4 : ℝ)) *
      (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) /
        T.H (T.sample (K.cell m)) ^ ((3 / 4 : ℝ) + δ))
  have hrm : 0 ≤ rm := by dsimp only [rm]; positivity
  have hrp : 0 ≤ rp := by dsimp only [rp]; positivity
  have hbm : ‖n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W‖ ≤ Am * rm * ‖F.val m‖ := by
    simpa only [n07aVolumeWeight, neg_zero, Real.rpow_zero, one_mul, neg_neg, rm,
      mul_assoc] using
      n07a_reference_block_from_weight (B := B) hD hT hV ((3 / 4 : ℝ) - δ) s Am hminus m F W hW k
  have hbp : ‖n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W‖ ≤ Ap * rp * ‖F.val m‖ := by
    simpa only [n07aVolumeWeight, neg_zero, Real.rpow_zero, one_mul, neg_neg, rp,
      mul_assoc] using
      n07a_reference_block_from_weight (B := B) hD hT hV ((3 / 4 : ℝ) + δ) s Ap hplus m F W hW k
  have hbmin : ‖n07aVolumeCellReweight hV (3 / 4 : ℝ) 0 k W‖ ≤
      (Am + Ap) * min rm rp * ‖F.val m‖ := by
    by_cases h : rm ≤ rp
    · rw [min_eq_left h]
      exact hbm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hAp.le) hrm) (norm_nonneg _))
    · rw [min_eq_right (le_of_not_ge h)]
      exact hbp.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hAm.le) hrp) (norm_nonneg _))
  have hmin : min rm rp = T.M (T.sample (K.cell k)) ^ B.lossMaterial *
      Real.exp (-δ * |Real.log (T.H (T.sample (K.cell k))) -
        Real.log (T.H (T.sample (K.cell m)))|) :=
    n07a_twoWeightRatio_min hHk hHm (Real.rpow_pos_of_pos hMk _).le hδ.le (3 / 4 : ℝ)
  rw [hmin] at hbmin
  simpa only [mul_assoc] using hbmin


/-- The reference inverse on a one-cell source has exponential decay in
logarithmic height. All angular orders use the original N05 inverse. -/
theorem n07a_reference_inverse_cell_decay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h05 : N05Properties D T S C K V b B) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (1 / 4 : ℝ) ∧ ∀ s : ℕ,
      ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (F : V.level (3 / 4 : ℝ) 0 s),
        ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s,
          V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
            (fun k => (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))).1 k) ∧
          canonicalUnknownScalars S K
            (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))) ≤
              A * T.H (T.sample (K.cell m)) ^ δ * ‖F.val m‖ ∧
          ∀ k : ℕ, ‖n07aVolumeCellReweight h05.2.1 (3 / 4 : ℝ) 0 k W‖ ≤
            A * T.M (T.sample (K.cell k)) ^ B.lossMaterial *
              Real.exp (-δ * |Real.log (T.H (T.sample (K.cell k))) -
                Real.log (T.H (T.sample (K.cell m)))|) * ‖F.val m‖ := by
  let weights := n07a_reference_three_weights (D := D) (T := T) (S := S) (C := C)
    (K := K) (V := V) (b := b) (B := B) h05
  let δ : ℝ := weights.choose
  have hδ : 0 < δ := weights.choose_spec.1
  have hδsmall : δ < (1 / 4 : ℝ) := weights.choose_spec.2.1
  have hweights : n07aReferenceThreeWeights (S := S) (K := K) (V := V) (B := B) δ :=
    weights.choose_spec.2.2
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro s
  let hm := hweights ((3 / 4 : ℝ) - δ) (Or.inl rfl) 0 s
  let hp := hweights ((3 / 4 : ℝ) + δ) (Or.inr (Or.inr rfl)) 0 s
  let hb := hweights (3 / 4 : ℝ) (Or.inr (Or.inl rfl)) 0 s
  let Am : ℝ := hm.choose
  let Ap : ℝ := hp.choose
  have hAm : 0 < Am := hm.choose_spec.1
  have hAp : 0 < Ap := hp.choose_spec.1
  have hminus : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      ((3 / 4 : ℝ) - δ) 0 s Am := hm.choose_spec.2
  have hplus : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      ((3 / 4 : ℝ) + δ) 0 s Ap := hp.choose_spec.2
  have hbase : n07aReferenceWeightBound (S := S) (K := K) (V := V) (B := B)
      (3 / 4 : ℝ) 0 s hb.choose := hb.choose_spec.2
  have hbase0 := n07a_reference_weight_zero (B := B) (3 / 4 : ℝ) s hb.choose hbase
  refine ⟨Am + Ap, add_pos hAm hAp, ?_⟩
  intro m F
  let Q : V.level (3 / 4 : ℝ) 0 s :=
    n07aVolumeCellReweight h05.2.1 (3 / 4 : ℝ) 0 m F
  have hQ : V.forget (3 / 4 : ℝ) 0 s Q =
      Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m) :=
    n07aVolumeCellReweight_forget h05.2.1 (3 / 4 : ℝ) 0 m F
      (n07aVolumeWeight_pos hD hT (3 / 4 : ℝ) 0 m).ne'
  let representation := hbase0 Q
  let W : V.level (3 / 4 : ℝ) (-B.lossMaterial) s := representation.choose
  have hW : V.forget (3 / 4 : ℝ) (-B.lossMaterial) s W =
      (fun k => (B.globalInverse (Pi.single m (V.forget (3 / 4 : ℝ) 0 s F m))).1 k) :=
    representation.choose_spec.1.trans
      (congrArg (fun source => fun k => (B.globalInverse source).1 k) hQ)
  refine ⟨W, hW, ?_, ?_⟩
  · have hs := n07a_reference_cell_scalars (B := B) hD hT h05.2.1 δ s Am hminus m F
    have hm := spaces_trace_sample_mem hD hT (K.cell m)
    have hH := (hT.2.1 _ hm).2.1
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hAp.le)
        (Real.rpow_pos_of_pos hH δ).le) (norm_nonneg _))
  · exact n07a_reference_cell_output_decay (B := B) hD hT h05.2.1 δ hδ s
      Am Ap hAm hAp hminus hplus m F W hW

end ContinuousFlexibility.Analysis
