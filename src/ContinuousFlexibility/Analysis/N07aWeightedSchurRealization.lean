import ContinuousFlexibility.Analysis.N07aMaterialEmbeddingLinear
import ContinuousFlexibility.Analysis.N07aSchurLiftIdentity
import ContinuousFlexibility.Analysis.N07aAngularCommutatorDomain
import ContinuousFlexibility.Analysis.N07aCircleCoefficientDecay

/-!
# Schur realization in the actual weighted source graph

The supplied block realizations are unique because the prescribed forget
map is injective. Their Riesz sum is identified with the same base
operator after the genuine material inclusion. No unbounded series of
vectors is inferred from a scalar weak sum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ENNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aWeightedSchurLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aWeightedSchurLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aWeightedSchurLevelInner (γ t : ℝ) (s : ℕ) :
    InnerProductSpace ℝ (V.level γ t s) := Submodule.innerProductSpace _

theorem n07aAngularLevelBand_square_budget
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (hI : ∀ m, K.left m < K.right m)
    (s : ℕ) (u : V.level γ t s) :
    Summable (fun j => ‖n07aAngularLevelBand hV γ t hI s j u‖ ^ 2) ∧
      ∑' j, ‖n07aAngularLevelBand hV γ t hI s j u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  let e := n07aAngularHilbertEquiv hV γ t hI s
  have hc (j : ℕ) : ‖e u j‖ = ‖n07aAngularLevelBand hV γ t hI s j u‖ := by
    rw [← Submodule.norm_coe, n07aAngularHilbertEquiv_apply_val]
  have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (e u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hc, LinearIsometryEquiv.norm_map] at h
  exact ⟨h.summable, h.tsum_eq.le⟩

theorem n07aAngularTail_schur (c : ℝ) (hc : 0 ≤ c) :
    (∀ l j : ℕ, 0 ≤ n07aAngularTail ((j : ℤ) - l) * c) ∧
    (∀ l : ℕ, Summable (fun j : ℕ => n07aAngularTail ((j : ℤ) - l) * c) ∧
      ∑' j : ℕ, n07aAngularTail ((j : ℤ) - l) * c ≤ (∑' k : ℤ, n07aAngularTail k) * c) ∧
    (∀ j : ℕ, Summable (fun l : ℕ => n07aAngularTail ((j : ℤ) - l) * c) ∧
      ∑' l : ℕ, n07aAngularTail ((j : ℤ) - l) * c ≤ (∑' k : ℤ, n07aAngularTail k) * c) := by
  have he (l j : ℕ) : n07aAngularTail ((j : ℤ) - l) = n07aAngularTail ((l : ℤ) - j) := by
    rw [← n07aAngularTail_neg, neg_sub]
  refine ⟨fun l j => mul_nonneg (n07aAngularTail_nonneg _) hc, ?_, ?_⟩
  · intro l
    simp_rw [he l]
    exact ⟨(n07aAngularTail_shift_summable l).mul_right c, by
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (n07aAngularTail_shift_tsum_le l) hc⟩
  · intro j
    exact ⟨(n07aAngularTail_shift_summable j).mul_right c, by
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (n07aAngularTail_shift_tsum_le j) hc⟩

theorem exists_n07aWeightedSchurOperator
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hI : ∀ m, K.left m < K.right m) (b p : ℕ)
    (R Q : V.level γ 0 b →L[ℝ] V.level γ 0 b) (κ : ℕ → ℕ → ℝ)
    (hQ : ∀ l j x, n07aAngularLevelBand hV γ 0 hI b l
      (Q (n07aAngularLevelBand hV γ 0 hI b j x)) =
      κ l j • n07aAngularLevelBand hV γ 0 hI b l
        (R (n07aAngularLevelBand hV γ 0 hI b j x)))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hblocks : ∀ U : V.level γ 0 (b + p), ∀ l j,
      ∃ W : V.level γ t (b + p), V.forget γ t (b + p) W =
        V.forget γ 0 b (κ l j • n07aAngularLevelBand hV γ 0 hI b l
          (R (n07aAngularLevelBand hV γ 0 hI b j
            (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)))) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (a * ‖n07aAngularLevelBand hV γ 0 hI (b + p) j U‖ +
            c * ‖n07aAngularLevelBand hV γ 0 hI b j
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)‖)) :
    ∃ A : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p), ∀ U,
      V.forget γ t (b + p) (A U) = V.forget γ 0 b
        (Q (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)) ∧
      ‖A U‖ ≤ (∑' k : ℤ, n07aAngularTail k) *
        (a * ‖U‖ + c * ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U‖) := by
  let : CompleteSpace (V.level γ t (b + p)) := n07aAngularLevelComplete hV γ t (b + p)
  let I := n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p)
  let J := n07aAngularMaterialToBaseLinear hD hT hV ht (Nat.le_add_right b p)
  let PI := n07aAngularLevelBand hV γ 0 hI (b + p)
  let PO := n07aAngularLevelBand hV γ t hI (b + p)
  let PB := n07aAngularLevelBand hV γ 0 hI b
  let τ : ℝ := ∑' k : ℤ, n07aAngularTail k
  have hτ : 0 ≤ τ := tsum_nonneg n07aAngularTail_nonneg
  have hi (j : ℕ) (U : V.level γ 0 (b + p)) : I (PI j U) = PB j (I U) :=
    n07aAngularLevelTruncate_band hV γ 0 hI (Nat.le_add_right b p) j U
  have hj (l : ℕ) (W : V.level γ t (b + p)) : PB l (J W) = J (PO l W) :=
    n07aAngularMaterialToBaseLinear_band hD hT hV ht (Nat.le_add_right b p) hI l W
  have hJ : Function.Injective J := by
    intro U W h
    apply hV.2.2.1 γ t (b + p)
    have h' := congrArg (V.forget γ 0 b) h
    simpa only [n07aAngularMaterialToBaseLinear_forget] using h'
  let f (l j : ℕ) : V.level γ 0 (b + p) →ₗ[ℝ] CanonicalSequence S K :=
    (V.forget γ 0 b).comp ((κ l j) • ((PB l).comp (R.comp ((PB j).comp I)))).toLinearMap
  have hf (l j : ℕ) (U : V.level γ 0 (b + p)) :
      ∃ W : V.level γ t (b + p), V.forget γ t (b + p) W = f l j U ∧
        ‖W‖ ≤ (n07aAngularTail ((j : ℤ) - l) * (a + c)) * ‖U‖ := by
    obtain ⟨W, hW, hn⟩ := hblocks U l j
    refine ⟨W, ?_, hn.trans ?_⟩
    · simpa only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] using hW
    · have h₀ := mul_le_mul_of_nonneg_left
        (n07aAngularLevelBand_norm_le hV γ 0 hI (b + p) j U) ha
      have h₁ := mul_le_mul_of_nonneg_left
        ((n07aAngularLevelBand_norm_le hV γ 0 hI b j (I U)).trans
          (n07aAngularLevelTruncate_norm_le hV γ 0 (Nat.le_add_right b p) U)) hc
      exact (mul_le_mul_of_nonneg_left (add_le_add h₀ h₁)
        (n07aAngularTail_nonneg _)).trans_eq (by ring)
  let A (l j : ℕ) : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p) :=
    n07aVolumeBoundedLift hV γ t (b + p) (f l j)
      (n07aAngularTail ((j : ℤ) - l) * (a + c)) (hf l j)
  have hactual (l j : ℕ) (U : V.level γ 0 (b + p)) :
      J (A l j U) = κ l j • PB l (R (PB j (I U))) := by
    apply hV.2.2.1 γ 0 b
    rw [n07aAngularMaterialToBaseLinear_forget, n07aVolumeBoundedLift_forget]
    simp only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  have hsharp (l j : ℕ) (U : V.level γ 0 (b + p)) :
      ‖A l j U‖ ≤ n07aAngularTail ((j : ℤ) - l) *
        (a * ‖PI j U‖ + c * ‖PB j (I U)‖) := by
    obtain ⟨W, hW, hn⟩ := hblocks U l j
    have he : A l j U = W := by
      apply hV.2.2.1 γ t (b + p)
      rw [n07aVolumeBoundedLift_forget]
      simpa only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] using hW.symm
    rwa [he]
  have hcompI (i j : ℕ) (U : V.level γ 0 (b + p)) :
      PI i (PI j U) = if i = j then PI j U else 0 := by
    by_cases h : i = j
    · subst i
      simpa only [ite_true] using n07aAngularLevelBand_idempotent hV γ 0 hI (b + p) j U
    · simpa only [if_neg h] using n07aAngularLevelBand_comp_eq_zero hV γ 0 hI (b + p) h U
  have hcompO (i j : ℕ) (W : V.level γ t (b + p)) :
      PO i (PO j W) = if i = j then PO j W else 0 := by
    by_cases h : i = j
    · subst i
      simpa only [ite_true] using n07aAngularLevelBand_idempotent hV γ t hI (b + p) j W
    · simpa only [if_neg h] using n07aAngularLevelBand_comp_eq_zero hV γ t hI (b + p) h W
  have hcompB (i j : ℕ) (x : V.level γ 0 b) : PB i (PB j x) = if i = j then PB j x else 0 := by
    by_cases h : i = j
    · subst i
      simpa only [ite_true] using n07aAngularLevelBand_idempotent hV γ 0 hI b j x
    · simpa only [if_neg h] using n07aAngularLevelBand_comp_eq_zero hV γ 0 hI b h x
  have hleft (l j : ℕ) (U : V.level γ 0 (b + p)) : PO l (A l j U) = A l j U := by
    apply hJ
    rw [← hj, hactual, map_smul, hcompB, ite_true]
  have hright (l j k : ℕ) (U : V.level γ 0 (b + p)) :
      A l j (PI k U) = if j = k then A l j U else 0 := by
    apply hJ
    rw [hactual, hi, hcompB]
    by_cases h : j = k
    · subst k
      rw [if_pos rfl, if_pos rfl, hactual]
    · rw [if_neg h, if_neg h, map_zero, map_zero, smul_zero, map_zero]
  have hsI := n07aAngularLevelBand_square_budget hV γ 0 hI (b + p)
  have hsB := n07aAngularLevelBand_square_budget hV γ 0 hI b
  have hsO := n07aAngularLevelBand_square_budget hV γ t hI (b + p)
  have hsa := n07aAngularTail_schur a ha
  have hsc := n07aAngularTail_schur c hc
  obtain ⟨Z, _, hnorm, hpair⟩ := exists_n07aSchurRiesz_oneHigh
    (n07aSchurLiftBlockForm PO A) I
    (fun j U => ‖PI j U‖) (fun j U => ‖PB j (I U)‖) (fun l W => ‖PO l W‖)
    (fun l j => n07aAngularTail ((j : ℤ) - l) * a)
    (fun l j => n07aAngularTail ((j : ℤ) - l) * c)
    (mul_nonneg hτ ha) (mul_nonneg hτ ha) (mul_nonneg hτ hc) (mul_nonneg hτ hc)
    hsa.1 hsc.1 hsa.2.1 hsa.2.2 hsc.2.1 hsc.2.2
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    hsI (fun U => hsB (I U)) hsO (fun i U W => by
      rw [n07aSchurLiftBlockForm_apply]
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_mul_of_nonneg_right (hsharp i.1 i.2 U) (norm_nonneg (PO i.1 W))).trans_eq
          (by ring)))
  have hzblock (l j : ℕ) (U : V.level γ 0 (b + p)) : PO l (Z (PI j U)) = A l j U :=
    n07aSchurLift_block PI PO A Z hcompO
      (n07aAngularLevelBand_symmetric hV γ t hI (b + p)) hleft hright
      (fun U W => by simpa only [n07aSchurLiftBlockForm_apply] using hpair U W) l j U
  have hsame (U : V.level γ 0 (b + p)) : J (Z U) = Q (I U) := by
    apply n07aSchurLift_eq_original PI PO PB A Z J (Q.comp I)
      (n07aAngularLevelBand_hasSum hV γ 0 hI (b + p))
      (n07aAngularLevelBand_total hV γ 0 hI b) hj hzblock
    intro l j x
    rw [hactual, ContinuousLinearMap.comp_apply, hi, hQ]
  refine ⟨Z, fun U => ⟨?_, ?_⟩⟩
  · have h := congrArg (V.forget γ 0 b) (hsame U)
    simpa only [n07aAngularMaterialToBaseLinear_forget] using h
  · have h := hnorm U
    rw [Real.sqrt_mul_self (mul_nonneg hτ ha), Real.sqrt_mul_self (mul_nonneg hτ hc)] at h
    exact h.trans_eq (by ring)

end ContinuousFlexibility.Analysis
