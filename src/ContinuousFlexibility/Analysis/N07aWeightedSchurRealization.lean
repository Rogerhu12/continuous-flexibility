module

public import ContinuousFlexibility.Analysis.N07aMaterialEmbeddingLinear
public import ContinuousFlexibility.Analysis.N07aSchurLiftIdentity
public import ContinuousFlexibility.Analysis.N07aAngularCommutatorDomain
public import ContinuousFlexibility.Analysis.N07aAngularBandLift
public import ContinuousFlexibility.Analysis.N07aCircleCoefficientDecay

/-!
# Schur realization in the actual weighted source graph

The supplied block realizations are unique because the prescribed forget
map is injective. Their Riesz sum is identified with the same base
operator after the genuine material inclusion. No unbounded series of
vectors is inferred from a scalar weak sum.
-/

@[expose] public section

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

private theorem n07aWeightedSchurBandComposition
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (hI : ∀ m, K.left m < K.right m)
    (s i j : ℕ) (u : V.level γ t s) :
    n07aAngularLevelBand hV γ t hI s i (n07aAngularLevelBand hV γ t hI s j u) =
      if i = j then n07aAngularLevelBand hV γ t hI s j u else 0 := by
  by_cases h : i = j
  · subst i
    rw [ite_eq_left rfl]
    exact n07aAngularLevelBand_idempotent hV γ t hI s j u
  · rw [ite_eq_right h]
    exact n07aAngularLevelBand_comp_eq_zero hV γ t hI s h u

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

private theorem exists_n07aWeightedSchurBlocks
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hI : ∀ m, K.left m < K.right m) (b p : ℕ)
    (R : V.level γ 0 b →L[ℝ] V.level γ 0 b) (κ : ℕ → ℕ → ℝ)
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
    ∃ A : ℕ → ℕ → V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p),
      (∀ l j U, n07aAngularMaterialToBaseLinear hD hT hV ht (Nat.le_add_right b p)
        (A l j U) = κ l j • n07aAngularLevelBand hV γ 0 hI b l
          (R (n07aAngularLevelBand hV γ 0 hI b j
            (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)))) ∧
      (∀ l j U, ‖A l j U‖ ≤ n07aAngularTail ((j : ℤ) - l) *
        (a * ‖n07aAngularLevelBand hV γ 0 hI (b + p) j U‖ +
          c * ‖n07aAngularLevelBand hV γ 0 hI b j
            (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)‖)) := by
  let I := n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p)
  let PB := n07aAngularLevelBand hV γ 0 hI b
  let f (l j : ℕ) : V.level γ 0 (b + p) →ₗ[ℝ] CanonicalSequence S K :=
    (V.forget γ 0 b).comp ((κ l j) • ((PB l).comp (R.comp ((PB j).comp I)))).toLinearMap
  have hfapply (l j : ℕ) (U : V.level γ 0 (b + p)) :
      f l j U = V.forget γ 0 b (κ l j • PB l (R (PB j (I U)))) := by
    simp only [f, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      smul_apply, ContinuousLinearMap.comp_apply]
  have hf (l j : ℕ) (U : V.level γ 0 (b + p)) :
      ∃ W : V.level γ t (b + p), V.forget γ t (b + p) W = f l j U ∧
        ‖W‖ ≤ (n07aAngularTail ((j : ℤ) - l) * (a + c)) * ‖U‖ := by
    obtain ⟨W, hW, hn⟩ := hblocks U l j
    refine ⟨W, hW.trans (hfapply l j U).symm, hn.trans ?_⟩
    have h₀ := mul_le_mul_of_nonneg_left
      (n07aAngularLevelBand_norm_le hV γ 0 hI (b + p) j U) ha
    have h₁ := mul_le_mul_of_nonneg_left
      ((n07aAngularLevelBand_norm_le hV γ 0 hI b j (I U)).trans
        (n07aAngularLevelTruncate_norm_le hV γ 0 (Nat.le_add_right b p) U)) hc
    exact (mul_le_mul_of_nonneg_left (add_le_add h₀ h₁)
      (n07aAngularTail_nonneg _)).trans_eq (by ring)
  let A (l j : ℕ) : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p) :=
    n07aVolumeBoundedLift hV γ t (b + p) (f l j)
      (n07aAngularTail ((j : ℤ) - l) * (a + c)) (hf l j)
  have hforget (l j : ℕ) (U : V.level γ 0 (b + p)) :
      V.forget γ t (b + p) (A l j U) = f l j U :=
    n07aVolumeBoundedLift_forget hV γ t (b + p) (f l j)
      (n07aAngularTail ((j : ℤ) - l) * (a + c)) (hf l j) U
  refine ⟨A, ?_, ?_⟩
  · intro l j U
    apply hV.2.2.1 γ 0 b
    rw [n07aAngularMaterialToBaseLinear_forget]
    exact (hforget l j U).trans (hfapply l j U)
  · intro l j U
    obtain ⟨W, hW, hn⟩ := hblocks U l j
    have he : A l j U = W :=
      (hV.2.2.1 γ t (b + p))
        ((hforget l j U).trans ((hfapply l j U).trans hW.symm))
    rwa [he]

private theorem n07aWeightedSchurBlockAlgebra
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (PI : ℕ → E →L[ℝ] E) (PO : ℕ → F →L[ℝ] F) (PB : ℕ → H →L[ℝ] H)
    (I : E →L[ℝ] H) (J : F →L[ℝ] H) (R : H →L[ℝ] H)
    (κ : ℕ → ℕ → ℝ) (A : ℕ → ℕ → E →L[ℝ] F)
    (hcompB : ∀ i j x, PB i (PB j x) = if i = j then PB j x else 0)
    (hi : ∀ j x, I (PI j x) = PB j (I x))
    (hj : ∀ l y, PB l (J y) = J (PO l y)) (hJ : Function.Injective J)
    (hactual : ∀ l j x, J (A l j x) = κ l j • PB l (R (PB j (I x)))) :
    (∀ l j x, PO l (A l j x) = A l j x) ∧
      (∀ l j k x, A l j (PI k x) = if j = k then A l j x else 0) := by
  constructor
  · intro l j x
    apply hJ
    rw [← hj, hactual, map_smul, hcompB, ite_eq_left rfl]
  · intro l j k x
    apply hJ
    rw [hactual, hi, hcompB]
    by_cases h : j = k
    · subst k
      rw [ite_eq_left rfl, ite_eq_left rfl, hactual]
    · rw [ite_eq_right h, ite_eq_right h, map_zero, map_zero, smul_zero, map_zero]

private theorem exists_n07aSchurRealization
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (PI : ℕ → E →L[ℝ] E) (PO : ℕ → F →L[ℝ] F) (PB : ℕ → H →L[ℝ] H)
    (I : E →L[ℝ] H) (J : F →L[ℝ] H) (Q : H →L[ℝ] H)
    (A : ℕ → ℕ → E →L[ℝ] F) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcompO : ∀ i j y, PO i (PO j y) = if i = j then PO j y else 0)
    (hsymm : ∀ i x y, ⟪PO i x, y⟫ = ⟪x, PO i y⟫)
    (hleft : ∀ l j x, PO l (A l j x) = A l j x)
    (hright : ∀ l j k x, A l j (PI k x) = if j = k then A l j x else 0)
    (hsI : ∀ x, Summable (fun j => ‖PI j x‖ ^ 2) ∧ ∑' j, ‖PI j x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hsB : ∀ x, Summable (fun j => ‖PB j x‖ ^ 2) ∧ ∑' j, ‖PB j x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hsO : ∀ y, Summable (fun l => ‖PO l y‖ ^ 2) ∧ ∑' l, ‖PO l y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hsum : ∀ x, HasSum (fun j => PI j x) x)
    (htotal : ∀ x : H, (∀ l, PB l x = 0) → x = 0)
    (hinter : ∀ l y, PB l (J y) = J (PO l y))
    (hactual : ∀ l j x, J (A l j x) = PB l (Q (I (PI j x))))
    (hsharp : ∀ l j x, ‖A l j x‖ ≤ n07aAngularTail ((j : ℤ) - l) *
      (a * ‖PI j x‖ + c * ‖PB j (I x)‖)) :
    ∃ Z : E →L[ℝ] F, ∀ x, J (Z x) = Q (I x) ∧
      ‖Z x‖ ≤ (∑' k : ℤ, n07aAngularTail k) * (a * ‖x‖ + c * ‖I x‖) := by
  let τ : ℝ := ∑' k : ℤ, n07aAngularTail k
  have hτ : 0 ≤ τ := tsum_nonneg n07aAngularTail_nonneg
  have hsa := n07aAngularTail_schur a ha
  have hsc := n07aAngularTail_schur c hc
  obtain ⟨Z, _, hnorm, hpair⟩ := exists_n07aSchurRiesz_oneHigh
    (n07aSchurLiftBlockForm PO A) I
    (fun j x => ‖PI j x‖) (fun j x => ‖PB j (I x)‖) (fun l y => ‖PO l y‖)
    (fun l j => n07aAngularTail ((j : ℤ) - l) * a)
    (fun l j => n07aAngularTail ((j : ℤ) - l) * c)
    (mul_nonneg hτ ha) (mul_nonneg hτ ha) (mul_nonneg hτ hc) (mul_nonneg hτ hc)
    hsa.1 hsc.1 hsa.2.1 hsa.2.2 hsc.2.1 hsc.2.2
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    hsI (fun x => hsB (I x)) hsO (fun i x y => by
      rw [n07aSchurLiftBlockForm_apply]
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_mul_of_nonneg_right (hsharp i.1 i.2 x) (norm_nonneg (PO i.1 y))).trans_eq
          (by ring)))
  have hzblock (l j : ℕ) (x : E) : PO l (Z (PI j x)) = A l j x :=
    n07aSchurLift_block PI PO A Z hcompO hsymm hleft hright
      (fun x y => by simpa only [n07aSchurLiftBlockForm_apply] using hpair x y) l j x
  have hsame := n07aSchurLift_eq_original PI PO PB A Z J (Q.comp I)
    hsum htotal hinter hzblock
    (fun l j x => by simpa only [ContinuousLinearMap.comp_apply] using hactual l j x)
  refine ⟨Z, fun x => ⟨hsame x, ?_⟩⟩
  have h := hnorm x
  rw [Real.sqrt_mul_self (mul_nonneg hτ ha), Real.sqrt_mul_self (mul_nonneg hτ hc)] at h
  exact h.trans_eq (by ring)

private theorem exists_n07aWeightedSchurAssembly
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hI : ∀ m, K.left m < K.right m) (b p : ℕ)
    (R Q : V.level γ 0 b →L[ℝ] V.level γ 0 b) (κ : ℕ → ℕ → ℝ)
    (hQ : ∀ (l j : ℕ) (x : V.level γ 0 b), n07aAngularLevelBand hV γ 0 hI b l
      (Q (n07aAngularLevelBand hV γ 0 hI b j x)) =
      κ l j • n07aAngularLevelBand hV γ 0 hI b l
        (R (n07aAngularLevelBand hV γ 0 hI b j x)))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (A : ℕ → ℕ → V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p))
    (hactualRaw : ∀ (l j : ℕ) (U : V.level γ 0 (b + p)),
      n07aAngularMaterialToBaseLinear hD hT hV ht (Nat.le_add_right b p) (A l j U) =
        κ l j • n07aAngularLevelBand hV γ 0 hI b l
          (R (n07aAngularLevelBand hV γ 0 hI b j
            (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U))))
    (hsharpRaw : ∀ (l j : ℕ) (U : V.level γ 0 (b + p)), ‖A l j U‖ ≤ n07aAngularTail ((j : ℤ) - l) *
      (a * ‖n07aAngularLevelBand hV γ 0 hI (b + p) j U‖ +
        c * ‖n07aAngularLevelBand hV γ 0 hI b j
          (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)‖)) :
    ∃ Z : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p), ∀ U,
      V.forget γ t (b + p) (Z U) = V.forget γ 0 b
        (Q (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)) ∧
      ‖Z U‖ ≤ (∑' k : ℤ, n07aAngularTail k) *
        (a * ‖U‖ + c * ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U‖) := by
  let : CompleteSpace (V.level γ t (b + p)) := n07aAngularLevelComplete hV γ t (b + p)
  let I : V.level γ 0 (b + p) →L[ℝ] V.level γ 0 b := n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p)
  let J : V.level γ t (b + p) →L[ℝ] V.level γ 0 b :=
    n07aAngularMaterialToBaseLinear hD hT hV (γ := γ) ht (Nat.le_add_right b p)
  let PI : ℕ → V.level γ 0 (b + p) →L[ℝ] V.level γ 0 (b + p) := n07aAngularLevelBand hV γ 0 hI (b + p)
  let PO : ℕ → V.level γ t (b + p) →L[ℝ] V.level γ t (b + p) := n07aAngularLevelBand hV γ t hI (b + p)
  let PB : ℕ → V.level γ 0 b →L[ℝ] V.level γ 0 b := n07aAngularLevelBand hV γ 0 hI b
  have hi (j : ℕ) (U : V.level γ 0 (b + p)) : I (PI j U) = PB j (I U) :=
    n07aAngularLevelTruncate_band hV γ 0 hI (Nat.le_add_right b p) j U
  have hj (l : ℕ) (W : V.level γ t (b + p)) : PB l (J W) = J (PO l W) :=
    n07aAngularMaterialToBaseLinear_band hD hT hV ht (Nat.le_add_right b p) hI l W
  have hJ : Function.Injective J := by
    intro U W h
    apply hV.2.2.1 γ t (b + p)
    have h' := congrArg (V.forget γ 0 b) h
    simpa only [J, n07aAngularMaterialToBaseLinear_forget] using h'
  have hactual (l j : ℕ) (U : V.level γ 0 (b + p)) :
      J (A l j U) = κ l j • PB l (R (PB j (I U))) := hactualRaw l j U
  have hsharp (l j : ℕ) (U : V.level γ 0 (b + p)) :
      ‖A l j U‖ ≤ n07aAngularTail ((j : ℤ) - l) *
        (a * ‖PI j U‖ + c * ‖PB j (I U)‖) := hsharpRaw l j U
  have hcompO : ∀ (i j : ℕ) (x : V.level γ t (b + p)),
      PO i (PO j x) = if i = j then PO j x else 0 := n07aWeightedSchurBandComposition hV γ t hI (b + p)
  have hcompB : ∀ (i j : ℕ) (x : V.level γ 0 b),
      PB i (PB j x) = if i = j then PB j x else 0 := n07aWeightedSchurBandComposition hV γ 0 hI b
  have halgebra := n07aWeightedSchurBlockAlgebra PI PO PB I J R κ A
    hcompB hi hj hJ hactual
  let realization := exists_n07aSchurRealization PI PO PB I J Q A ha hc hcompO
    (n07aAngularLevelBand_symmetric hV γ t hI (b + p)) halgebra.1 halgebra.2
    (n07aAngularLevelBand_square_budget hV γ 0 hI (b + p))
    (n07aAngularLevelBand_square_budget hV γ 0 hI b)
    (n07aAngularLevelBand_square_budget hV γ t hI (b + p))
    (n07aAngularLevelBand_hasSum hV γ 0 hI (b + p))
    (n07aAngularLevelBand_total hV γ 0 hI b) hj
    (fun l j U => (hactual l j U).trans
      ((hQ l j (I U)).symm.trans
        (congrArg (fun x : V.level γ 0 b => PB l (Q x)) (hi j U).symm))) hsharp
  let Z : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p) := realization.choose
  have hZ := realization.choose_spec
  refine ⟨Z, fun U => ⟨?_, (hZ U).2⟩⟩
  have h := congrArg (V.forget γ 0 b) (hZ U).1
  simpa only [J, n07aAngularMaterialToBaseLinear_forget] using h

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
  let blocks := exists_n07aWeightedSchurBlocks hD hT hV γ ht hI b p R κ ha hc hblocks
  exact exists_n07aWeightedSchurAssembly hD hT hV γ ht hI b p R Q κ hQ ha hc
    blocks.choose blocks.choose_spec.1 blocks.choose_spec.2

end ContinuousFlexibility.Analysis
