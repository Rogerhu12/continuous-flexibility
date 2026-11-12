import ContinuousFlexibility.Analysis.N07aVolumeLinearLift
import ContinuousFlexibility.Analysis.N07aAngularCanonicalProjection
import ContinuousFlexibility.Analysis.N07aAngularCommutatorDomain
import ContinuousFlexibility.Analysis.N07aSchurLiftIdentity
import ContinuousFlexibility.Analysis.N07aCircleCoefficientDecay
import ContinuousFlexibility.Analysis.N06CanonicalTestSeparation
import ContinuousFlexibility.Analysis.N06PhysicalTestCoordinates
import ContinuousFlexibility.Analysis.N07aCanonicalWeakJets

/-!
# A Schur operator with the prescribed actual canonical source

Only the individual angular blocks are initially realized in the given
source level.  Schur summability constructs a bounded operator there.
Its actual source is identified first on a single input band and then
on all inputs by continuous compact-test pairings.  Continuity of the
unassembled sequence-valued source is not an assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory Statements
open scoped RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {γ t : ℝ} {s : ℕ}

local instance n06SourceSchurLevelGroup : NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _
local instance n06SourceSchurLevelSpace : NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _
local instance n06SourceSchurLevelInner : InnerProductSpace ℝ (V.level γ t s) :=
  Submodule.innerProductSpace _

private theorem n06_sourceSchur_band_bessel
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (F : V.level γ t s) :
    Summable (fun j => ‖n07aAngularLevelBand hV γ t hI s j F‖ ^ 2) ∧
      ∑' j, ‖n07aAngularLevelBand hV γ t hI s j F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  let e := n07aAngularHilbertEquiv hV γ t hI s
  have he (j : ℕ) : ‖e F j‖ = ‖n07aAngularLevelBand hV γ t hI s j F‖ := by
    rw [← Submodule.norm_coe]
    exact congrArg norm (n07aAngularHilbertEquiv_apply_val hV γ t hI s F j)
  refine ⟨?_, ?_⟩
  · simpa only [he] using angular_summable_norm_sq (e F)
  · calc
      _ = ∑' j, ‖e F j‖ ^ 2 := tsum_congr (fun j => by rw [he])
      _ = ‖e F‖ ^ 2 := angular_tsum_norm_sq (e F)
      _ = ‖F‖ ^ 2 := congrArg (fun x : ℝ => x ^ 2) (e.norm_map F)
      _ ≤ ‖F‖ ^ 2 := le_rfl

private theorem n06_sourceSchur_tail_swap (j l : ℕ) :
    n07aAngularTail ((j : ℤ) - l) = n07aAngularTail ((l : ℤ) - j) := by
  rw [show (j : ℤ) - l = -((l : ℤ) - j) by ring, n07aAngularTail_neg]

private theorem n06_sourceSchur_projection_comp
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (i j : ℕ) (F : V.level γ t s) :
    n07aAngularLevelBand hV γ t hI s i (n07aAngularLevelBand hV γ t hI s j F) =
      if i = j then n07aAngularLevelBand hV γ t hI s j F else 0 := by
  by_cases hij : i = j
  · subst i
    exact (n07aAngularLevelBand_idempotent hV γ t hI s j F).trans (if_pos rfl).symm
  · rw [if_neg hij]
    exact n07aAngularLevelBand_comp_eq_zero hV γ t hI s hij F

private theorem n06_sourceSchur_block_family
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (f : V.level γ t s →ₗ[ℝ] CanonicalSequence S K)
    (A : ℝ) (hA : 0 ≤ A)
    (hblocks : ∀ j l (F : V.level γ t s),
      n07aAngularLevelBand hV γ t hI s j F = F →
      ∃ G : V.level γ t s,
        V.forget γ t s G = n07aAngularSequenceBand hI l (f F) ∧
        ‖G‖ ≤ A * n07aAngularTail ((j : ℤ) - l) * ‖F‖) :
    ∃ blocks : ℕ → ℕ → V.level γ t s →L[ℝ] V.level γ t s,
      (∀ l j F, V.forget γ t s (blocks l j F) =
        n07aAngularSequenceBand hI l (f (n07aAngularLevelBand hV γ t hI s j F))) ∧
      (∀ l j F, ‖blocks l j F‖ ≤ A * n07aAngularTail ((j : ℤ) - l) *
        ‖n07aAngularLevelBand hV γ t hI s j F‖) ∧
      (∀ l j F, n07aAngularLevelBand hV γ t hI s l (blocks l j F) = blocks l j F) ∧
      (∀ l j k F, blocks l j (n07aAngularLevelBand hV γ t hI s k F) =
        if j = k then blocks l j F else 0) := by
  let P : ℕ → V.level γ t s →L[ℝ] V.level γ t s :=
    fun j => n07aAngularLevelBand hV γ t hI s j
  let fb (l j : ℕ) : V.level γ t s →ₗ[ℝ] CanonicalSequence S K :=
    LinearMap.pi (fun m => (n07aAngularBand m (hI m) l).toLinearMap.comp
      ((LinearMap.proj m).comp (f.comp (P j).toLinearMap)))
  have hfb (l j : ℕ) (F : V.level γ t s) :
      fb l j F = n07aAngularSequenceBand hI l (f (P j F)) := by
    funext m
    simp only [fb, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      ContinuousLinearMap.coe_coe, n07aAngularSequenceBand_apply]
  have hex (l j : ℕ) (F : V.level γ t s) :
      ∃ G : V.level γ t s, V.forget γ t s G = fb l j F ∧
        ‖G‖ ≤ (A * n07aAngularTail ((j : ℤ) - l)) * ‖F‖ := by
    obtain ⟨G, hG, hn⟩ := hblocks j l (P j F)
      (n07aAngularLevelBand_idempotent hV γ t hI s j F)
    refine ⟨G, hG.trans (hfb l j F).symm, hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (n07aAngularLevelBand_norm_le hV γ t hI s j F)
      (mul_nonneg hA (n07aAngularTail_nonneg _))
  let blocks (l j : ℕ) : V.level γ t s →L[ℝ] V.level γ t s :=
    n07aVolumeBoundedLift hV γ t s (fb l j)
      (A * n07aAngularTail ((j : ℤ) - l)) (hex l j)
  have hforget (l j : ℕ) (F : V.level γ t s) :
      V.forget γ t s (blocks l j F) = n07aAngularSequenceBand hI l (f (P j F)) :=
    (n07aVolumeBoundedLift_forget hV γ t s (fb l j)
      (A * n07aAngularTail ((j : ℤ) - l)) (hex l j) F).trans (hfb l j F)
  have hnorm (l j : ℕ) (F : V.level γ t s) :
      ‖blocks l j F‖ ≤ A * n07aAngularTail ((j : ℤ) - l) * ‖P j F‖ := by
    obtain ⟨G, hG, hn⟩ := hblocks j l (P j F)
      (n07aAngularLevelBand_idempotent hV γ t hI s j F)
    have he : blocks l j F = G := (hV.2.2.1 γ t s) ((hforget l j F).trans hG.symm)
    rw [he]
    exact hn
  have hcomp (i j : ℕ) (F : V.level γ t s) :
      P i (P j F) = if i = j then P j F else 0 :=
    n06_sourceSchur_projection_comp hV hI i j F
  have hleft (l j : ℕ) (F : V.level γ t s) : P l (blocks l j F) = blocks l j F := by
    apply hV.2.2.1 γ t s
    rw [n07aAngularLevelBand_forget, hforget]
    funext m
    simp only [n07aAngularSequenceBand_apply, n07aAngularBand_idempotent]
  have hright (l j k : ℕ) (F : V.level γ t s) :
      blocks l j (P k F) = if j = k then blocks l j F else 0 := by
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl]
      apply hV.2.2.1 γ t s
      rw [hforget, hforget, hcomp, if_pos rfl]
    · rw [if_neg hjk]
      apply hV.2.2.1 γ t s
      have hzero : P j (P k F) = 0 := (hcomp j k F).trans (if_neg hjk)
      have hfzero : f (P j (P k F)) = 0 := (congrArg f hzero).trans f.map_zero
      calc
        V.forget γ t s (blocks l j (P k F)) =
            n07aAngularSequenceBand hI l (f (P j (P k F))) := hforget l j (P k F)
        _ = n07aAngularSequenceBand hI l 0 :=
          congrArg (n07aAngularSequenceBand hI l) hfzero
        _ = 0 := by
          funext m
          exact (n07aAngularBand m (hI m) l).map_zero
        _ = V.forget γ t s 0 := (V.forget γ t s).map_zero.symm
  exact ⟨blocks, hforget, hnorm, hleft, hright⟩

private theorem n06_sourceSchur_assemble
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (P : ℕ → E →L[ℝ] E) (blocks : ℕ → ℕ → E →L[ℝ] E)
    (A : ℝ) (hA : 0 ≤ A)
    (hcomp : ∀ i j F, P i (P j F) = if i = j then P j F else 0)
    (hsymm : ∀ i F G, inner ℝ (P i F) G = inner ℝ F (P i G))
    (hleft : ∀ l j F, P l (blocks l j F) = blocks l j F)
    (hright : ∀ l j k F, blocks l j (P k F) = if j = k then blocks l j F else 0)
    (hbessel : ∀ F, Summable (fun j => ‖P j F‖ ^ 2) ∧
      ∑' j, ‖P j F‖ ^ 2 ≤ ‖F‖ ^ 2)
    (hnorm : ∀ l j F, ‖blocks l j F‖ ≤
      A * n07aAngularTail ((j : ℤ) - l) * ‖P j F‖) :
    ∃ M : E →L[ℝ] E, ‖M‖ ≤ A * ∑' k : ℤ, n07aAngularTail k ∧
      ∀ l j F, P l (M (P j F)) = blocks l j F := by
  let a : ℕ → ℕ → ℝ := fun l j => A * n07aAngularTail ((j : ℤ) - l)
  let total : ℝ := ∑' k : ℤ, n07aAngularTail k
  have htotal : 0 ≤ total := tsum_nonneg n07aAngularTail_nonneg
  have ha (l j : ℕ) : 0 ≤ a l j := mul_nonneg hA (n07aAngularTail_nonneg _)
  have hrow (l : ℕ) : Summable (fun j => a l j) ∧ ∑' j, a l j ≤ A * total := by
    have he : (fun j : ℕ => a l j) = fun j : ℕ => A * n07aAngularTail ((l : ℤ) - j) := by
      funext j
      rw [a, n06_sourceSchur_tail_swap]
    rw [he]
    refine ⟨(n07aAngularTail_shift_summable l).mul_left A, ?_⟩
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (n07aAngularTail_shift_tsum_le l) hA
  have hcol (j : ℕ) : Summable (fun l => a l j) ∧ ∑' l, a l j ≤ A * total := by
    refine ⟨(n07aAngularTail_shift_summable j).mul_left A, ?_⟩
    change (∑' l : ℕ, A * n07aAngularTail ((j : ℤ) - l)) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (n07aAngularTail_shift_tsum_le j) hA
  have hb (i : ℕ × ℕ) (F G : E) :
      ‖n07aSchurLiftBlockForm P blocks i F G‖ ≤ a i.1 i.2 * ‖P i.1 G‖ * ‖P i.2 F‖ := by
    rw [n07aSchurLiftBlockForm_apply]
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right (hnorm i.1 i.2 F) (norm_nonneg _)).trans_eq (by dsimp only [a]; ring))
  obtain ⟨M, hMn, hMpair⟩ := exists_n07aSchurRiesz
    (n07aSchurLiftBlockForm P blocks)
    (fun j F => ‖P j F‖) (fun l G => ‖P l G‖) a
    (mul_nonneg hA htotal) (mul_nonneg hA htotal) ha hrow hcol
    (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    hbessel hbessel hb
  have hMpair' (F G : E) : inner ℝ (M F) G =
      ∑' i : ℕ × ℕ, inner ℝ (blocks i.1 i.2 F) (P i.1 G) := by
    simpa only [n07aSchurLiftBlockForm_apply] using hMpair F G
  have hMblock (l j : ℕ) (F : E) : P l (M (P j F)) = blocks l j F :=
    n07aSchurLift_block P P blocks M hcomp
      hsymm hleft hright hMpair' l j F
  refine ⟨M, ?_, hMblock⟩
  simpa only [← pow_two, Real.sqrt_sq (mul_nonneg hA htotal)] using hMn

private theorem n06_sourceSchur_band_identification
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (f : V.level γ t s →ₗ[ℝ] CanonicalSequence S K)
    (blocks : ℕ → ℕ → V.level γ t s →L[ℝ] V.level γ t s)
    (M : V.level γ t s →L[ℝ] V.level γ t s)
    (hforget : ∀ l j F, V.forget γ t s (blocks l j F) =
      n07aAngularSequenceBand hI l (f (n07aAngularLevelBand hV γ t hI s j F)))
    (hMblock : ∀ l j F,
      n07aAngularLevelBand hV γ t hI s l (M (n07aAngularLevelBand hV γ t hI s j F)) =
        blocks l j F) :
    ∀ j F, V.forget γ t s (M (n07aAngularLevelBand hV γ t hI s j F)) =
      f (n07aAngularLevelBand hV γ t hI s j F) := by
  intro j F
  funext m
  have he (l : ℕ) :
      n07aAngularBand m (hI m) l
          (V.forget γ t s (M (n07aAngularLevelBand hV γ t hI s j F)) m) =
        n07aAngularBand m (hI m) l (f (n07aAngularLevelBand hV γ t hI s j F) m) := by
    have hh := congrArg (fun X : V.level γ t s => V.forget γ t s X m) (hMblock l j F)
    simpa only [n07aAngularLevelBand_forget, hforget,
      n07aAngularSequenceBand_apply] using hh
  have hs₁ := n07aAngularBand_hasSum m (hI m)
    (V.forget γ t s (M (n07aAngularLevelBand hV γ t hI s j F)) m)
  have hs₂ := n07aAngularBand_hasSum m (hI m)
    (f (n07aAngularLevelBand hV γ t hI s j F) m)
  simp_rw [he] at hs₁
  exact hs₁.unique hs₂

private theorem n06_sourceSchur_identify
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (f : V.level γ t s →ₗ[ℝ] CanonicalSequence S K)
    (Q : ∀ m (φ : PolarPoint → ℝ), CanonicalTest S K m φ → V.level γ t s →L[ℝ] ℝ)
    (hQ : ∀ F m (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ),
      n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ) (f F m) = Q m φ hφ F)
    (M : V.level γ t s →L[ℝ] V.level γ t s)
    (hband : ∀ j F, V.forget γ t s (M (n07aAngularLevelBand hV γ t hI s j F)) =
      f (n07aAngularLevelBand hV γ t hI s j F)) :
    ∀ F, V.forget γ t s (M F) = f F := by
  let P : ℕ → V.level γ t s →L[ℝ] V.level γ t s :=
    fun j => n07aAngularLevelBand hV γ t hI s j
  intro F
  funext m
  apply n06_canonicalL2_test_ext
  intro φ hφ
  let q := n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ)
  let L : V.level γ t s →L[ℝ] ℝ :=
    q.comp ((n06VolumeCoordinate T V γ t s m).comp M)
  have hL (X : V.level γ t s) : L X = q (V.forget γ t s (M X) m) := by
    simp only [L, ContinuousLinearMap.comp_apply, n06VolumeCoordinate_apply hV]
  have hseq (j : ℕ) : L (P j F) = Q m φ hφ (P j F) := by
    rw [hL, hband]
    exact hQ (P j F) m φ hφ
  have h₁ := (n07aAngularLevelBand_hasSum hV γ t hI s F).mapL L
  have h₂ := (n07aAngularLevelBand_hasSum hV γ t hI s F).mapL (Q m φ hφ)
  change HasSum (fun j => L (P j F)) (L F) at h₁
  simp_rw [hseq] at h₁
  have he : L F = Q m φ hφ F := h₁.unique h₂
  rw [← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ),
    ← n07aCanonicalTestPairing_apply φ (n07a_canonicalTest_memLp hφ)]
  exact (hL F).symm.trans (he.trans (hQ F m φ hφ).symm)

theorem n06_canonicalSource_schur
    (hV : IsVolumeModel T S K V) (hI : ∀ m, K.left m < K.right m)
    (f : V.level γ t s →ₗ[ℝ] CanonicalSequence S K)
    (Q : ∀ m (φ : PolarPoint → ℝ), CanonicalTest S K m φ → V.level γ t s →L[ℝ] ℝ)
    (hQ : ∀ F m (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ),
      n07aCanonicalTestPairing φ (n07a_canonicalTest_memLp hφ) (f F m) = Q m φ hφ F)
    (A : ℝ) (hA : 0 ≤ A)
    (hblocks : ∀ j l (F : V.level γ t s),
      n07aAngularLevelBand hV γ t hI s j F = F →
      ∃ G : V.level γ t s,
        V.forget γ t s G = n07aAngularSequenceBand hI l (f F) ∧
        ‖G‖ ≤ A * n07aAngularTail ((j : ℤ) - l) * ‖F‖) :
    ∃ M : V.level γ t s →L[ℝ] V.level γ t s,
      ‖M‖ ≤ A * ∑' k : ℤ, n07aAngularTail k ∧
      ∀ F, V.forget γ t s (M F) = f F := by
  letI : CompleteSpace (V.level γ t s) := n07aAngularLevelComplete hV γ t s
  obtain ⟨blocks, hforget, hnorm, hleft, hright⟩ :=
    n06_sourceSchur_block_family hV hI f A hA hblocks
  obtain ⟨M, hM, hMblock⟩ := n06_sourceSchur_assemble
    (fun j => n07aAngularLevelBand hV γ t hI s j) blocks A hA
    (n06_sourceSchur_projection_comp hV hI)
    (n07aAngularLevelBand_symmetric hV γ t hI s) hleft hright
    (n06_sourceSchur_band_bessel hV hI) hnorm
  have hband := n06_sourceSchur_band_identification hV hI f blocks M hforget hMblock
  exact ⟨M, hM, n06_sourceSchur_identify hV hI f Q hQ M hband⟩

end ContinuousFlexibility.Analysis
