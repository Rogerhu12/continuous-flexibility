module

public import ContinuousFlexibility.Analysis.N07aWeightedSchurRealization

/-!
# The same bounded commutator in every actual weighted graph

The order-zero blocks construct one bounded commutator. Its exact block
identity identifies every higher weighted Schur realization with this
same operator. The maximal angular domain identity is then the proved
coordinate identity for this operator, rather than an extra hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ENNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aWeightedCommLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aWeightedCommLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aWeightedCommLevelInner (γ t : ℝ) (s : ℕ) :
    InnerProductSpace ℝ (V.level γ t s) := Submodule.innerProductSpace _
local instance n07aWeightedCommBandGroup (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b n : ℕ) :
    NormedAddCommGroup (n07aAngularBandSpace hV γ 0 hI b n) := Submodule.normedAddCommGroup _
local instance n07aWeightedCommBandSpace (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b n : ℕ) :
    NormedSpace ℝ (n07aAngularBandSpace hV γ 0 hI b n) := Submodule.normedSpace _

private theorem n07aWeightedComm_base_bound
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ)
    (R : V.level γ 0 b →L[ℝ] V.level γ 0 b) (a c : ℝ)
    (hblocks : ∀ (x : V.level γ 0 b) (j l : ℕ),
      ∃ W : V.level γ 0 b,
        V.forget γ 0 b W = V.forget γ 0 b
          (((l : ℝ) - j) • n07aAngularLevelBand hV γ 0 hI b l
            (R (n07aAngularLevelBand hV γ 0 hI b j
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b 0) x)))) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (a * ‖n07aAngularLevelBand hV γ 0 hI b j x‖ +
            c * ‖n07aAngularLevelBand hV γ 0 hI b j
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b 0) x)‖))
    (l j : ℕ) (x : V.level γ 0 b) :
    ‖n07aCommutatorBlock (n07aAngularLevelBand hV γ 0 hI b) R l j x‖ ≤
      (n07aAngularTail ((j : ℤ) - l) * (a + c)) *
        ‖n07aAngularLevelBand hV γ 0 hI b j x‖ := by
  let : CompleteSpace (V.level γ 0 b) := n07aAngularLevelComplete hV γ 0 b
  let PB : ℕ → V.level γ 0 b →L[ℝ] V.level γ 0 b :=
    n07aAngularLevelBand hV γ 0 hI b
  let result := hblocks x j l
  let W : V.level γ 0 b := result.choose
  have htr : n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b 0) x = x :=
    n07aAngularLevelTruncate_refl hV γ 0 b x
  have hW : V.forget γ 0 b W = V.forget γ 0 b
      (((l : ℝ) - j) • PB l (R (PB j x))) := by
    simpa only [htr] using result.choose_spec.1
  have he : W = n07aCommutatorBlock PB R l j x :=
    hV.2.2.1 γ 0 b (hW.trans (congrArg (V.forget γ 0 b)
      (n07aCommutatorBlock_apply PB R l j x).symm))
  have hn : ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
      (a * ‖PB j x‖ + c * ‖PB j x‖) := by
    simpa only [htr] using result.choose_spec.2
  exact (congrArg norm he.symm).le.trans (hn.trans_eq (by ring))

private theorem exists_n07aWeightedComm_base
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ)
    (R : V.level γ 0 b →L[ℝ] V.level γ 0 b) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ (l j : ℕ) (x : V.level γ 0 b),
      ‖n07aCommutatorBlock (n07aAngularLevelBand hV γ 0 hI b) R l j x‖ ≤
        (n07aAngularTail ((j : ℤ) - l) * c) *
          ‖n07aAngularLevelBand hV γ 0 hI b j x‖) :
    ∃ Q : V.level γ 0 b →L[ℝ] V.level γ 0 b,
      ∀ (l j : ℕ) (x : V.level γ 0 b),
        n07aAngularLevelBand hV γ 0 hI b l
          (Q (n07aAngularLevelBand hV γ 0 hI b j x)) =
        ((l : ℝ) - j) • n07aAngularLevelBand hV γ 0 hI b l
          (R (n07aAngularLevelBand hV γ 0 hI b j x)) := by
  let : CompleteSpace (V.level γ 0 b) := n07aAngularLevelComplete hV γ 0 b
  let PB : ℕ → V.level γ 0 b →L[ℝ] V.level γ 0 b :=
    n07aAngularLevelBand hV γ 0 hI b
  let τ : ℝ := ∑' k : ℤ, n07aAngularTail k
  have hτ : 0 ≤ τ := tsum_nonneg n07aAngularTail_nonneg
  have hkernel := n07aAngularTail_schur c hc
  let result := exists_n07aSchurCommutator PB R
    (fun (l j : ℕ) => n07aAngularTail ((j : ℤ) - l) * c)
    (mul_nonneg hτ hc) (mul_nonneg hτ hc)
    hkernel.1 hkernel.2.1 hkernel.2.2
    (n07aAngularLevelBand_square_budget hV γ 0 hI b) hb
  let Q : V.level γ 0 b →L[ℝ] V.level γ 0 b := result.choose
  have hpair := result.choose_spec.2
  have hcomp (i j : ℕ) (x : V.level γ 0 b) :
      PB i (PB j x) = if i = j then PB j x else 0 := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact n07aAngularLevelBand_idempotent hV γ 0 hI b i x
    · rw [ite_eq_right hij]
      exact n07aAngularLevelBand_comp_eq_zero hV γ 0 hI b hij x
  refine ⟨Q, fun l j x => ?_⟩
  exact (n07aSchurCommutator_block PB R Q hcomp
    (n07aAngularLevelBand_symmetric hV γ 0 hI b) hpair l j x).trans
      (n07aCommutatorBlock_apply PB R l j x)

theorem exists_n07aWeightedCommutatorOperators
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ)
    (R : V.level γ 0 b →L[ℝ] V.level γ 0 b)
    (a c : ℝ → ℕ → ℝ) (ha : ∀ t p, 0 ≤ a t p) (hc : ∀ t p, 0 ≤ c t p)
    (hblocks : ∀ (t : ℝ) (p : ℕ) (U : V.level γ 0 (b + p)) (j l : ℕ) (commute : Bool),
      ∃ W : V.level γ t (b + p),
        V.forget γ t (b + p) W = V.forget γ 0 b
          ((if commute then ((l : ℝ) - j) else 1) •
            n07aAngularLevelBand hV γ 0 hI b l
              (R (n07aAngularLevelBand hV γ 0 hI b j
                (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)))) ∧
        ‖W‖ ≤ n07aAngularTail ((j : ℤ) - l) *
          (a t p * ‖n07aAngularLevelBand hV γ 0 hI (b + p) j U‖ +
            c t p * ‖n07aAngularLevelBand hV γ 0 hI b j
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)‖)) :
    ∃ Q : V.level γ 0 b →L[ℝ] V.level γ 0 b,
      (∀ u, n07aAngularHilbertEquiv hV γ 0 hI b u ∈ angularFrequencyDomain (𝕜 := ℝ) →
        n07aAngularLambda hV γ 0 hI b (R u) =
          R (n07aAngularLambda hV γ 0 hI b u) + Q u) ∧
      ∀ t, 0 ≤ t → ∀ p (commute : Bool),
        ∃ A : V.level γ 0 (b + p) →L[ℝ] V.level γ t (b + p), ∀ U,
          V.forget γ t (b + p) (A U) = V.forget γ 0 b
            ((if commute then Q else R)
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U)) ∧
          ‖A U‖ ≤ (∑' k : ℤ, n07aAngularTail k) *
            (a t p * ‖U‖ + c t p *
              ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) U‖) := by
  have hb := n07aWeightedComm_base_bound hV γ hI b R (a 0 0) (c 0 0)
    (fun x j l => hblocks 0 0 x j l true)
  let result := exists_n07aWeightedComm_base hV γ hI b R
    (add_nonneg (ha 0 0) (hc 0 0)) hb
  let Q : V.level γ 0 b →L[ℝ] V.level γ 0 b := result.choose
  have hQ := result.choose_spec
  refine ⟨Q, fun u hu =>
    (n07aAngularCommutator_domain hV γ 0 hI b R Q hQ u hu).2, ?_⟩
  intro t ht p commute
  apply exists_n07aWeightedSchurOperator hD hT hV γ ht hI b p R
    (if commute then Q else R) (fun (l j : ℕ) => if commute then ((l : ℝ) - j) else 1)
    (fun l j x => by
      cases commute
      · simp only [Bool.false_eq_true, ite_false, one_smul]
      · exact hQ l j x)
    (ha t p) (hc t p)
  intro U l j
  exact hblocks t p U j l commute

end ContinuousFlexibility.Analysis
