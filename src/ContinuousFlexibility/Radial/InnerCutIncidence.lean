import ContinuousFlexibility.Radial.InnerBoundedOverlap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

/-!
# The actual finite cut incidence and its Hilbert bounds

Restriction to the cuts of a piece is an operator between finite real
Euclidean spaces. Counting how many pieces contain each cut proves the
Bessel estimate used by the interface assembly, without a hypothesis on
that estimate. For a linear chain with `n` internal cuts and `n + 1`
pieces, each cut belongs to exactly its two neighboring pieces. The two
outer Dirichlet endpoints are not internal cuts.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators

section FiniteCuts

variable {α β : Type*} [DecidableEq α] [Fintype β]

/-- The number of local pieces incident to a cut. -/
def innerCutMultiplicity (I : β → Finset α) (c : α) : ℕ :=
  (Finset.univ.filter (fun b => c ∈ I b)).card

/-- Count a scalar contribution once for every incident piece. -/
theorem innerCut_sum_eq_multiplicity (J : Finset α) (I : β → Finset α)
    (hI : ∀ b, I b ⊆ J) (f : α → ℝ) :
    (∑ b, ∑ c ∈ I b, f c) =
      ∑ c ∈ J, (innerCutMultiplicity I c : ℝ) * f c := by
  classical
  have hlocal (b : β) :
      (∑ c ∈ I b, f c) = ∑ c ∈ J, if c ∈ I b then f c else 0 := by
    have hfilter : J.filter (fun c => c ∈ I b) = I b := by
      ext c
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hc => ⟨hI b hc, hc⟩⟩
    calc
      _ = ∑ c ∈ J.filter (fun c => c ∈ I b), f c :=
        congrArg (fun s : Finset α => ∑ c ∈ s, f c) hfilter.symm
      _ = _ := Finset.sum_filter (s := J) (fun c => c ∈ I b) f
  calc
    _ = ∑ b, ∑ c ∈ J, if c ∈ I b then f c else 0 :=
      Finset.sum_congr rfl (fun b _ => hlocal b)
    _ = ∑ c ∈ J, ∑ b, if c ∈ I b then f c else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [innerCutMultiplicity]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- A bound on the actual incidence count bounds every nonnegative
weighted sum, independently of the number of cuts or pieces. -/
theorem innerCut_sum_le (J : Finset α) (I : β → Finset α)
    (hI : ∀ b, I b ⊆ J) (d : ℕ)
    (hdegree : ∀ c ∈ J, innerCutMultiplicity I c ≤ d)
    (f : α → ℝ) (hf : ∀ c ∈ J, 0 ≤ f c) :
    (∑ b, ∑ c ∈ I b, f c) ≤ (d : ℝ) * ∑ c ∈ J, f c := by
  rw [innerCut_sum_eq_multiplicity J I hI f]
  calc
    _ ≤ ∑ c ∈ J, (d : ℝ) * f c := Finset.sum_le_sum (fun c hc =>
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdegree c hc)) (hf c hc))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The finite-dimensional restriction norm is precisely the sum of the
squares of its retained coordinates. -/
theorem innerCut_restriction_norm_sq_eq (J I : Finset α) (hI : I ⊆ J)
    (x : EuclideanSpace ℝ J) :
    ‖EuclideanSpace.restrict₂ hI x‖ ^ 2 =
      ∑ c ∈ I, if hc : c ∈ J then (x ⟨c, hc⟩) ^ 2 else 0 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ = ∑ c : I, if hc : (c : α) ∈ J then (x ⟨c, hc⟩) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [EuclideanSpace.restrict₂_apply, dif_pos (hI c.property)]
    _ = _ := Finset.sum_coe_sort I _

/-- The Hilbert Bessel bound follows from counting cut incidences. -/
theorem innerCut_restrictions_bessel (J : Finset α) (I : β → Finset α)
    (hI : ∀ b, I b ⊆ J) (d : ℕ)
    (hdegree : ∀ c ∈ J, innerCutMultiplicity I c ≤ d)
    (x : EuclideanSpace ℝ J) :
    (∑ b, ‖EuclideanSpace.restrict₂ (hI b) x‖ ^ 2) ≤ (d : ℝ) * ‖x‖ ^ 2 := by
  classical
  let f : α → ℝ := fun c => if hc : c ∈ J then (x ⟨c, hc⟩) ^ 2 else 0
  have hf : ∀ c ∈ J, 0 ≤ f c := by
    intro c hc
    dsimp only [f]
    rw [dif_pos hc]
    exact sq_nonneg _
  have hglobal : (∑ c ∈ J, f c) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_coe_sort J f]
    apply Finset.sum_congr rfl
    intro c _
    simp only [f, dif_pos c.property]
  calc
    _ = ∑ b, ∑ c ∈ I b, f c := Finset.sum_congr rfl (fun b _ =>
      innerCut_restriction_norm_sq_eq J (I b) (hI b) x)
    _ ≤ (d : ℝ) * ∑ c ∈ J, f c := innerCut_sum_le J I hI d hdegree f hf
    _ = _ := congrArg (fun z : ℝ => (d : ℝ) * z) hglobal

/-- Local interface errors assembled on an actual finite cut family have
an operator bound supplied by the incidence count. -/
theorem norm_innerCutBlockSum_le (J : Finset α) (I : β → Finset α)
    (hI : ∀ b, I b ⊆ J) (d : ℕ)
    (hdegree : ∀ c ∈ J, innerCutMultiplicity I c ≤ d)
    (K : ∀ b, EuclideanSpace ℝ (I b) →L[ℝ] EuclideanSpace ℝ (I b))
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ b, ‖K b‖ ≤ η) :
    ‖innerInterfaceBlockSum (fun b => EuclideanSpace.restrict₂ (hI b)) K‖ ≤
      (d : ℝ) * η :=
  norm_innerInterfaceBlockSum_le _ K (Nat.cast_nonneg d) hη
    (innerCut_restrictions_bessel J I hI d hdegree) hK

/-- The same incidence bound survives the contractive reference-interface
normalization used in the inner inverse. -/
theorem norm_innerCutBlockSum_normalized_le (J : Finset α) (I : β → Finset α)
    (hI : ∀ b, I b ⊆ J) (d : ℕ)
    (hdegree : ∀ c ∈ J, innerCutMultiplicity I c ≤ d)
    (K : ∀ b, EuclideanSpace ℝ (I b) →L[ℝ] EuclideanSpace ℝ (I b))
    (A : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ b, ‖K b‖ ≤ η) (hA : ‖A‖ ≤ 1) :
    ‖A.comp ((innerInterfaceBlockSum
      (fun b => EuclideanSpace.restrict₂ (hI b)) K).comp A.adjoint)‖ ≤ (d : ℝ) * η :=
  norm_innerInterfaceBlockSum_normalized_le _ K A (Nat.cast_nonneg d) hη
    (innerCut_restrictions_bessel J I hI d hdegree) hK hA

end FiniteCuts

section LinearChain

/-- Piece `p` meets the internal cut immediately before it and the one
immediately after it, when those cuts exist. Models and gaps are the
alternating pieces of this same linear chain. -/
def innerChainPieceCuts (n : ℕ) (p : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val = p.val ∨ i.val + 1 = p.val)

/-- A model or gap has at most two internal endpoints, including the
pieces adjacent to the two outer Dirichlet boundaries. -/
theorem innerChainPieceCuts_card_le_two (n : ℕ) (p : Fin (n + 1)) :
    (innerChainPieceCuts n p).card ≤ 2 := by
  classical
  have hsub : (innerChainPieceCuts n p).image (fun i => i.val) ⊆
      ({p.val, p.val - 1} : Finset ℕ) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hi' : i.val = p.val ∨ i.val + 1 = p.val :=
      (Finset.mem_filter.mp hi).2
    apply Finset.mem_insert.mpr
    rcases hi' with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mpr (by omega))
  calc
    _ = ((innerChainPieceCuts n p).image (fun i => i.val)).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ ({p.val, p.val - 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- Every internal cut is incident exactly to the piece on each side.
There are no other incidences, regardless of the length of the chain. -/
theorem innerChainCut_incidentPieces (n : ℕ) (i : Fin n) :
    Finset.univ.filter (fun p : Fin (n + 1) => i ∈ innerChainPieceCuts n p) =
      {i.castSucc, i.succ} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, innerChainPieceCuts,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

/-- The two incident pieces are distinct, so every internal cut has
multiplicity exactly two. -/
theorem innerChainCut_multiplicity (n : ℕ) (i : Fin n) :
    innerCutMultiplicity (innerChainPieceCuts n) i = 2 := by
  unfold innerCutMultiplicity
  rw [innerChainCut_incidentPieces]
  exact Finset.card_pair (ne_of_lt i.castSucc_lt_succ)

/-- Actual restriction from all internal cut values to one piece. -/
def innerChainRestriction (n : ℕ) (p : Fin (n + 1)) :
    EuclideanSpace ℝ (Finset.univ : Finset (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (innerChainPieceCuts n p) :=
  EuclideanSpace.restrict₂ (Finset.subset_univ _)

/-- The concrete chain restrictions have Bessel constant two, proved
from their cut incidences rather than supplied as an analytic premise. -/
theorem innerChain_restrictions_bessel (n : ℕ)
    (x : EuclideanSpace ℝ (Finset.univ : Finset (Fin n))) :
    (∑ p, ‖innerChainRestriction n p x‖ ^ 2) ≤ 2 * ‖x‖ ^ 2 := by
  simpa only [innerChainRestriction, Nat.cast_ofNat] using
    innerCut_restrictions_bessel (Finset.univ : Finset (Fin n))
      (innerChainPieceCuts n) (fun _ => Finset.subset_univ _) 2
      (fun i _ => (innerChainCut_multiplicity n i).le) x

/-- Assembly of the actual chain blocks loses only the factor two. -/
theorem norm_innerChainBlockSum_le (n : ℕ)
    (K : ∀ p : Fin (n + 1), EuclideanSpace ℝ (innerChainPieceCuts n p) →L[ℝ]
      EuclideanSpace ℝ (innerChainPieceCuts n p))
    {η : ℝ} (hη : 0 ≤ η) (hK : ∀ p, ‖K p‖ ≤ η) :
    ‖innerInterfaceBlockSum (innerChainRestriction n) K‖ ≤ 2 * η :=
  norm_innerInterfaceBlockSum_le _ K (by norm_num) hη
    (innerChain_restrictions_bessel n) hK

/-- Contractive normalization converts local errors below one quarter
into the strict one-half interface bound, uniformly in the cut count. -/
theorem norm_innerChainBlockSum_normalized_lt_half (n : ℕ)
    (K : ∀ p : Fin (n + 1), EuclideanSpace ℝ (innerChainPieceCuts n p) →L[ℝ]
      EuclideanSpace ℝ (innerChainPieceCuts n p))
    (A : EuclideanSpace ℝ (Finset.univ : Finset (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Finset.univ : Finset (Fin n)))
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (hK : ∀ p, ‖K p‖ ≤ η) (hA : ‖A‖ ≤ 1) :
    ‖A.comp ((innerInterfaceBlockSum (innerChainRestriction n) K).comp A.adjoint)‖ <
      1 / 2 := by
  have h := norm_innerInterfaceBlockSum_normalized_le
    (innerChainRestriction n) K A (by norm_num : (0 : ℝ) ≤ 2) hη
    (innerChain_restrictions_bessel n) hK hA
  exact h.trans_lt (by linarith)

end LinearChain

end ContinuousFlexibility.Radial
