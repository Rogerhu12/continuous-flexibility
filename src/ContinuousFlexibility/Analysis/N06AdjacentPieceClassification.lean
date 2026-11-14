module

public import ContinuousFlexibility.Analysis.N06NegativePieceFiniteness
public import ContinuousFlexibility.Analysis.N06FiniteAtlasBoundary
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Every adjacent negative reference pair is the prescribed cut pair

At a common endpoint of two negative pieces the reference slope cannot
vanish: it would have a local maximum there, contradicting the original
simple-root condition. The endpoint therefore belongs to one actual
negative component. The two prescribed half-pieces fill that component,
and disjointness forces the endpoint to be its prescribed cut.

Thus the ordinary root and affine-cut matching theorems exhaust all
adjacent reference indices, with no new classification premise. Current
physical domains are not asserted to be these radial intervals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- Disjoint nonempty reference intervals cannot contain another piece's
right endpoint in their own open interval. -/
theorem n06_physicalRight_not_mem_piece
    (h04 : N04Properties D T S C L K base loss ε) (m n : ℕ) :
    K.physicalRight m ∉ Ioo (K.physicalLeft n) (K.physicalRight n) := by
  intro hr
  obtain ⟨x, hxl, hxr⟩ := exists_between
    (max_lt (h04.1.referenceBounds m).1 hr.1)
  have hxm : x ∈ Ioo (K.physicalLeft m) (K.physicalRight m) :=
    ⟨(le_max_left _ _).trans_lt hxl, hxr⟩
  have hxn : x ∈ Ioo (K.physicalLeft n) (K.physicalRight n) :=
    ⟨(le_max_right _ _).trans_lt hxl, hxr.trans hr.2⟩
  have he : m = n := n06_physicalPiece_eq_of_commonPoint h04 hxm hxn
  have hbad : K.physicalRight m < K.physicalRight m := by
    simpa only [← he] using hr.2
  exact lt_irrefl _ hbad

/-- Any interface between two nonempty reference intervals lies in the open
annulus, even though a single outer piece may have an exterior endpoint. -/
theorem n06_adjacentInterface_mem_core
    (h04 : N04Properties D T S C L K base loss ε)
    {ml mr : ℕ} (hjoin : K.physicalRight ml = K.physicalLeft mr) :
    K.physicalRight ml ∈ radialCore D := by
  obtain ⟨x, hxl, hxr⟩ := exists_between (h04.1.referenceBounds ml).1
  obtain ⟨y, hyl, hyr⟩ := exists_between (h04.1.referenceBounds mr).1
  have hx := (h04.1.referenceBounds ml).2.2 ⟨hxl, hxr⟩
  have hy := (h04.1.referenceBounds mr).2.2 ⟨hyl, hyr⟩
  refine ⟨hx.1.trans hxr, ?_⟩
  rw [hjoin]
  exact hyl.trans hy.2

/-- Two adjacent negative reference intervals have strictly negative slope
at the common endpoint. A zero would violate the original simple-root
condition by Fermat's theorem. -/
theorem n06_adjacent_negative_slope_lt
    (hD : RadialProfileGeometry D)
    (h04 : N04Properties D T S C L K base loss ε)
    {ml mr : ℕ} (hml : K.positive ml = false) (hmr : K.positive mr = false)
    (hjoin : K.physicalRight ml = K.physicalLeft mr) :
    deriv D.w (K.physicalRight ml) < 0 := by
  have hnegative : ∀ m, K.positive m = false →
      ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), deriv D.w r < 0 :=
    h04.1.referenceNegative
  have hw : ContDiff ℝ 2 D.w := hD.2.2.1.1.of_le (by simp)
  have hdw : ContDiff ℝ 1 (deriv D.w) := hw.deriv'
  have hc : Continuous (deriv D.w) := hdw.continuous
  have hclosure : K.physicalRight ml ∈
      closure (Ioo (K.physicalLeft ml) (K.physicalRight ml)) := by
    rw [closure_Ioo (h04.1.referenceBounds ml).1.ne]
    exact ⟨(h04.1.referenceBounds ml).1.le, le_rfl⟩
  have hle : deriv D.w (K.physicalRight ml) ≤ 0 :=
    le_on_closure (fun r hr => (hnegative ml hml r hr).le)
      hc.continuousOn continuousOn_const hclosure
  rcases lt_or_eq_of_le hle with hlt | hzero
  · exact hlt
  · have hmax : IsLocalMax (deriv D.w) (K.physicalRight ml) := by
      change ∀ᶠ x in 𝓝 (K.physicalRight ml), deriv D.w x ≤ deriv D.w (K.physicalRight ml)
      have hmem : K.physicalRight ml ∈
          Ioo (K.physicalLeft ml) (K.physicalRight mr) := by
        refine ⟨(h04.1.referenceBounds ml).1, ?_⟩
        rw [hjoin]
        exact (h04.1.referenceBounds mr).1
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with x hx
      rw [hzero]
      rcases lt_trichotomy x (K.physicalRight ml) with hxl | hxe | hxr
      · exact (hnegative ml hml x ⟨hx.1, hxl⟩).le
      · rw [hxe, hzero]
      · exact (hnegative mr hmr x ⟨by rw [← hjoin]; exact hxr, hx.2⟩).le
    exact False.elim ((hD.2.2.2.2.2.2 (K.physicalRight ml)
      (n06_adjacentInterface_mem_core h04 hjoin) hzero) hmax.deriv_eq_zero)

/-- The reference index order has no unlisted negative/negative interface.
Every such pair is exactly the ordered pair in `K.cutPair`. -/
theorem n06_adjacent_negative_eq_cutPair
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {ml mr : ℕ} (hml : K.positive ml = false) (hmr : K.positive mr = false)
    (hjoin : K.physicalRight ml = K.physicalLeft mr) :
    ∃ n, ml = (K.cutPair n).1 ∧ mr = (K.cutPair n).2 := by
  have hD : RadialProfileGeometry D := h01.1.1.choose_spec.1
  have hC : controlGeometryConditions D S C := h01.2.2.2.1
  have hneg := n06_adjacent_negative_slope_lt hD h04 hml hmr hjoin
  obtain ⟨n, hn⟩ := hC.2.2.2.2.1 (K.physicalRight ml)
    (n06_adjacentInterface_mem_core h04 hjoin) hneg
  have hpieces := h04.1.referenceBounds
  have hcut := h04.2.1.1.1
  obtain ⟨_, _, hleft, hright, hcutjoin, _⟩ := hcut n
  have hmid : K.physicalRight ml = K.physicalRight (K.cutPair n).1 := by
    rcases lt_trichotomy (K.physicalRight ml) (K.physicalRight (K.cutPair n).1) with
      hbefore | heq | hafter
    · exact False.elim (n06_physicalRight_not_mem_piece h04 ml (K.cutPair n).1
        ⟨by rw [hleft]; exact hn.1, hbefore⟩)
    · exact heq
    · exact False.elim (n06_physicalRight_not_mem_piece h04 ml (K.cutPair n).2
        ⟨by rw [← hcutjoin]; exact hafter, by rw [hright]; exact hn.2⟩)
  have heL : ml = (K.cutPair n).1 := Analysis.n06_disjoint_intervals_right_injective
    (fun i => (hpieces i).1) (n06_physicalPiece_pairwiseDisjoint h04) hmid
  have heR : mr = (K.cutPair n).2 := n06_disjoint_intervals_left_injective
    (fun i => (hpieces i).1) (n06_physicalPiece_pairwiseDisjoint h04)
      (hjoin.symm.trans (hmid.trans hcutjoin))
  exact ⟨n, heL, heR⟩

/-- The two already proved transmission mechanisms exhaust every
neighbor in the reference atlas index order. -/
theorem n06_adjacentPiece_positive_or_cutPair
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {ml mr : ℕ} (hjoin : K.physicalRight ml = K.physicalLeft mr) :
    (K.positive ml = true ∨ K.positive mr = true) ∨
      ∃ n, ml = (K.cutPair n).1 ∧ mr = (K.cutPair n).2 := by
  by_cases hml : K.positive ml = true
  · exact Or.inl (Or.inl hml)
  by_cases hmr : K.positive mr = true
  · exact Or.inl (Or.inr hmr)
  exact Or.inr (n06_adjacent_negative_eq_cutPair h01 h04
    (Bool.eq_false_of_not_eq_true hml) (Bool.eq_false_of_not_eq_true hmr) hjoin)

end ContinuousFlexibility.Statements
