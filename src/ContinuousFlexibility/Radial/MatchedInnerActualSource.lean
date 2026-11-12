import ContinuousFlexibility.Radial.MatchedInnerActualInverse
import Mathlib.Data.Finset.Max

/-!
# The actual matching source belongs to the finite-chain source space

The union of the open physical pieces differs from the full inner
interval only at finitely many cuts. Those cuts have zero physical
measure. Consequently the original matching source restriction, with its
one admissible scalar, is an element of the existing finite-chain Hilbert
space. This gives the same-C inverse formula for the actual sourceInner
input that occurs in the global matching formula.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped ContDiff Matrix.Norms.L2Operator
open ContinuousFlexibility.Statements

theorem matchedInnerChainRegion_of_mem_not_cut {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) {r : ℝ}
    (hr : r ∈ Ioo (G.left 0) (G.right (Fin.last n)))
    (hcut : ∀ i, r ≠ G.cuts i) :
    r ∈ innerRadialChainRegion D G := by
  classical
  change G.cuts 0 < r ∧ r < G.cuts (Fin.last (n + 1)) at hr
  let s : Finset (Fin (n + 2)) := Finset.univ.filter (fun i => G.cuts i < r)
  have hs : s.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1⟩⟩
  let i : Fin (n + 2) := s.max' hs
  have hi : G.cuts i < r := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hilast : i ≠ Fin.last (n + 1) := by
    intro he
    rw [he] at hi
    exact lt_asymm hi hr.2
  have hiv : i.val < n + 1 := by
    by_contra hn
    have he : i = Fin.last (n + 1) := Fin.ext (by
      have hlt := i.isLt
      simp only [Fin.val_last]
      omega)
    exact hilast he
  let p : Fin (n + 1) := ⟨i.val, hiv⟩
  have hpi : p.castSucc = i := Fin.ext rfl
  have hnext : r < G.cuts p.succ := by
    by_contra hn
    have hnlt : G.cuts p.succ < r :=
      lt_of_le_of_ne (le_of_not_gt hn) (hcut p.succ).symm
    have hm : p.succ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnlt⟩
    have hle : p.succ ≤ i := s.le_max' _ hm
    have hle' : p.val + 1 ≤ i.val := hle
    change i.val + 1 ≤ i.val at hle'
    omega
  apply Set.mem_iUnion.mpr
  refine ⟨p, ?_, hnext⟩
  change G.cuts p.castSucc < r
  rw [hpi]
  exact hi

theorem matchedInnerChainRegion_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {n : ℕ} (G : InnerRadialChainGeometry D n) :
    ∀ᵐ r ∂radialHilbertMeasure D,
      r ∈ innerRadialChainRegion D G ↔ r ∈ Ioo (G.left 0) (G.right (Fin.last n)) := by
  have hc : ∀ᵐ r ∂radialHilbertMeasure D, ∀ i, r ≠ G.cuts i :=
    ae_all_iff.mpr (fun i => matching_ae_ne hD (G.cuts i))
  filter_upwards [hc] with r hr
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
    exact matchedInnerChain_piece_Ioo_subset G p hp
  · intro h
    exact matchedInnerChainRegion_of_mem_not_cut G h hr

/-- Membership of the original matching source in the existing actual
finite-chain source space; no new source projection is introduced. -/
theorem matchedInner_sourceInner_mem {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (hleft : M.innerLeft = G.left 0) (hright : M.innerRight = G.right (Fin.last n))
    (F : RadialModePair D) (hF : M.frequency ≠ 2 → F.2 = 0) :
    WithLp.toLp 2 (M.sourceInner F) ∈
      innerSupportedAdmissibleSource (radialHilbertMeasure D)
        (innerRadialChainRegion D G) (decide (M.frequency = 2)) := by
  classical
  apply (mem_innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) (decide (M.frequency = 2)) _).mpr
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  constructor
  · by_cases hj : M.frequency = 2
    · exact Or.inl (by simp [hj])
    · right
      rw [(hM.2.2.2.1 F).1]
      exact hF hj
  · apply innerL2PieceProjection_eq_self _ _ (innerRadialChainRegion_measurable D G)
    filter_upwards [(hM.2.2.2.1 F).2.2.1, matchedInnerChainRegion_ae hD G]
      with r hsrc hregion
    intro hout
    have hin : r ∉ Ioo M.innerLeft M.innerRight := by
      intro hr
      apply hout
      apply hregion.mpr
      simpa only [hleft, hright] using hr
    rw [hsrc, if_neg hin]

/-- The actual matching source can be passed directly to the same finite
Schur inverse. Its ambient Dirichlet and Poisson fields are unchanged. -/
theorem matchedInnerActualInverse_sourceInner_ambient {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (hw : ContDiff ℝ ∞ D.w) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (M : RadialMatchingData D) (hM : MatchingLocalRealizations D M)
    (hleft : M.innerLeft = G.left 0) (hright : M.innerRight = G.right (Fin.last n))
    (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
    (central : Fin (n + 1)) (column : RadialModeL2 D)
    (hcolumn : column = matchingBorderVector D hD hB)
    (hcolfix : innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left central) (G.right central)) column = column)
    (C : InnerRadialActualChain D G (decide (M.frequency = 2))
      (M.frequency : ℝ) central column)
    (hS : IsUnit C.fluxMatrix)
    (F : RadialModePair D) (hF : M.frequency ≠ 2 → F.2 = 0) :
    WithLp.toLp 2 (M.innerInverse (M.sourceInner F)) =
      C.ambientDirichlet hw (WithLp.toLp 2 (M.sourceInner F)) + C.ambientPoisson hw
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹
          ((C.ambientPoisson hw).adjoint (WithLp.toLp 2 (M.sourceInner F)))) := by
  let Fphys : InnerRadialPhysicalSource D G (decide (M.frequency = 2)) :=
    ⟨WithLp.toLp 2 (M.sourceInner F),
      matchedInner_sourceInner_mem hD G M hM hleft hright F hF⟩
  exact matchedInnerActualInverse_ambient hD hB hw G M hleft hright hsub
    central column hcolumn hcolfix C hS hM Fphys

end ContinuousFlexibility.Radial
