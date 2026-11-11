import ContinuousFlexibility.Analysis.N07aAngularPieceInterfaces
import ContinuousFlexibility.Analysis.N07aAngularFirstJetGluing
import Mathlib.Order.Interval.Set.Disjoint

/-!
# One C¹ physical field from the actual closed canonical pieces

The a.e. cover and raw geometry already give an everywhere closed cover.
Matching genuine boundary germs make the value independent of the chosen
closed piece. Differentiability is local on the two adjacent sides, and
continuity of the actual first derivative follows from its uniqueness on
each closed half-strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

theorem n07a_disjoint_intervals_order {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (h : Disjoint (Ioo a b) (Ioo c d)) :
    b ≤ c ∨ d ≤ a := by
  have hd := Ioo_disjoint_Ioo.mp h
  rcases le_max_iff.mp hd with hleft | hright
  · rcases min_le_iff.mp hleft with hba | hda
    · exact (not_le_of_gt hab hba).elim
    · exact Or.inr hda
  · rcases min_le_iff.mp hright with hbc | hdc
    · exact Or.inl hbc
    · exact (not_le_of_gt hcd hdc).elim

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_physicalClosedPieces_overlap
    (h04 : N04Properties D T S C L K base loss ε) {i j : ℕ} (hij : i ≠ j)
    {r : ℝ} (hi : r ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hj : r ∈ Icc (K.physicalLeft j) (K.physicalRight j)) :
    (K.physicalRight i = r ∧ K.physicalLeft j = r) ∨
      (K.physicalRight j = r ∧ K.physicalLeft i = r) := by
  rcases n07a_disjoint_intervals_order (h04.2.2.2.1 i).1 (h04.2.2.2.1 j).1
    (n07a_physicalPieces_pairwise_disjoint h04 hij) with h | h
  · exact Or.inl ⟨le_antisymm (h.trans hj.1) hi.2,
      le_antisymm hj.1 (hi.2.trans h)⟩
  · exact Or.inr ⟨le_antisymm (h.trans hi.1) hj.2,
      le_antisymm hi.1 (hj.2.trans h)⟩

theorem n07a_glue_closed_physical_pieces
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K)
    (W : ℕ → PolarPoint → ℝ)
    (hW : ∀ m, ContDiffOn ℝ ∞ (W m) (physicalPieceOpen S K m))
    (hboundary : ∀ i j : ℕ, i ≠ j → K.physicalRight i = K.physicalLeft j →
      K.physicalRight i ∈ Ioo D.a D.b → ∀ θ : ℝ,
      let p : PolarPoint := (K.physicalRight i, θ)
      ∃ u v : PolarPoint → ℝ,
        ContDiffAt ℝ ∞ u p ∧ ContDiffAt ℝ ∞ v p ∧
        u p = v p ∧ fderiv ℝ u p = fderiv ℝ v p ∧
        (∀ᶠ x in 𝓝 p, x.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) → W i x = u x) ∧
        (∀ᶠ x in 𝓝 p, x.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j) → W j x = v x)) :
    ∃ f : PolarPoint → ℝ,
      ContDiffOn ℝ 1 f (annularOpen D) ∧
      (∀ m p, p ∈ annularOpen D →
        p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) → f p = W m p) ∧
      (∀ p, p ∉ annularOpen D → f p = 0) ∧
      ∀ p ∈ annularOpen D, ∃ u : PolarPoint → ℝ,
        ContDiffAt ℝ ∞ u p ∧
        ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → f q = u q := by
  classical
  have hcross (i j : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D)
      (hi : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i))
      (hj : p.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j)) : W i p = W j p := by
    by_cases hij : i = j
    · subst j; rfl
    have hadj (i j : ℕ) (hne : i ≠ j) (hi : K.physicalRight i = p.1)
        (hj : K.physicalLeft j = p.1) : W i p = W j p := by
      have hcore : K.physicalRight i ∈ Ioo D.a D.b := hi.symm ▸ hp.1
      obtain ⟨u, v, _, _, huv, _, hui, hvj⟩ := hboundary i j hne (hi.trans hj.symm) hcore p.2
      have hpi : p.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) := by
        rw [← hi]
        exact ⟨(h04.2.2.2.1 i).1.le, le_rfl⟩
      have hpj : p.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j) := by
        rw [← hj]
        exact ⟨le_rfl, (h04.2.2.2.1 j).1.le⟩
      have he := (hui.self_of_nhds (show (K.physicalRight i, p.2).1 ∈
          Icc (K.physicalLeft i) (K.physicalRight i) by simpa only [hi] using hpi)).trans
        (huv.trans (hvj.self_of_nhds (by simpa only [hi] using hpj)).symm)
      simpa only [hi, Prod.eta] using he
    rcases n07a_physicalClosedPieces_overlap h04 hij hi hj with h | h
    · exact hadj i j hij h.1 h.2
    · exact (hadj j i (fun hji => hij hji.symm) h.1 h.2).symm
  have hcover (r : ℝ) (hr : r ∈ Ioo D.a D.b) :=
    n07a_physicalClosedPieces_cover hD hT h04 href hr
  let index (r : ℝ) : ℕ := if hr : r ∈ Ioo D.a D.b then (hcover r hr).choose else 0
  have hindex (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      r ∈ Icc (K.physicalLeft (index r)) (K.physicalRight (index r)) := by
    simp only [index, dite_eq_left hr]
    exact (hcover r hr).choose_spec
  let f : PolarPoint → ℝ := fun p => if p.1 ∈ Ioo D.a D.b then W (index p.1) p else 0
  have heq (m : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D)
      (hm : p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m)) : f p = W m p := by
    exact (ite_eq_left hp.1).trans (hcross (index p.1) m p hp (hindex p.1 hp.1) hm)
  have hlocal (p : PolarPoint) (hp : p ∈ annularOpen D) :
      ContDiffAt ℝ ∞ f p ∨ ∃ u v : PolarPoint → ℝ,
        ContDiffAt ℝ ∞ u p ∧ ContDiffAt ℝ ∞ v p ∧ fderiv ℝ u p = fderiv ℝ v p ∧
        (∀ᶠ q in 𝓝 p, q.1 ≤ p.1 → f q = u q) ∧
        (∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → f q = v q) := by
    by_cases hinterior : ∃ m, p ∈ physicalPieceOpen S K m
    · obtain ⟨m, hm⟩ := hinterior
      apply Or.inl
      apply ((hW m).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hm)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hm] with q hq
      exact heq m q ⟨(h04.2.2.2.1 m).2.2 hq.1, mem_univ _⟩ (Ioo_subset_Icc_self hq.1)
    · have hnot (m : ℕ) : p.1 ∉ Ioo (K.physicalLeft m) (K.physicalRight m) :=
        fun hm => hinterior ⟨m, hm, mem_univ _⟩
      obtain ⟨i, j, hij, hi, hj⟩ := n07a_physicalPieces_adjacent_at_boundary hD hT h04 href hp.1 hnot
      have hcore : K.physicalRight i ∈ Ioo D.a D.b := hi.symm ▸ hp.1
      obtain ⟨u, v, hu, hv, _, hd, hui, hvj⟩ := hboundary i j hij (hi.trans hj.symm) hcore p.2
      have hu' : ContDiffAt ℝ ∞ u p := by simpa only [hi, Prod.eta] using hu
      have hv' : ContDiffAt ℝ ∞ v p := by simpa only [hi, Prod.eta] using hv
      have hd' : fderiv ℝ u p = fderiv ℝ v p := by simpa only [hi, Prod.eta] using hd
      have hui' : ∀ᶠ q in 𝓝 p,
          q.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) → W i q = u q := by
        simpa only [hi, Prod.eta] using hui
      have hvj' : ∀ᶠ q in 𝓝 p,
          q.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j) → W j q = v q := by
        simpa only [hi, Prod.eta] using hvj
      refine Or.inr ⟨u, v, hu', hv', hd', ?_, ?_⟩
      · have hleft : K.physicalLeft i < p.1 := by simpa only [hi] using (h04.2.2.2.1 i).1
        filter_upwards [hui', (isOpen_Ioo.prod isOpen_univ).mem_nhds hp,
          (isOpen_lt continuous_const continuous_fst).mem_nhds hleft] with q hq hqD hql hqc
        have hqm : q.1 ∈ Icc (K.physicalLeft i) (K.physicalRight i) :=
          ⟨hql.le, by simpa only [hi] using hqc⟩
        exact (heq i q hqD hqm).trans (hq hqm)
      · have hright : p.1 < K.physicalRight j := by simpa only [hj] using (h04.2.2.2.1 j).1
        filter_upwards [hvj', (isOpen_Ioo.prod isOpen_univ).mem_nhds hp,
          (isOpen_lt continuous_fst continuous_const).mem_nhds hright] with q hq hqD hqr hqc
        have hqm : q.1 ∈ Icc (K.physicalLeft j) (K.physicalRight j) :=
          ⟨by simpa only [hj] using hqc, hqr.le⟩
        exact (heq j q hqD hqm).trans (hq hqm)
  have hdiff (p : PolarPoint) (hp : p ∈ annularOpen D) : DifferentiableAt ℝ f p := by
    rcases hlocal p hp with h | ⟨u, v, hu, hv, hd, hl, hr⟩
    · exact h.differentiableAt (by simp)
    · exact (n07a_two_closed_branches_hasFDerivAt rfl
        (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp)) hd hl hr).differentiableAt
  have hright (p : PolarPoint) (hp : p ∈ annularOpen D) :
      ∃ u : PolarPoint → ℝ, ContDiffAt ℝ ∞ u p ∧
        ∀ᶠ q in 𝓝 p, p.1 ≤ q.1 → f q = u q := by
    rcases hlocal p hp with h | ⟨u, v, hu, hv, hd, hl, hr⟩
    · exact ⟨f, h, Filter.Eventually.of_forall fun _ _ => rfl⟩
    · exact ⟨v, hv, hr⟩
  refine ⟨f, ?_, heq, (fun p hp => ite_eq_right (fun h => hp ⟨h, mem_univ _⟩)), hright⟩
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hdc : ContinuousOn (fderiv ℝ f) (annularOpen D) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    rcases hlocal p hp with h | ⟨u, v, hu, hv, _, hl, hr⟩
    · exact (h.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ ∞ by simp)).continuousAt
    · apply n07a_two_closed_branches_fderiv_continuousAt rfl _ hu hv hl hr
      filter_upwards [hopen.mem_nhds hp] with q hq
      exact hdiff q hq
  have hc : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) f (annularOpen D) :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hopen).mpr
      ⟨fun p hp => (hdiff p hp).differentiableWithinAt, by simp, contDiffOn_zero.mpr hdc⟩
  simpa only [zero_add] using hc

end ContinuousFlexibility.Analysis
