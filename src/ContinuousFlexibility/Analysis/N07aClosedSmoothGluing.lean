module

public import ContinuousFlexibility.Analysis.N07aClosedJets

/-!
# Gluing genuine within-smooth functions on two closed rectangles

Matching closed Taylor jets gives a Taylor series on the union. At the
interface, derivatives are joined with `HasFDerivWithinAt.union`; elsewhere
one side contains a relative neighborhood. Neither branch needs a smooth
extension to the other side of the interface.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem n07a_hasFDerivWithinAt_two_closed_rectangles
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l c r : ℝ} {T : Set ℝ}
    {u v : PolarPoint → F}
    {du dv : PolarPoint → PolarPoint →L[ℝ] F}
    (hu : ∀ p ∈ Icc l c ×ˢ T, HasFDerivWithinAt u (du p) (Icc l c ×ˢ T) p)
    (hv : ∀ p ∈ Icc c r ×ˢ T, HasFDerivWithinAt v (dv p) (Icc c r ×ˢ T) p)
    (hvalue : ∀ θ ∈ T, u (c, θ) = v (c, θ))
    (hderiv : ∀ θ ∈ T, du (c, θ) = dv (c, θ))
    (hlc : l ≤ c) (hcr : c ≤ r) :
    ∀ p ∈ Icc l r ×ˢ T,
      HasFDerivWithinAt (fun q => if q.1 ≤ c then u q else v q)
        (if p.1 ≤ c then du p else dv p) (Icc l r ×ˢ T) p := by
  rintro ⟨x, θ⟩ hp
  rcases lt_trichotomy x c with hlt | heq | hgt
  · have hside : (x, θ) ∈ Icc l c ×ˢ T := ⟨⟨hp.1.1, hlt.le⟩, hp.2⟩
    have hd : HasFDerivWithinAt
        (fun q => if q.1 ≤ c then u q else v q) (du (x, θ))
        (Icc l c ×ˢ T) (x, θ) :=
      (hu _ hside).congr (fun q hq => if_pos hq.1.2) (if_pos hlt.le)
    have hnhds : Icc l c ×ˢ T ∈ 𝓝[Icc l r ×ˢ T] (x, θ) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds hlt)]
        with q hq hqc
      exact ⟨⟨hq.1.1, hqc.le⟩, hq.2⟩
    simpa only [if_pos hlt.le] using hd.mono_of_mem_nhdsWithin hnhds
  · subst x
    have hleft : (c, θ) ∈ Icc l c ×ˢ T := ⟨⟨hlc, le_rfl⟩, hp.2⟩
    have hright : (c, θ) ∈ Icc c r ×ˢ T := ⟨⟨le_rfl, hcr⟩, hp.2⟩
    have hdl : HasFDerivWithinAt
        (fun q => if q.1 ≤ c then u q else v q) (du (c, θ))
        (Icc l c ×ˢ T) (c, θ) :=
      (hu _ hleft).congr (fun q hq => if_pos hq.1.2) (if_pos le_rfl)
    have hdr : HasFDerivWithinAt
        (fun q => if q.1 ≤ c then u q else v q) (du (c, θ))
        (Icc c r ×ˢ T) (c, θ) := by
      apply ((hv _ hright).congr_fderiv (hderiv θ hp.2).symm).congr
      · intro q hq
        change (if q.1 ≤ c then u q else v q) = v q
        by_cases hqc : q.1 ≤ c
        · have hqe : q.1 = c := le_antisymm hqc hq.1.1
          rw [if_pos hqc]
          simpa only [← hqe, Prod.eta] using hvalue q.2 hq.2
        · exact if_neg hqc
      · exact (if_pos le_rfl).trans (hvalue θ hp.2)
    have hunion : (Icc l c ×ˢ T) ∪ (Icc c r ×ˢ T) = Icc l r ×ˢ T := by
      rw [← union_prod]
      congr 1
      exact Icc_union_Icc_eq_Icc hlc hcr
    simpa only [hunion, if_pos le_rfl] using hdl.union hdr
  · have hside : (x, θ) ∈ Icc c r ×ˢ T := ⟨⟨hgt.le, hp.1.2⟩, hp.2⟩
    let V : Set PolarPoint := Ioc c r ×ˢ T
    have hV : V ⊆ Icc c r ×ˢ T := Set.prod_mono Ioc_subset_Icc_self Subset.rfl
    have hd : HasFDerivWithinAt
        (fun q => if q.1 ≤ c then u q else v q) (dv (x, θ)) V (x, θ) :=
      ((hv _ hside).mono hV).congr
        (fun q hq => if_neg (not_le_of_gt hq.1.1)) (if_neg (not_le_of_gt hgt))
    have hnhds : V ∈ 𝓝[Icc l r ×ˢ T] (x, θ) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_fst).mem_nhds hgt)]
        with q hq hqc
      exact ⟨⟨hqc, hq.1.2⟩, hq.2⟩
    simpa only [if_neg (not_le_of_gt hgt)] using hd.mono_of_mem_nhdsWithin hnhds

/-- Closed Taylor jets suffice for genuine smooth gluing on the union. -/
theorem n07a_contDiffOn_two_closed_rectangles
    {l c r : ℝ} (hlc : l < c) (hcr : c < r)
    {T : Set ℝ} (hT : UniqueDiffOn ℝ T)
    {u v : PolarPoint → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Icc l c ×ˢ T))
    (hv : ContDiffOn ℝ ∞ v (Icc c r ×ˢ T))
    (hjets : ∀ n : ℕ, ∀ θ ∈ T,
      iteratedFDerivWithin ℝ n u (Icc l c ×ˢ T) (c, θ) =
        iteratedFDerivWithin ℝ n v (Icc c r ×ˢ T) (c, θ)) :
    ContDiffOn ℝ ∞ (fun p => if p.1 ≤ c then u p else v p) (Icc l r ×ˢ T) := by
  let Pu := ftaylorSeriesWithin ℝ u (Icc l c ×ˢ T)
  let Pv := ftaylorSeriesWithin ℝ v (Icc c r ×ˢ T)
  let P : PolarPoint → FormalMultilinearSeries ℝ PolarPoint ℝ :=
    fun p n => if p.1 ≤ c then Pu p n else Pv p n
  have hPu := hu.ftaylorSeriesWithin ((uniqueDiffOn_Icc hlc).prod hT)
  have hPv := hv.ftaylorSeriesWithin ((uniqueDiffOn_Icc hcr).prod hT)
  have hmatch (n : ℕ) (θ : ℝ) (hθ : θ ∈ T) : Pu (c, θ) n = Pv (c, θ) n :=
    hjets n θ hθ
  have hdiff (n : ℕ) (p : PolarPoint) (hp : p ∈ Icc l r ×ˢ T) :
      HasFDerivWithinAt (fun q => P q n) (P p (n + 1)).curryLeft
        (Icc l r ×ˢ T) p := by
    have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
    have hd := n07a_hasFDerivWithinAt_two_closed_rectangles
      (fun q hq => hPu.fderivWithin n hn q hq)
      (fun q hq => hPv.fderivWithin n hn q hq)
      (hmatch n)
      (fun θ hθ => congrArg ContinuousMultilinearMap.curryLeft (hmatch (n + 1) θ hθ))
      hlc.le hcr.le p hp
    by_cases hpc : p.1 ≤ c
    · simpa only [P, if_pos hpc] using hd
    · simpa only [P, if_neg hpc] using hd
  have hseries : HasFTaylorSeriesUpToOn ∞
      (fun p => if p.1 ≤ c then u p else v p) P (Icc l r ×ˢ T) := by
    refine ⟨?_, fun n _ p hp => hdiff n p hp, ?_⟩
    · intro p hp
      by_cases hpc : p.1 ≤ c
      · simpa only [P, if_pos hpc] using hPu.zero_eq p ⟨⟨hp.1.1, hpc⟩, hp.2⟩
      · simpa only [P, if_neg hpc] using
          hPv.zero_eq p ⟨⟨(lt_of_not_ge hpc).le, hp.1.2⟩, hp.2⟩
    · intro n _ p hp
      exact (hdiff n p hp).continuousWithinAt
  exact hseries.contDiffOn

end ContinuousFlexibility.Analysis
