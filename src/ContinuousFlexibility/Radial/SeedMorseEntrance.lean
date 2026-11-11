import ContinuousFlexibility.Radial.SeedSelectedTailEntry
import ContinuousFlexibility.Radial.MorseChainScales
import ContinuousFlexibility.Radial.MorseCellMassTravel

/-!
# Positive profile derivatives at the inward Morse seams

The profile identity is differentiated on the open cell and extended by
continuity to its endpoints. Thus both inward cuts have strictly positive
profile derivative, including the first cell on each side.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open Statements
open scoped Topology ContDiff

theorem profile_deriv_of_cell_identity {w R : ℝ → ℝ} {a b amp A B : ℝ}
    (hw : ContDiff ℝ ∞ w) (hR : ContDiff ℝ ∞ R) (hab : a < b)
    (hcell : ∀ x ∈ Icc a b,
      deriv (deriv R) x = -morseRho A B x * R x ∧
      w (R x) = amp * deriv R x) :
    ∀ x ∈ Icc a b,
      deriv w (R x) * deriv R x = amp * (-morseRho A B x * R x) := by
  have hws : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hRs : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hclosed : IsClosed {x | deriv w (R x) * deriv R x =
      amp * (-morseRho A B x * R x)} :=
    isClosed_eq ((hws.continuous.comp hR.continuous).mul hRs.continuous)
      (continuous_const.mul ((contDiff_morseRho A B).continuous.neg.mul hR.continuous))
  have hopen : Ioo a b ⊆ {x | deriv w (R x) * deriv R x =
      amp * (-morseRho A B x * R x)} := by
    intro x hx
    have hg : (fun t => w (R t)) =ᶠ[𝓝 x] fun t => amp * deriv R t := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      exact (hcell t (Ioo_subset_Icc_self ht)).2
    have hd : deriv w (R x) * deriv R x = amp * deriv (deriv R) x :=
      (((hw.differentiable (by simp) (R x)).hasDerivAt).comp x
        (hR.differentiable (by simp) x).hasDerivAt).unique
        (((hRs.differentiable (by simp) x).hasDerivAt.const_mul amp).congr_of_eventuallyEq hg)
    change deriv w (R x) * deriv R x = amp * (-morseRho A B x * R x)
    rw [hd, (hcell x (Ioo_subset_Icc_self hx)).1]
  have hclosure := closure_minimal hopen hclosed
  rw [closure_Ioo hab.ne] at hclosure
  exact fun _ hx => hclosure hx

theorem morseRealization_seam_deriv_pos {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {C : ℕ → ℝ} (hreal : MorseChainRealization T σ D C)
    (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) (right : Bool) {n : ℕ}
    (hn : T.index ≤ n) :
    0 < deriv D.w (morseChainSeam T right n) := by
  have hacc := hreal.2.2.2.2.2.2.2.2.2
  have hw := hacc.1.2.2.1.1
  obtain ⟨hRs, hab, hcell⟩ := hreal.2.2.1 right n hn
  have hg := hreal.2.1 right n hn
  have hamp := morseChainAmplitude_pos T σ hσ n
  let x := if right then T.leftX right n else T.rightX right n
  have hx : x ∈ Icc (T.leftX right n) (T.rightX right n) := by
    cases right with
    | false => exact ⟨hab.le, le_rfl⟩
    | true => exact ⟨le_rfl, hab.le⟩
  have hr : 0 < T.radius right n x :=
    hacc.1.1.trans (hreal.2.2.2.2.1 right n hn ⟨x, hx, rfl⟩).1
  have he := profile_deriv_of_cell_identity hw hRs hab
    (fun t ht => ⟨(hcell t ht).2.1, (hcell t ht).2.2⟩) x hx
  have hρ : morseRho (morseChainA T n) (morseChainB T n) x < 0 := by
    cases right with
    | false =>
      apply morseRho_neg_after_right_turn hg.1 hg.2.1
      exact hg.2.2.2.2.1
    | true =>
      have hA : 0 < morseChainA T n := (mul_pos (by norm_num) hg.1).trans hg.2.1
      have hx' : x = morseCellLeftCut := hg.2.2.1
      rw [hx']
      unfold morseRho
      have hexp : exp (-2 * morseCellLeftCut) = exp (-morseCellLeftCut) ^ 2 := by
        rw [pow_two, ← exp_add]
        congr 1
        ring
      rw [hexp, exp_neg_morseCellLeftCut]
      nlinarith [hg.1]
  have hprod : 0 < deriv D.w (T.radius right n x) * deriv (T.radius right n) x := by
    rw [he]
    exact mul_pos hamp (mul_pos (neg_pos.mpr hρ) hr)
  exact (mul_pos_iff_of_pos_right (hcell x hx).1).mp hprod

theorem exists_seedSelectedTail_regular_entrance (hR07 : R07Statement) :
    ∃ S : SelectedTailData, IsSelectedTail S ∧
      ∀ right : Bool,
        S.entry right S.chain.index ∈ radialCore (S.family S.sigma) ∧
        0 < deriv (S.family S.sigma).w (S.entry right S.chain.index) ∧
        RadialNaturalTail (S.family S.sigma) right 2
          (S.entry right S.chain.index) (S.outgoing right 2) := by
  obtain ⟨S, hS⟩ := hR07
  obtain ⟨n, hn, _⟩ := hS.2.2.2.2.1 2 (by omega) (by decide)
  refine ⟨seedSelectedTailAtBand S n, isSelectedTail_seedSelectedTailAtBand hS hn, ?_⟩
  intro right
  have hd := hS.2.2.2.2.2 right n 2 (by omega) (by decide) hn
  rcases hd with ⟨_, he, _, _, _, hentry, _, _, _, _, _, hnatural, _⟩
  have hpos := morseRealization_seam_deriv_pos
    (hS.2.2.2.1 S.sigma hS.2.2.1).1 hS.2.2.1 right hn.1
  have hpos' : 0 < deriv (S.family S.sigma).w (S.entry right n) := by
    rw [hentry]
    exact hpos
  simpa [seedSelectedTailAtBand] using
    And.intro he (And.intro hpos' hnatural)

end ContinuousFlexibility.Radial
