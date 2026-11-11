import ContinuousFlexibility.Statements.RadialTargets
import ContinuousFlexibility.Analysis.OneSidedSmoothExtension
import ContinuousFlexibility.Radial.MorseChainFlatExtension
import ContinuousFlexibility.Radial.CentralStatementBridges
import ContinuousFlexibility.Radial.SeedPairGluing

/-!
# Smooth extensions and regular entrance equations for radial tails

A regular entrance and an endpoint-flat germ give a global smooth
outward zero extension. These local analytic facts do not depend on
the quantitative construction that produces the flat germ.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- A smooth regular entrance and a smooth flat outward germ give a
global representative equal to the original function on the closed
entrance side and equal to zero past the outward endpoint. -/
theorem smooth_zero_right_of_flat_germ {f v : ℝ → ℝ} {c e d : ℝ}
    (hce : c < e) (hed : e < d) (hf₀ : ContDiffAt ℝ ∞ f c)
    (hf : ContDiffOn ℝ ∞ f (Ioo c d)) (hv : ContDiff ℝ ∞ v)
    (heq : EqOn v f (Ioo e d)) (hjet : ∀ k, iteratedDeriv k v d = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (Ico c d) ∧
      ∀ k x, d ≤ x → iteratedDeriv k F x = 0 := by
  have hcd : c < d := hce.trans hed
  have hfclosed : ContDiffOn ℝ ∞ f (Ico c d) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hcx | hcx
    · subst x
      exact hf₀.contDiffWithinAt
    · exact (hf.contDiffAt (isOpen_Ioo.mem_nhds ⟨hcx, hx.2⟩)).contDiffWithinAt
  obtain ⟨U, hUeq, hU⟩ := exists_contDiffOn_Iio_extension_of_Ico hcd hfclosed
  let F : ℝ → ℝ := fun x => if x < d then U x else 0
  have hFeq : EqOn F f (Ico c d) := by
    intro x hx
    exact (if_pos hx.2).trans (hUeq hx)
  have hFsmooth : ContDiffOn ℝ ∞ F (Iio d) := by
    intro x hx
    apply ((hU.contDiffAt (isOpen_Iio.mem_nhds hx)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_lt_nhds (show x < d from hx)] with y hy
    exact if_pos hy
  have hzero : ∀ x, d ≤ x → F x = 0 :=
    fun x hx => if_neg (not_lt.mpr hx)
  have hlim (k : ℕ) : Tendsto (iteratedDeriv k F) (𝓝[<] d) (𝓝 0) := by
    have hvlim : Tendsto (iteratedDeriv k v) (𝓝[<] d) (𝓝 0) := by
      simpa only [hjet k] using
        ((ContDiff.continuous_iteratedDeriv k hv (by simp)).continuousAt (x := d)).tendsto.mono_left
          nhdsWithin_le_nhds
    apply hvlim.congr'
    filter_upwards [Ioo_mem_nhdsLT hed] with x hx
    have hgerm : F =ᶠ[𝓝 x] v := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact (hFeq ⟨(hce.trans hy.1).le, hy.2⟩).trans (heq hy).symm
    exact (hgerm.iteratedDeriv_eq k).symm
  have hflat := contDiff_flat_of_left_jet_limits hFsmooth hzero hlim
  exact ⟨F, hflat.1, hFeq, hflat.2⟩

/-- The same theorem reflected, preserving the original closed entrance. -/
theorem smooth_zero_left_of_flat_germ {f v : ℝ → ℝ} {c e d : ℝ}
    (hce : c < e) (hed : e < d) (hf₀ : ContDiffAt ℝ ∞ f d)
    (hf : ContDiffOn ℝ ∞ f (Ioo c d)) (hv : ContDiff ℝ ∞ v)
    (heq : EqOn v f (Ioo c e)) (hjet : ∀ k, iteratedDeriv k v c = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (Ioc c d) ∧
      ∀ k x, x ≤ c → iteratedDeriv k F x = 0 := by
  have hf₀' : ContDiffAt ℝ ∞ (fun x => f (-x)) (-d) := by
    have hh : ContDiffAt ℝ ∞ f (-(-d)) := by simpa only [neg_neg] using hf₀
    exact hh.comp (-d) contDiffAt_id.neg
  have hf' : ContDiffOn ℝ ∞ (fun x => f (-x)) (Ioo (-d) (-c)) :=
    hf.comp contDiff_id.neg.contDiffOn
      (fun x hx => ⟨by linarith only [hx.2], by linarith only [hx.1]⟩)
  have heq' : EqOn (fun x => v (-x)) (fun x => f (-x)) (Ioo (-e) (-c)) := by
    intro x hx
    apply heq
    exact ⟨by linarith only [hx.2], by linarith only [hx.1]⟩
  have hjet' (k : ℕ) : iteratedDeriv k (fun x => v (-x)) (-c) = 0 := by
    rw [iteratedDeriv_comp_neg, neg_neg, hjet k, smul_zero]
  obtain ⟨U, hU, hUeq, hUzero⟩ := smooth_zero_right_of_flat_germ
    (neg_lt_neg hed) (neg_lt_neg hce) hf₀' hf' (hv.comp contDiff_id.neg) heq' hjet'
  refine ⟨fun x => U (-x), hU.comp contDiff_id.neg, ?_, ?_⟩
  · intro x hx
    have hh := hUeq ⟨neg_le_neg hx.2, neg_lt_neg hx.1⟩
    simpa only [neg_neg] using hh
  · intro k x hx
    rw [iteratedDeriv_comp_neg, hUzero k (-x) (neg_le_neg hx), smul_zero]

private theorem iteratedDeriv_entry_eq_of_eqOn {f g : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (hS : UniqueDiffOn ℝ S) (hc : c ∈ S)
    (hf : ContDiffAt ℝ ∞ f c) (hg : ContDiffAt ℝ ∞ g c) (heq : EqOn f g S)
    (k : ℕ) : iteratedDeriv k f c = iteratedDeriv k g c := by
  calc
    _ = iteratedDerivWithin k f S c :=
      (iteratedDerivWithin_eq_iteratedDeriv hS (hf.of_le (by simp)) hc).symm
    _ = iteratedDerivWithin k g S c := iteratedDerivWithin_congr heq hc
    _ = _ := iteratedDerivWithin_eq_iteratedDeriv hS (hg.of_le (by simp)) hc

/-- Equality on the full tail and at the regular entrance preserves
every actual entrance jet, including the logarithmic matching slope. -/
theorem radialTail_extension_entry_jets {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u v : ℝ → ℝ} (hentry : entry ∈ radialCore D)
    (hu : ContDiffAt ℝ ∞ u entry) (hv : ContDiffAt ℝ ∞ v entry)
    (hvalue : v entry = u entry)
    (heq : ∀ r ∈ radialTailInterval D right entry, v r = u r) (k : ℕ) :
    radialJet k v entry = radialJet k u entry := by
  rw [radialJet_eq_iteratedDeriv, radialJet_eq_iteratedDeriv]
  cases right
  · apply iteratedDeriv_entry_eq_of_eqOn (uniqueDiffOn_Ioc D.a entry)
      (show entry ∈ Ioc D.a entry from ⟨hentry.1, le_rfl⟩) hv hu _ k
    intro r hr
    rcases eq_or_lt_of_le hr.2 with hr' | hr'
    · subst r
      exact hvalue
    · exact heq r ⟨hr.1, hr'⟩
  · apply iteratedDeriv_entry_eq_of_eqOn (uniqueDiffOn_Ico entry D.b)
      (show entry ∈ Ico entry D.b from ⟨le_rfl, hentry.2⟩) hv hu _ k
    intro r hr
    rcases eq_or_lt_of_le hr.1 with hr' | hr'
    · subst r
      exact hvalue
    · exact heq r ⟨hr', hr.2⟩

theorem morseSecondMode_radialJacobi_continuousAt {w v : ℝ → ℝ} {a r : ℝ}
    (hw : ContDiffAt ℝ ∞ w r) (hv : ContDiffAt ℝ ∞ v r) (hr : r ≠ 0) :
    ContinuousAt (radialJacobi a w v) r := by
  have hv' : ContDiffAt ℝ ∞ (deriv v) r := hv.derivWithin (m := ∞) (by simp)
  have hflux : ContDiffAt ℝ ∞ (fun t => w t * deriv v t) r := hw.mul hv'
  have hflux' := (hflux.derivWithin (m := ∞) (by simp)).continuousAt
  have hw' := (hw.derivWithin (m := ∞) (by simp)).continuousAt
  exact hflux'.sub (((continuousAt_const.mul hw').div continuousAt_id hr).mul hv.continuousAt)

/-- Continuity of the actual Jacobi expression carries a homogeneous
equation from an open tail to its regular entrance. -/
theorem radialJacobi_zero_at_tail_entry {D : ReferenceData} {right : Bool}
    {entry a : ℝ} {v : ℝ → ℝ} (hD : RadialProfileGeometry D)
    (hentry : entry ∈ radialCore D) (hv : ContDiffAt ℝ ∞ v entry)
    (hode : ∀ r ∈ radialTailInterval D right entry, radialJacobi a D.w v r = 0) :
    radialJacobi a D.w v entry = 0 := by
  have hcont : ContinuousAt (radialJacobi a D.w v) entry :=
    morseSecondMode_radialJacobi_continuousAt hD.2.2.1.1.contDiffAt hv
      (hD.1.trans hentry.1).ne'
  cases right
  · have he : radialJacobi a D.w v =ᶠ[𝓝[<] entry] (fun _ : ℝ => (0 : ℝ)) :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT hentry.1) (fun r hr => hode r hr)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' he.symm)
  · have he : radialJacobi a D.w v =ᶠ[𝓝[>] entry] (fun _ : ℝ => (0 : ℝ)) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT hentry.2) (fun r hr => hode r hr)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' he.symm)

theorem radialNaturalTail_entry_radialJacobi {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (hD : RadialProfileGeometry D)
    (hentry : entry ∈ radialCore D) (hu : RadialNaturalTail D right 2 entry u) :
    radialJacobi 4 D.w u entry = 0 := by
  apply radialJacobi_zero_at_tail_entry hD hentry hu.1
  intro r hr
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hu.2.1.2 r hr

/-- A smooth extension satisfying the original equation on the open
tail also satisfies it at the regular entrance. -/
theorem radialTail_extension_radialJacobi {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u v : ℝ → ℝ} (hD : RadialProfileGeometry D)
    (hentry : entry ∈ radialCore D) (hu : RadialNaturalTail D right 2 entry u)
    (hv : ContDiff ℝ ∞ v)
    (heq : ∀ r ∈ radialTailInterval D right entry, v r = u r) :
    radialJacobi 4 D.w v entry = 0 ∧
      ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w v r = 0 := by
  have hopen : IsOpen (radialTailInterval D right entry) := by
    cases right <;> exact isOpen_Ioo
  have hode : ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w v r = 0 := by
    intro r hr
    have hgerm : v =ᶠ[𝓝 r] u :=
      Filter.mem_of_superset (hopen.mem_nhds hr) (fun t ht => heq t ht)
    rw [radialJacobi_eq_of_germs
      (Filter.EventuallyEq.rfl : D.w =ᶠ[𝓝 r] D.w) hgerm]
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hu.2.1.2 r hr
  exact ⟨radialJacobi_zero_at_tail_entry hD hentry hv.contDiffAt hode, hode⟩

end ContinuousFlexibility.Radial
