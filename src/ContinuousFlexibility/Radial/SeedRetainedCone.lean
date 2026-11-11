import ContinuousFlexibility.Radial.SeedConeTailGluing
import ContinuousFlexibility.Radial.SeedPureTailConstruction
import ContinuousFlexibility.Radial.SeedPureTailCanonical

/-!
# Retaining an arbitrarily long part of the original first cone

At an actual cone germ the logarithmic profile can be chosen affine on
the entire line.  Thus inward continuation leaves an exact cone all the
way up to the original cut.  The point at which the second-mode mixture
is replaced by a pure mode can be moved arbitrarily far inward, without
changing either function.  Subsequent canonicalization retains every
outward germ and preserves positivity of the profile derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem exists_seedLinearLogExtension {w : ℝ → ℝ} {e C : ℝ}
    (he : 0 < e) (hC : 0 < C) (hw : w =ᶠ[𝓝 e] (fun r => C * r)) :
    ∃ E : SeedPositiveLogExtension (fun y => log (w (exp y))) (log e),
      ∀ r, 0 < r → E.radialProfile r = C * r := by
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => t + log C) 1 y :=
    (hasDerivAt_id' y).add_const (log C)
  have hmap : Tendsto exp (𝓝 (log e)) (𝓝 e) := by
    simpa only [exp_log he] using (continuous_exp.tendsto (log e))
  have hg : (fun y : ℝ => y + log C) =ᶠ[𝓝 (log e)]
      (fun y => log (w (exp y))) := by
    filter_upwards [hw.comp_tendsto hmap] with y hy
    change y + log C = log (w (exp y))
    rw [hy, log_mul hC.ne' (exp_ne_zero y), log_exp]
    ring
  refine ⟨{
    logProfile := fun y => y + log C
    left := log e - 1
    right := log e + 1
    left_lt := by linarith
    right_gt := by linarith
    smooth := contDiff_id.add contDiff_const
    positive := fun y => by rw [(hd y).deriv]; norm_num
    germ := hg
    left_cone := fun y _ => (hd y).deriv
    right_cone := fun y _ => (hd y).deriv
  }, ?_⟩
  intro r hr
  change exp (log r + log C) = C * r
  rw [exp_add, exp_log hr, exp_log hC, mul_comm]

/-- At a prescribed old cone cut, the inward profile can remain that
same cone everywhere. No new selected tail or normalization is chosen. -/
theorem exists_seedConeTail_of_coneGerm {D : ReferenceData} {right : Bool} {entry C : ℝ}
    {u V : ℝ → ℝ} (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    (hC : 0 < C) (hcone : D.w =ᶠ[𝓝 entry] (fun r => C * r))
    (hV : ContDiff ℝ ∞ V)
    (hVtail : ∀ r ∈ radialTailInterval D right entry, V r = u r)
    (hVzero : ∀ r, (if right then D.b ≤ r else r ≤ D.a) → V r = 0)
    (hODE : radialJacobi 4 D.w V entry = 0 ∧
      ∀ r ∈ radialTailInterval D right entry, radialJacobi 4 D.w V r = 0)
    (hne : (V entry, deriv V entry) ≠ (0, 0)) :
    ∃ T : SeedConeTail D right entry u,
      ∀ r, 0 < r → (if right then r ≤ entry else entry ≤ r) →
        T.profile =ᶠ[𝓝 r] (fun t => C * t) := by
  obtain ⟨E, hE⟩ := exists_seedLinearLogExtension (hD.1.trans hentry.1) hC hcone
  obtain ⟨T, hT⟩ :=
    exists_seedConeTail_of_logExtension hD hentry E hV hVtail hVzero hODE hne
  refine ⟨T, fun r hr hi => (hT r hi).trans ?_⟩
  exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds hr) (fun t ht => hE t ht)

/-- Moving the cone cutoff inward changes no function. -/
def SeedConeTail.withCut {D : ReferenceData} {right : Bool} {entry : ℝ} {u : ℝ → ℝ}
    (T : SeedConeTail D right entry u) (cut : ℝ) (hcut : 0 < cut)
    (horder : if right then cut ≤ T.cut else T.cut ≤ cut) :
    SeedConeTail D right entry u :=
  { T with
    cut := cut
    cut_pos := hcut
    cut_order := by
      cases right
      · exact T.cut_order.trans_le horder
      · exact horder.trans_lt T.cut_order
    cone_eq := by
      intro r hr hi
      apply T.cone_eq r hr
      cases right
      · exact horder.trans_lt hi
      · exact hi.trans_le horder }

@[simp] theorem SeedConeTail.withCut_profile {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedConeTail D right entry u)
    (cut : ℝ) (hp : 0 < cut) (ho : if right then cut ≤ T.cut else T.cut ≤ cut) :
    (T.withCut cut hp ho).profile = T.profile := rfl

@[simp] theorem SeedConeTail.withCut_height {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedConeTail D right entry u)
    (cut : ℝ) (hp : 0 < cut) (ho : if right then cut ≤ T.cut else T.cut ≤ cut) :
    (T.withCut cut hp ho).height = T.height := rfl

@[simp] theorem SeedConeTail.withCut_cut {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedConeTail D right entry u)
    (cut : ℝ) (hp : 0 < cut) (ho : if right then cut ≤ T.cut else T.cut ≤ cut) :
    (T.withCut cut hp ho).cut = cut := rfl

/-- Canonicalize strictly inward of any prescribed cone cutoff. The
old profile and height germs, and each positive profile derivative, survive. -/
theorem SeedConeTail.toCanonical_retaining_at {D : ReferenceData} {right : Bool}
    {entry : ℝ} {u : ℝ → ℝ} (T : SeedConeTail D right entry u)
    (hD : RadialProfileGeometry D) (hentry : entry ∈ radialCore D)
    {cut : ℝ} (hp : 0 < cut) (ho : if right then cut ≤ T.cut else T.cut ≤ cut) :
    ∃ P : SeedPureTail D right entry u,
      P.mode = (if right then (-2 : ℝ) else 2) ∧
      (if right then P.cut < cut else cut < P.cut) ∧
      (∀ r, (if right then cut ≤ r else r ≤ cut) →
        P.profile =ᶠ[𝓝 r] T.profile ∧ P.height =ᶠ[𝓝 r] T.height) ∧
      ∀ r, 0 < r → 0 < deriv T.profile r → 0 < deriv P.profile r := by
  let T₀ := T.withCut cut hp ho
  obtain ⟨P, hPcut, hP, hPd⟩ := T₀.toPureTail_retaining hentry
  have hc : if right then P.cut < cut else cut < P.cut := hPcut
  obtain ⟨Q, hQmode, hQcut, hQ, hQd⟩ := P.toCanonical_retaining hD hentry
  refine ⟨Q, hQmode, ?_, ?_, ?_⟩
  · cases right
    · exact hc.trans_le hQcut
    · exact hQcut.trans_lt hc
  · intro r hr
    have hrP : if right then P.cut ≤ r else r ≤ P.cut := by
      cases right
      · exact hr.trans hc.le
      · exact hc.le.trans hr
    have h₁ := hP r hr
    have h₂ := hQ r hrP
    exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
  · intro r hr hd
    exact hQd r hr (hPd r hr hd)

end ContinuousFlexibility.Radial
