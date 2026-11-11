import ContinuousFlexibility.Radial.R07PhysicalNormalization
import ContinuousFlexibility.Radial.R07NaturalContinuation
import ContinuousFlexibility.Radial.R07RadialTransport
import ContinuousFlexibility.Radial.R07HeightCubeExtension

/-!
# A continuous family of actual outgoing natural solutions

The normalized R06 family is converted to globally smooth physical
representatives, continued to a fixed matching radius, and transported by
the actual radial equation.  This constructs the outgoing state used in
height selection rather than assuming a continuous choice of that state.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def r07OutgoingState (j : ℕ) (entry : ℝ) (v : ℝ → ℝ) : ℝ × ℝ :=
  (v entry, entry * deriv v entry / (j : ℝ) ^ 2 - v entry)

/-- The actual natural equation holds on the closed segment joining its
entrance to any deeper interior radius. -/
theorem radialNaturalTail_zero_uIcc {D : ReferenceData} (hD : RadialProfileGeometry D)
    {side : Bool} {j : ℕ} {e f : ℝ} (he : e ∈ radialCore D) (hf : f ∈ radialCore D)
    (hef : if side then e < f else f < e) {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hN : RadialNaturalTail D side j e v) :
    ∀ r ∈ uIcc e f, radialJacobi ((j : ℝ) ^ 2) D.w v r = 0 := by
  have hne : e ≠ f := by
    cases side
    · exact (ne_of_lt hef).symm
    · exact ne_of_lt hef
  have hlt : min e f < max e f := min_lt_max.mpr hne
  apply radialJacobi_zero_on_Icc hD.2.2.1.1 hv
    (hD.1.trans (lt_min he.1 hf.1)) hlt
  intro r hr
  apply hN.2.1.2 r
  cases side
  · rw [min_eq_right hef.le, max_eq_left hef.le] at hr
    exact ⟨hf.1.trans hr.1, hr.2⟩
  · rw [min_eq_left hef.le, max_eq_right hef.le] at hr
    exact ⟨hr.1, hr.2.trans hf.2⟩

theorem r07OutgoingState_ne_zero {D : ReferenceData} (hD : RadialProfileGeometry D)
    {side : Bool} {j : ℕ} {e : ℝ} (hj : 2 ≤ j) (he : e ∈ radialCore D)
    {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hN : RadialNaturalTail D side j e v) :
    r07OutgoingState j e v ≠ (0, 0) := by
  intro hzero
  have hvalue : v e = 0 := congrArg Prod.fst hzero
  have hsecond : e * deriv v e / (j : ℝ) ^ 2 - v e = 0 := congrArg Prod.snd hzero
  have hjn : (j : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : j ≠ 0))
  have he' : e ≠ 0 := (hD.1.trans he.1).ne'
  have hquot : e * deriv v e / (j : ℝ) ^ 2 = 0 := by simpa only [hvalue, sub_zero] using hsecond
  have hmul : e * deriv v e = 0 := (div_eq_zero_iff.mp hquot).resolve_right hjn
  have hderiv : deriv v e = 0 := (mul_eq_zero.mp hmul).resolve_left he'
  exact radialNaturalTail_cauchyData_ne_zero hD he hv hN (Prod.ext hvalue hderiv)

/-- Given the actual complete R06 data for a height family, its normalized
parameter theorem constructs a continuous nonzero physical outgoing state
at an earlier fixed matching radius.  The returned solutions retain the
explicit normalized deep Cauchy data, which will prove update invariance. -/
theorem exists_continuous_radialNaturalFamily_of_R06_data
    (D : HeightRatios → ReferenceData) (Q : HeightRatios → DeepTailData)
    (side : Bool) (j start : ℕ) {η₀ K₀ e f : ℝ} (hj : 2 ≤ j)
    (hparameter : DeepTailParameterContinuity η₀ K₀)
    (hQ : ∀ σ, DeepTailHypotheses (Q σ) ∧ (Q σ).η ≤ η₀ ∧ K₀ ≤ (Q σ).K)
    (hfixed : ∀ σ τ, (Q σ).entrance = (Q τ).entrance ∧
      (Q σ).endpoint = (Q τ).endpoint ∧ (Q σ).node = (Q τ).node ∧
      (Q σ).Λ = (Q τ).Λ ∧ (Q σ).η = (Q τ).η ∧ (Q σ).K = (Q τ).K)
    (hjets : ∀ k, ContinuousOn (fun z : HeightRatios × ℝ => radialJet k (Q z.1).p z.2)
      {z | z.2 ∈ Ico (Q z.1).entrance (Q z.1).endpoint})
    (hacc : ∀ σ, IsAccumulatingProfile (D σ))
    (hends : ∀ σ τ, (D σ).a = (D τ).a ∧ (D σ).b = (D τ).b)
    (hline : ∀ σ, TailNaturalLineAndKernel (Q σ))
    (hflat : ∀ σ, TailPhysicalFlatConclusion (D σ) (Q σ) side j start)
    (hrelation : ∀ σ, TailPhysicalRelation (D σ) (Q σ) side j start)
    (hentrance : ∀ σ, tailPhysicalRadius side (Q σ).entrance = f)
    (he : ∀ σ, e ∈ radialCore (D σ)) (hf : ∀ σ, f ∈ radialCore (D σ))
    (hef : if side then e < f else f < e)
    (hw₀ : ContinuousOn (fun z : HeightRatios × ℝ => (D z.1).w z.2)
      {z | z.2 ∈ uIcc f e})
    (hw₁ : ContinuousOn (fun z : HeightRatios × ℝ => deriv (D z.1).w z.2)
      {z | z.2 ∈ uIcc f e}) :
    ∃ U V : HeightRatios → ℝ → ℝ,
      (∀ σ, TailNaturalEquation (Q σ) (U σ) ∧ U σ (Q σ).entrance = 1) ∧
      (∀ σ, ContDiff ℝ ∞ (V σ) ∧ RadialNaturalTail (D σ) side j e (V σ) ∧
        V σ f = r07PhysicalGauge (if side then (D σ).b else (D σ).a) side j (Q σ).entrance ∧
        deriv (V σ) f = r07PhysicalInitialSlope (if side then (D σ).b else (D σ).a)
          side j (Q σ).entrance (deriv (U σ) (Q σ).entrance)) ∧
      Continuous (fun σ => r07OutgoingState j e (V σ)) ∧
      ∀ σ, r07OutgoingState j e (V σ) ≠ (0, 0) := by
  obtain ⟨U, hU, hUc⟩ := hparameter Q hQ hfixed hjets
  have hgeometry (σ : HeightRatios) : RadialProfileGeometry (D σ) :=
    (Classical.choose_spec (hacc σ)).1
  have hnormalized (σ : HeightRatios) : ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      RadialNaturalTail (D σ) side j f v ∧
      v f = r07PhysicalGauge (if side then (D σ).b else (D σ).a) side j (Q σ).entrance ∧
      deriv v f = r07PhysicalInitialSlope (if side then (D σ).b else (D σ).a)
        side j (Q σ).entrance (deriv (U σ) (Q σ).entrance) := by
    have hend : (Q σ).endpoint = r07OutwardLog side (if side then (D σ).b else (D σ).a) := by
      cases side <;> exact (hrelation σ).2.1
    simpa only [hentrance σ] using exists_normalized_physicalNaturalTail
      (hacc σ) (hQ σ).1.1 hend (hline σ) (hflat σ) (hU σ).1 (hU σ).2
  choose v hv hNv hv₀ hv₁ using hnormalized
  have hcontinued (σ : HeightRatios) : ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      RadialNaturalTail (D σ) side j e u ∧ u f = v σ f ∧ deriv u f = deriv (v σ) f :=
    exists_radialNaturalTail_continuation_with_cauchy (hgeometry σ) (he σ) (hf σ) hef (hv σ) (hNv σ)
  choose V hV hNV hV₀ hV₁ using hcontinued
  have hvalue (σ : HeightRatios) := (hV₀ σ).trans (hv₀ σ)
  have hslope (σ : HeightRatios) := (hV₁ σ).trans (hv₁ σ)
  let base : HeightRatios := ⟨fun _ => 1, fun _ => ⟨le_rfl, by norm_num⟩⟩
  let endpoint : ℝ := if side then (D base).b else (D base).a
  let entrance : ℝ := (Q base).entrance
  have hEnd (σ : HeightRatios) : (if side then (D σ).b else (D σ).a) = endpoint := by
    cases side
    · exact (hends σ base).1
    · exact (hends σ base).2
  have hEntry (σ : HeightRatios) : (Q σ).entrance = entrance := (hfixed σ base).1
  have hvalue_eq : (fun σ => V σ f) = fun _ => r07PhysicalGauge endpoint side j entrance := by
    funext σ
    rw [hvalue σ, hEnd σ, hEntry σ]
  have hslope_eq : (fun σ => deriv (V σ) f) = fun σ =>
      r07PhysicalInitialSlope endpoint side j entrance (deriv (U σ) (Q σ).entrance) := by
    funext σ
    exact (hslope σ).trans (congrArg
      (fun z : ℝ × ℝ => r07PhysicalInitialSlope z.1 side j z.2 (deriv (U σ) (Q σ).entrance))
      (Prod.ext (hEnd σ) (hEntry σ)))
  have hinit₀ : Continuous (fun σ => V σ f) := by rw [hvalue_eq]; exact continuous_const
  have hinit₁ : Continuous (fun σ => deriv (V σ) f) := by
    rw [hslope_eq]
    unfold r07PhysicalInitialSlope
    exact (continuous_const.add (continuous_const.mul hUc)).div_const _
  have hcore (σ : HeightRatios) (r : ℝ) (hr : r ∈ uIcc f e) : r ∈ radialCore (D σ) :=
    ⟨(lt_min (hf σ).1 (he σ).1).trans_le hr.1,
      hr.2.trans_lt (max_lt (hf σ).2 (he σ).2)⟩
  have hODE (σ : HeightRatios) (r : ℝ) (hr : r ∈ uIcc f e) :
      radialJacobi ((j : ℝ) ^ 2) (D σ).w (V σ) r = 0 :=
    radialNaturalTail_zero_uIcc (hgeometry σ) (he σ) (hf σ) hef (hV σ) (hNV σ) r
      (by simpa only [uIcc_comm f e] using hr)
  have hCauchy := continuous_radialCauchyData_transport j
    (fun σ => (hgeometry σ).2.2.1.1) hV hw₀ hw₁
    (fun σ r hr => ((hgeometry σ).2.2.2.2.1 r (hcore σ r hr)).ne')
    (fun r hr => ((hgeometry base).1.trans (hcore base r hr).1).ne')
    hODE hinit₀ hinit₁
  refine ⟨U, V, hU, fun σ => ⟨hV σ, hNV σ, hvalue σ, hslope σ⟩, ?_, ?_⟩
  · change Continuous (fun σ => (V σ e, e * deriv (V σ) e / (j : ℝ) ^ 2 - V σ e))
    exact hCauchy.fst.prodMk
      (((continuous_const.mul hCauchy.snd).div_const ((j : ℝ) ^ 2)).sub hCauchy.fst)
  · intro σ
    exact r07OutgoingState_ne_zero (hgeometry σ) hj (he σ) (hV σ) (hNV σ)

end ContinuousFlexibility.Radial
