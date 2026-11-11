import ContinuousFlexibility.Radial.WeakDivergenceRegularity
import ContinuousFlexibility.Radial.ModeCompactLocal
import Mathlib.Topology.Compactness.Lindelof

/-!
# C1 representatives of modal weak solutions

Compact regularity patches glue to a single C1 representative on the
whole radial core. The gluing uses uniqueness of continuous functions
that agree almost everywhere on an open set. A countable open subcover
ensures that the resulting representative agrees almost everywhere with
the original modal Hilbert-space element.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Local globally C1 representatives of an almost-everywhere function
glue to a C1 representative on the whole set. -/
theorem exists_contDiffOn_representative_of_locally
    {U : Set ℝ} {u : ℝ → ℝ}
    (hlocal : ∀ x ∈ U, ∃ V : Set ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 1 f ∧
        u =ᵐ[volume.restrict V] f) :
    ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 1 v U ∧
      u =ᵐ[volume.restrict U] v := by
  classical
  have hh (x : U) : ∃ V : Set ℝ,
      IsOpen V ∧ (x : ℝ) ∈ V ∧ V ⊆ U ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 1 f ∧
        u =ᵐ[volume.restrict V] f := hlocal x x.2
  choose V hVo hVx hVU f hf huf using hh
  let v (x : ℝ) : ℝ := if hx : x ∈ U then f ⟨x, hx⟩ x else 0
  have hvf (x : U) : EqOn v (f x) (V x) := by
    intro y hy
    have hyU : y ∈ U := hVU x hy
    let z : U := ⟨y, hyU⟩
    have hxy : f x =ᵐ[volume.restrict (V x ∩ V z)] f z :=
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left (huf x)).symm.trans
        (ae_restrict_of_ae_restrict_of_subset inter_subset_right (huf z))
    have hp : EqOn (f x) (f z) (V x ∩ V z) :=
      Measure.eqOn_open_of_ae_eq hxy ((hVo x).inter (hVo z))
        (hf x).continuous.continuousOn (hf z).continuous.continuousOn
    have hyrep := hp y ⟨hy, hVx z⟩
    dsimp only [v]
    rw [dif_pos hyU]
    exact hyrep.symm
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    let z : U := ⟨x, hx⟩
    have heq : v =ᶠ[𝓝 x] f z := by
      filter_upwards [(hVo z).mem_nhds (hVx z)] with y hy
      exact hvf z hy
    exact ((hf z).contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hcover : U ⊆ ⋃ x : U, V x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩
    obtain ⟨T, hTc, hTU⟩ :=
      (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo hcover
    have hbig : u =ᵐ[volume.restrict (⋃ x ∈ T, V x)] v := by
      rw [ae_eq_restrict_biUnion_iff V hTc u v]
      intro x hx
      filter_upwards [huf x, self_mem_ae_restrict (hVo x).measurableSet] with y hy hyV
      exact hy.trans (hvf x hyV).symm
    exact ae_restrict_of_ae_restrict_of_subset hTU hbig

/-- A modal weak solution has a globally C1 representative on each
compact interior interval, together with its absolutely continuous flux. -/
theorem modeLocalEquation_contDiff_representative_on_compact
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j J U F) {l h : ℝ}
    (hlh : l < h) (hsub : Icc l h ⊆ radialCore D) (hJ : Ioo l h ⊆ J) :
    ∃ v : ℝ → ℝ, ∃ C : ℝ,
      ContDiff ℝ 1 v ∧
      (U.1 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo l h)] v ∧
      (∀ x ∈ Icc l h,
        D.w x * deriv v x = C + ∫ t in l..x, matchingPrincipalSource D j U F t) ∧
      AbsolutelyContinuousOnInterval (fun x => D.w x * deriv v x) l h ∧
      (deriv (fun x => D.w x * deriv v x) =ᵐ[volume.restrict (Ioo l h)]
        matchingPrincipalSource D j U F) := by
  have hg := matchingProfileGeometry hD
  apply exists_contDiff_representative_of_weak_divergence hlh
    (matchingMode_intervalIntegrable hD U.1 hlh.le hsub)
    (matchingPrincipalSource_intervalIntegrable hD hB j U F hlh.le hsub)
    hg.2.2.1.1
  · intro x hx
    exact (hg.2.2.2.2.1 x (hsub hx)).ne'
  · intro ψ hψ hcψ hψs
    exact modeLocalEquation_principal_on_compact hD hB hEq hlh.le hsub hJ hψ hcψ hψs

/-- Every modal weak solution on the full radial core has one C1
representative on that entire open core. It agrees almost everywhere
both for ordinary Lebesgue measure and for the actual radial Hilbert measure. -/
theorem modeLocalEquation_contDiffOn_representative
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j (radialCore D) U F) :
    ∃ v : ℝ → ℝ,
      ContDiffOn ℝ 1 v (radialCore D) ∧
      (U.1 : ℝ → ℝ) =ᵐ[volume.restrict (radialCore D)] v ∧
      (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] v := by
  have hlocal : ∀ x ∈ radialCore D, ∃ V : Set ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ radialCore D ∧
      ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧
        (U.1 : ℝ → ℝ) =ᵐ[volume.restrict V] v := by
    intro x hx
    change D.a < x ∧ x < D.b at hx
    let l : ℝ := (D.a + x) / 2
    let h : ℝ := (x + D.b) / 2
    have hlx : l < x := by dsimp only [l]; linarith [hx.1]
    have hxh : x < h := by dsimp only [h]; linarith [hx.2]
    have hlh : l < h := hlx.trans hxh
    have hsub : Icc l h ⊆ radialCore D := by
      intro y hy
      change D.a < y ∧ y < D.b
      dsimp only [l, h] at hy
      exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    have hsubo : Ioo l h ⊆ radialCore D := Ioo_subset_Icc_self.trans hsub
    obtain ⟨v, C, hv, huv, hflux, hfluxac, hfluxd⟩ :=
      modeLocalEquation_contDiff_representative_on_compact hD hB hEq hlh hsub hsubo
    exact ⟨Ioo l h, isOpen_Ioo, ⟨hlx, hxh⟩, hsubo, v, hv, huv⟩
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_representative_of_locally hlocal
  refine ⟨v, hv, huv, ?_⟩
  exact (withDensity_absolutelyContinuous _ _).ae_eq huv

end ContinuousFlexibility.Radial
