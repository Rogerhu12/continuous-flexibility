import ContinuousFlexibility.Analysis.N07aActualMaterialComparison
import ContinuousFlexibility.Analysis.StateNeighborhood
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Material weight ratios for the actual reference transport

The reference and current jet certificates place every current inverse point
in one fixed relative material window of the corresponding reference point.
The local logarithmic material estimates therefore bound both transported
weights by the same constant on every reference piece. Continuity extends
these bounds across the null radial exceptional set of the reference atlas.

The neighborhood restriction is chosen before the state and before the global
transport. Thus these estimates apply to the same transport already furnished
by the qualitative construction, without choosing a replacement witness.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- A continuous scalar bound on an almost-everywhere radial interval cover
holds on the entire open cylinder, including the omitted radial interfaces. -/
theorem n04Realization_continuous_bound_of_radial_cover
    {a b B : ℝ} {left right : ℕ → ℝ}
    (hcover : ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo a b \ E,
      ∃ m : ℕ, r ∈ Ioo (left m) (right m))
    {f : PolarPoint → ℝ}
    (hf : ContinuousOn f (Ioo a b ×ˢ univ))
    (hbound : ∀ m : ℕ, ∀ p ∈ Ioo (left m) (right m) ×ˢ (univ : Set ℝ),
      f p ≤ B) :
    ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), f p ≤ B := by
  classical
  obtain ⟨E, hE, hcover⟩ := hcover
  intro p hp
  by_contra hbad
  let g : ℝ → ℝ := fun r => f (r, p.2)
  have hg : ContinuousOn g (Ioo a b) :=
    hf.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hopen : IsOpen (Ioo a b ∩ g ⁻¹' Ioi B) :=
    hg.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
  have hsub : Ioo a b ∩ g ⁻¹' Ioi B ⊆ E := by
    intro r hr
    by_contra hrE
    obtain ⟨m, hm⟩ := hcover r ⟨hr.1, hrE⟩
    exact (not_lt_of_ge (hbound m (r, p.2) ⟨hm, mem_univ _⟩)) hr.2
  have hzero : volume (Ioo a b ∩ g ⁻¹' Ioi B) = 0 :=
    measure_mono_null hsub hE
  exact hopen.measure_ne_zero volume ⟨p.1, hp.1, not_le.mp hbad⟩ hzero

/-- A local comparison for any positive radial weight extends through an
almost-everywhere radial cover under the actual displacement estimate. -/
theorem n04Realization_radial_weight_ratio_of_displacement
    {a b B δ : ℝ} {left right : ℕ → ℝ} {ell w : ℝ → ℝ}
    (hcover : ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo a b \ E,
      ∃ m : ℕ, r ∈ Ioo (left m) (right m))
    (hpieces : ∀ m, Ioo (left m) (right m) ⊆ Ioo a b)
    (hw : ContinuousOn w (Ioo a b))
    (hwp : ∀ r ∈ Ioo a b, 0 < w r)
    (hlocal : ∀ r₀ ∈ Ioo a b, ∀ r ∈ Ioo a b,
      |r - r₀| ≤ δ * ell r₀ → w r / w r₀ ≤ B)
    {τ : PolarPoint → PolarPoint}
    (hτ : ContinuousOn τ (Ioo a b ×ˢ univ))
    (hmap : MapsTo τ (Ioo a b ×ˢ univ) (Ioo a b ×ˢ univ))
    (hdisp : ∀ m : ℕ, ∀ p ∈ Ioo (left m) (right m) ×ˢ (univ : Set ℝ),
      |(τ p).1 - p.1| ≤ δ * ell p.1) :
    ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), w (τ p).1 / w p.1 ≤ B := by
  have hnum : ContinuousOn (fun p : PolarPoint => w (τ p).1)
      (Ioo a b ×ˢ univ) :=
    hw.comp hτ.fst (fun p hp => (hmap hp).1)
  have hden : ContinuousOn (fun p : PolarPoint => w p.1)
      (Ioo a b ×ˢ univ) :=
    hw.comp continuous_fst.continuousOn (fun p hp => hp.1)
  apply n04Realization_continuous_bound_of_radial_cover hcover
    (hnum.div hden (fun p hp => (hwp p.1 hp.1).ne'))
  intro m p hp
  have hpD : p ∈ Ioo a b ×ˢ (univ : Set ℝ) :=
    ⟨hpieces m hp.1, mem_univ _⟩
  exact hlocal p.1 hpD.1 (τ p).1 (hmap hpD).1 (hdisp m p hp)

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- Both material ratios of any continuous annulus-preserving realization of
the actual reference-to-current chart transition are uniformly bounded on one
common state neighborhood. In the primitive transport certificate these are
the two `E0` estimates with exponent zero. -/
theorem n04Realization_transport_weight_ratios_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
        ∀ τ : PolarPoint → PolarPoint,
          ContinuousOn τ (annularOpen D) →
          MapsTo τ (annularOpen D) (annularOpen D) →
          (∀ m, ∀ p ∈ referencePhysicalPieceOpen S K m,
            τ p = canonicalCurrentPoint C K z m p) →
          ∀ p ∈ annularOpen D,
            T.H (τ p).1 / T.H p.1 ≤ Real.exp 1 ∧
            T.M (τ p).1 / T.M p.1 ≤ Real.exp 1 := by
  obtain ⟨δ, hδ, hwindow⟩ := n07a_material_local_ratio_window hT
  obtain ⟨base', hb, η, hη, hηε, hdisplacement⟩ :=
    n07a_inverseChart_material_displacement hD hT hε hrefState hgeom href hcur hδ
  have hcover : ∃ E : Set ℝ, volume E = 0 ∧ ∀ r ∈ Ioo D.a D.b \ E,
      ∃ m : ℕ, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    obtain ⟨E, hE, hcover⟩ := hgeom.referencePartition
    exact ⟨E, hE, fun r hr => (hcover r hr).exists⟩
  have hpieces (m : ℕ) :
      Ioo (K.physicalLeft m) (K.physicalRight m) ⊆ Ioo D.a D.b :=
    (hgeom.referenceBounds m).2.2
  have hH : ContDiffOn ℝ ∞ T.H (radialCore D) := hT.1 T.H (by simp)
  have hM : ContDiffOn ℝ ∞ T.M (radialCore D) := hT.1 T.M (by simp)
  refine ⟨base', hb, η, hη, hηε, ?_⟩
  intro z hz hs τ hτ hmap heq
  let ζ : StateDirections S × ℝ :=
    (⟨z.1 - C.referenceState,
      (stateSectorSubmodule S).sub_mem hs hrefState.stateSector⟩, z.2)
  have hζ : ζ ∈ sectorNeighborhood S base' η η := hz
  have hζz : liftSectorParameter S C ζ = z := by
    apply Prod.ext
    · change C.referenceState + (z.1 - C.referenceState) = z.1
      exact (add_comm _ _).trans (sub_add_cancel _ _)
    · rfl
  have hdisp : ∀ m : ℕ, ∀ p ∈ referencePhysicalPieceOpen S K m,
      |(τ p).1 - p.1| ≤ δ * T.ell p.1 := by
    intro m p hp
    have hpref : p ∈ physicalPieceOpen S K (C.referenceState, 0) m := by
      rw [hgeom.referenceDomain m]
      exact hp
    have hchart := hgeom.charts (C.referenceState, 0)
      (reference_mem_stateNeighborhood S C base hε) hrefState.stateSector m
    have hy : K.chart (C.referenceState, 0) m p ∈ canonicalOpen S K m :=
      hchart.1 hpref
    have hinverse := hchart.2.2.1 p hpref
    have hd := hdisplacement ζ hζ m (K.chart (C.referenceState, 0) m p) hy
    rw [hζz, hinverse] at hd
    simpa only [heq m p hp, canonicalCurrentPoint] using hd
  have hHratio := n04Realization_radial_weight_ratio_of_displacement hcover hpieces
    hH.continuousOn (fun r hr => (hT.2.1 r hr).2.1)
    (fun r₀ hr₀ r hr hd => (hwindow r₀ hr₀ r hr hd).1) hτ hmap hdisp
  have hMratio := n04Realization_radial_weight_ratio_of_displacement hcover hpieces
    hM.continuousOn (fun r hr => zero_lt_one.trans_le (hT.2.1 r hr).2.2.2)
    (fun r₀ hr₀ r hr hd => (hwindow r₀ hr₀ r hr hd).2.2.1) hτ hmap hdisp
  exact fun p hp => ⟨hHratio p hp, hMratio p hp⟩

end ContinuousFlexibility.Analysis
