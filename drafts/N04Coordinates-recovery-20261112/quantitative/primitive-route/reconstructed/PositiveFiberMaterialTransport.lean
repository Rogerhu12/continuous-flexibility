import ContinuousFlexibility.Analysis.EndpointDistanceMaterialTransport
import ContinuousFlexibility.Analysis.PositiveMaterialExitChoice
import ContinuousFlexibility.Analysis.PositiveFiberClosedGeometry

/-!
# Uniform material ratios for the displayed positive fiber map

The actual scalar derivative and its fixed values keep each exit collar
inside itself. Interior collars use the explicit ambient-distance caps;
an ambient collar uses its actual identity data. This proves the weight
ratios for the displayed map, with no positive-component host and no
transport-ratio premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem positiveFiberChart_endpointX_shift_of_capped_exits
    {D : ReferenceData} {φ Y : PolarPoint → ℝ} {l r c d B : ℝ}
    (ha : D.a ≤ l) (hlc : l < c) (hcd : c < d) (hdr : d < r) (hb : r ≤ D.b)
    (hY : ContDiff ℝ ∞ Y) (hB : 0 < B)
    (hlower : ∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x)
    (hleft : ∀ θ, Y (l, θ) = l) (hright : ∀ θ, Y (r, θ) = r)
    (hmiddle : ∀ x ∈ Icc c d, ∀ θ, Y (x, θ) = x)
    (hcapL : l ≠ D.a → c - l ≤ Statements.endpointDistance D l / 2)
    (hcapR : r ≠ D.b → r - d ≤ Statements.endpointDistance D r / 2)
    (hambientL : l = D.a → ∀ x ∈ Icc l c, ∀ θ, Y (x, θ) = x)
    (hambientR : r = D.b → ∀ x ∈ Icc d r, ∀ θ, Y (x, θ) = x) :
    ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      (positiveFiberChart φ Y p).1 ∈ Ioo D.a D.b ∧
      |endpointX 1 (Statements.endpointDistance D (positiveFiberChart φ Y p).1) -
        endpointX 1 (Statements.endpointDistance D p.1)| ≤ 2 := by
  have hlr : l < r := hlc.trans (hcd.trans hdr)
  have hc (θ : ℝ) : Y (c, θ) = c := hmiddle c ⟨le_rfl, hcd.le⟩ θ
  have hd (θ : ℝ) : Y (d, θ) = d := hmiddle d ⟨hcd.le, le_rfl⟩ θ
  have hmapL : MapsTo (positiveFiberChart φ Y)
      (Icc l c ×ˢ (univ : Set ℝ)) (Icc l c ×ˢ (univ : Set ℝ)) :=
    (positiveFiberChart_maps_closedStrip hY hB hlower hleft hc).1
  have hmapR : MapsTo (positiveFiberChart φ Y)
      (Icc d r ×ˢ (univ : Set ℝ)) (Icc d r ×ˢ (univ : Set ℝ)) :=
    (positiveFiberChart_maps_closedStrip hY hB hlower hd hright).1
  intro p hp
  have hpCore : p.1 ∈ Ioo D.a D.b :=
    ⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩
  by_cases hpl : p.1 < c
  · have hpc : p.1 ∈ Icc l c := ⟨hp.1.1.le, hpl.le⟩
    have hqc : (positiveFiberChart φ Y p).1 ∈ Icc l c :=
      (hmapL (x := p) ⟨hpc, mem_univ _⟩).1
    by_cases hl : l = D.a
    · have he : (positiveFiberChart φ Y p).1 = p.1 :=
        hambientL hl p.1 hpc (φ p)
      rw [he]
      exact ⟨hpCore, by norm_num⟩
    · have hlCore : l ∈ Ioo D.a D.b :=
        ⟨lt_of_le_of_ne ha hl.symm, hlr.trans_le hb⟩
      have hpdist : |p.1 - l| ≤ Statements.endpointDistance D l / 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hpc.1)]
        exact (sub_le_sub_right hpc.2 l).trans (hcapL hl)
      have hqdist : |(positiveFiberChart φ Y p).1 - l| ≤
          Statements.endpointDistance D l / 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hqc.1)]
        exact (sub_le_sub_right hqc.2 l).trans (hcapL hl)
      exact ⟨(endpointDistance_half_collar_bounds hlCore hqdist).1,
        endpointX_one_shift_on_half_distance_collar hlCore hqdist hpdist⟩
  by_cases hpr : d < p.1
  · have hpc : p.1 ∈ Icc d r := ⟨hpr.le, hp.1.2.le⟩
    have hqc : (positiveFiberChart φ Y p).1 ∈ Icc d r :=
      (hmapR (x := p) ⟨hpc, mem_univ _⟩).1
    by_cases hr : r = D.b
    · have he : (positiveFiberChart φ Y p).1 = p.1 :=
        hambientR hr p.1 hpc (φ p)
      rw [he]
      exact ⟨hpCore, by norm_num⟩
    · have hrCore : r ∈ Ioo D.a D.b :=
        ⟨ha.trans_lt hlr, lt_of_le_of_ne hb hr⟩
      have hpdist : |p.1 - r| ≤ Statements.endpointDistance D r / 2 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hpc.2)]
        exact (sub_le_sub_left hpc.1 r).trans (hcapR hr)
      have hqdist : |(positiveFiberChart φ Y p).1 - r| ≤
          Statements.endpointDistance D r / 2 := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hqc.2)]
        exact (sub_le_sub_left hqc.1 r).trans (hcapR hr)
      exact ⟨(endpointDistance_half_collar_bounds hrCore hqdist).1,
        endpointX_one_shift_on_half_distance_collar hrCore hqdist hpdist⟩
  have hmid : p.1 ∈ Icc c d := ⟨le_of_not_gt hpl, le_of_not_gt hpr⟩
  have he : (positiveFiberChart φ Y p).1 = p.1 := hmiddle p.1 hmid (φ p)
  rw [he]
  exact ⟨hpCore, by norm_num⟩

/-- The exits are actual explicit functions of the component endpoints.
All numerical weight constants precede the component and scalar family.
The ambient identities are raw scalar identities, supplied separately
by the actual endpoint identity data. -/
theorem positiveFiberChart_material_ratios_for_exit_choice
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧
      ∀ l r (φ Y : PolarPoint → ℝ) (B : ℝ),
      let c := positiveMaterialLeftExit D l r
      let d := positiveMaterialRightExit D l r
      D.a ≤ l → l < r → r ≤ D.b →
      ContDiff ℝ ∞ Y → 0 < B →
      (∀ x θ, B ≤ deriv (fun t => Y (t, θ)) x) →
      (∀ θ, Y (l, θ) = l) → (∀ θ, Y (r, θ) = r) →
      (∀ x ∈ Icc c d, ∀ θ, Y (x, θ) = x) →
      (l = D.a → ∀ x ∈ Icc l c, ∀ θ, Y (x, θ) = x) →
      (r = D.b → ∀ x ∈ Icc d r, ∀ θ, Y (x, θ) = x) →
      ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      T.H (positiveFiberChart φ Y p).1 / T.H p.1 ≤ K * T.E0 p.1 ^ A ∧
        T.M (positiveFiberChart φ Y p).1 / T.M p.1 ≤ K * T.E0 p.1 ^ A := by
  obtain ⟨K, A, hK, hA, hweights⟩ :=
    material_H_M_ratios_of_bounded_endpointX_shift hT hRef (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨K, A, hK, hA, ?_⟩
  intro l r φ Y B
  dsimp only
  intro ha hlr hb hY hB hlower hleft hright hmiddle hambientL hambientR p hp
  obtain ⟨hlc, hcd, hdr, hcapL, hcapR⟩ := positiveMaterialExits_spec ha hlr hb
  have hpoint := positiveFiberChart_endpointX_shift_of_capped_exits
    (φ := φ) ha hlc hcd hdr hb hY hB hlower hleft hright hmiddle
      hcapL hcapR hambientL hambientR p hp
  exact hweights (positiveFiberChart φ Y p).1 p.1 hpoint.1
    ⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩ hpoint.2

end ContinuousFlexibility.Analysis
