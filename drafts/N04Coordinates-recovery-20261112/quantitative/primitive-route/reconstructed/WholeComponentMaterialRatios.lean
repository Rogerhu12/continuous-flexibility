import ContinuousFlexibility.Analysis.WholeComponentCollarInvariance
import ContinuousFlexibility.Analysis.EndpointDistanceMaterialTransport

/-!
# Material ratios for an already constructed whole-component transport

The exits remain arbitrary, so a separate normalization buffer can shrink
the two active collars. The same actual transport is used throughout.
One side argument handles both endpoints, and no material cell containing
the positive component is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

theorem wholeComponentTransport_material_ratios_of_capped_collars
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧
      ∀ {τ σ : PolarPoint → PolarPoint} {l r c d J : ℝ},
      D.a ≤ l → l < c → c < d → d < r → r ≤ D.b →
      WholeComponentTransportGeometry τ σ l r c d J →
      (∀ side θ, (τ (if side then r else l, θ)).1 = if side then r else l) →
      (l ≠ D.a → c - l ≤ Statements.endpointDistance D l / 2) →
      (r ≠ D.b → r - d ≤ Statements.endpointDistance D r / 2) →
      (∀ side, (if side then r else l) = (if side then D.b else D.a) →
        ∀ p ∈ Icc (if side then d else l) (if side then r else c) ×ˢ (univ : Set ℝ),
          (τ p).1 = p.1) →
      ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
        T.H (τ p).1 / T.H p.1 ≤ K * T.E0 p.1 ^ A ∧
          T.M (τ p).1 / T.M p.1 ≤ K * T.E0 p.1 ^ A := by
  obtain ⟨K, A, hK, hA, hweights⟩ :=
    material_H_M_ratios_on_endpointDistance_collar hT hRef
  refine ⟨K, A, hK, hA, ?_⟩
  intro τ σ l r c d J ha hlc hcd hdr hb hgeometry hroot hcapL hcapR hambient
  have hlr : l < r := hlc.trans (hcd.trans hdr)
  have hmaps := hgeometry.maps_capped_collars hlc hcd hdr hroot
  have hidentity (p : PolarPoint) (hp : p.1 ∈ Ioo D.a D.b)
      (he : (τ p).1 = p.1) :
      T.H (τ p).1 / T.H p.1 ≤ K * T.E0 p.1 ^ A ∧
        T.M (τ p).1 / T.M p.1 ≤ K * T.E0 p.1 ^ A := by
    have hd : 0 < Statements.endpointDistance D p.1 :=
      lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2)
    have hz : |p.1 - p.1| ≤ Statements.endpointDistance D p.1 / 2 := by
      rw [sub_self, abs_zero]
      exact (half_pos hd).le
    rw [he]
    exact hweights p.1 p.1 p.1 hp hz hz
  have hside (side : Bool) (p : PolarPoint) (hpCore : p.1 ∈ Ioo D.a D.b)
      (hp : p ∈ Icc (if side then d else l) (if side then r else c) ×ˢ (univ : Set ℝ)) :
      T.H (τ p).1 / T.H p.1 ≤ K * T.E0 p.1 ^ A ∧
        T.M (τ p).1 / T.M p.1 ≤ K * T.E0 p.1 ^ A := by
    by_cases he : (if side then r else l) = (if side then D.b else D.a)
    · exact hidentity p hpCore (hambient side he p hp)
    have hc : (if side then r else l) ∈ Ioo D.a D.b := by
      cases side with
      | false => exact ⟨lt_of_le_of_ne ha he.symm, hlr.trans_le hb⟩
      | true => exact ⟨ha.trans_lt hlr, lt_of_le_of_ne hb he⟩
    have hanchor : (if side then r else l) ∈
        Icc (if side then d else l) (if side then r else c) := by
      cases side with
      | false => exact ⟨le_rfl, hlc.le⟩
      | true => exact ⟨hdr.le, le_rfl⟩
    have hcap : (if side then r else c) - (if side then d else l) ≤
        Statements.endpointDistance D (if side then r else l) / 2 := by
      cases side with
      | false => exact hcapL he
      | true => exact hcapR he
    have hdist (x : ℝ)
        (hx : x ∈ Icc (if side then d else l) (if side then r else c)) :
        |x - (if side then r else l)| ≤
          Statements.endpointDistance D (if side then r else l) / 2 := by
      apply le_trans (b := (if side then r else c) - (if side then d else l)) _ hcap
      exact abs_le.mpr ⟨by linarith only [hx.1, hanchor.2],
        by linarith only [hx.2, hanchor.1]⟩
    have hmap : MapsTo τ
        (Icc (if side then d else l) (if side then r else c) ×ˢ (univ : Set ℝ))
        (Icc (if side then d else l) (if side then r else c) ×ˢ (univ : Set ℝ)) := by
      cases side with
      | false => exact hmaps.1
      | true => exact hmaps.2
    exact hweights (if side then r else l) (τ p).1 p.1 hc
      (hdist _ (hmap (x := p) hp).1) (hdist _ hp.1)
  intro p hp
  have hpCore : p.1 ∈ Ioo D.a D.b :=
    ⟨ha.trans_lt hp.1.1, hp.1.2.trans_le hb⟩
  by_cases hpl : p.1 < c
  · exact hside false p hpCore ⟨⟨hp.1.1.le, hpl.le⟩, mem_univ _⟩
  by_cases hpr : d < p.1
  · exact hside true p hpCore ⟨⟨hpr.le, hp.1.2.le⟩, mem_univ _⟩
  have hmid : p.1 ∈ Icc c d := ⟨le_of_not_gt hpl, le_of_not_gt hpr⟩
  have he : τ p = p := by
    simpa only [Prod.eta, id_eq] using
      (hgeometry.middle_germ p.1 hmid p.2).self_of_nhds
  exact hidentity p hpCore (congrArg Prod.fst he)

end ContinuousFlexibility.Analysis
