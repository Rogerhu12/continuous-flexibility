import ContinuousFlexibility.Analysis.EndpointTransportGeometry
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual middle circles prevent transport between the two collars

A continuous injective map fixing a vertical line cannot cross that line
along a radial segment whose endpoint remains on its original side.
One signed lemma treats both sides. Applied to the existing whole-component
geometry, it preserves the original transport and every matching jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

private theorem fixed_vertical_line_preserves_signed_side
    {τ : PolarPoint → PolarPoint} {a b v : ℝ}
    (hτ : Continuous τ) (hinj : Function.Injective τ) (hv : v ≠ 0)
    (ha : v * (a - b) < 0)
    (hanchor : ∀ θ, (τ (a, θ)).1 = a)
    (hfixed : ∀ θ, τ (b, θ) = (b, θ))
    (p : PolarPoint) (hp : v * (p.1 - b) ≤ 0) :
    v * ((τ p).1 - b) ≤ 0 := by
  by_cases hpb : p.1 = b
  · have he : p = (b, p.2) := Prod.ext hpb rfl
    rw [he, hfixed]
    simp only [sub_self, mul_zero, le_refl]
  have hpx : v * (p.1 - b) < 0 := by
    by_contra hn
    have he : v * (p.1 - b) = 0 := le_antisymm hp (le_of_not_gt hn)
    exact hpb (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hv))
  by_contra hbad
  have hbad' : 0 < v * ((τ p).1 - b) := lt_of_not_ge hbad
  let γ : ℝ → PolarPoint := fun t => ((1 - t) * a + t * p.1, p.2)
  let f : ℝ → ℝ := fun t => v * ((τ (γ t)).1 - b)
  have hγ : Continuous γ :=
    (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).prodMk continuous_const
  have hf : Continuous f :=
    continuous_const.mul ((hτ.comp hγ).fst.sub continuous_const)
  have hf0 : f 0 < 0 := by
    simpa only [f, γ, sub_zero, one_mul, zero_mul, add_zero, hanchor] using ha
  have hf1 : 0 < f 1 := by
    simpa only [f, γ, sub_self, zero_mul, one_mul, zero_add, Prod.eta] using hbad'
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc
    (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn ⟨hf0.le, hf1.le⟩
  have hradial : (τ (γ t)).1 = b :=
    sub_eq_zero.mp ((mul_eq_zero.mp hft).resolve_left hv)
  have himage : τ (γ t) = τ (b, (τ (γ t)).2) := by
    rw [hfixed]
    exact Prod.ext hradial rfl
  have hpoint : (1 - t) * a + t * p.1 = b :=
    congrArg Prod.fst (hinj himage)
  have hmix : (1 - t) * (v * (a - b)) + t * (v * (p.1 - b)) < 0 := by
    rcases lt_or_eq_of_le ht.2 with ht1 | ht1
    · exact add_neg_of_neg_of_nonpos
        (mul_neg_of_pos_of_neg (sub_pos.mpr ht1) ha)
        (mul_nonpos_of_nonneg_of_nonpos ht.1 hpx.le)
    · simpa only [ht1, sub_self, zero_mul, one_mul, zero_add] using hpx
  have hstrict : v * ((1 - t) * a + t * p.1 - b) < 0 := by
    calc
      v * ((1 - t) * a + t * p.1 - b) =
          (1 - t) * (v * (a - b)) + t * (v * (p.1 - b)) := by ring
      _ < 0 := hmix
  rw [hpoint, sub_self, mul_zero] at hstrict
  exact (lt_irrefl (0 : ℝ)) hstrict

theorem WholeComponentTransportGeometry.maps_capped_collars
    {τ σ : PolarPoint → PolarPoint} {l r c d J : ℝ}
    (h : WholeComponentTransportGeometry τ σ l r c d J)
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hroot : ∀ side θ, (τ (if side then r else l, θ)).1 = if side then r else l) :
    MapsTo τ (Icc l c ×ˢ (univ : Set ℝ)) (Icc l c ×ˢ (univ : Set ℝ)) ∧
      MapsTo τ (Icc d r ×ˢ (univ : Set ℝ)) (Icc d r ×ˢ (univ : Set ℝ)) := by
  have hc (θ : ℝ) : τ (c, θ) = (c, θ) :=
    (h.middle_germ c ⟨le_rfl, hcd.le⟩ θ).self_of_nhds
  have hd (θ : ℝ) : τ (d, θ) = (d, θ) :=
    (h.middle_germ d ⟨hcd.le, le_rfl⟩ θ).self_of_nhds
  constructor
  · intro p hp
    have hin : p ∈ Icc l r ×ˢ (univ : Set ℝ) :=
      ⟨⟨hp.1.1, hp.1.2.trans (hcd.le.trans hdr.le)⟩, hp.2⟩
    have hside := fixed_vertical_line_preserves_signed_side
      (τ := τ) (a := l) (b := c) (v := 1)
      h.smooth.continuous h.left_inverse.injective one_ne_zero
      (by linarith) (hroot false) hc p (by linarith only [hp.1.2])
    exact ⟨⟨(h.maps_closed (x := p) hin).1.1, by linarith only [hside]⟩, mem_univ _⟩
  · intro p hp
    have hin : p ∈ Icc l r ×ˢ (univ : Set ℝ) :=
      ⟨⟨(hlc.le.trans hcd.le).trans hp.1.1, hp.1.2⟩, hp.2⟩
    have hside := fixed_vertical_line_preserves_signed_side
      (τ := τ) (a := r) (b := d) (v := -1)
      h.smooth.continuous h.left_inverse.injective (by norm_num)
      (by linarith) (hroot true) hd p (by linarith only [hp.1.1])
    exact ⟨⟨by linarith only [hside], (h.maps_closed (x := p) hin).1.2⟩, mem_univ _⟩

end ContinuousFlexibility.Analysis
