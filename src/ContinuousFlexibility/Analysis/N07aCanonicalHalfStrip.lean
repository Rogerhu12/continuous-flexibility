module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual reflected canonical chart preserves a fundamental half strip

Reflection fixes the two angular boundary lines, and injectivity prevents
an interior point from crossing either one. The intermediate value theorem
therefore identifies the actual image of `0 < θ ≤ π`. This is the geometric
step needed to use ordinary plane change of variables for rough functions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem n07a_angle_Ioc_mapsTo {g : ℝ → ℝ} (hg : Continuous g)
    (h0 : g 0 = 0) (hpi : g Real.pi = Real.pi)
    (hz : ∀ t, g t = 0 → t = 0) (hp : ∀ t, g t = Real.pi → t = Real.pi) :
    MapsTo g (Ioc (0 : ℝ) Real.pi) (Ioc (0 : ℝ) Real.pi) := by
  intro θ hθ
  constructor
  · by_contra h
    have hlow : g θ ≤ 0 := le_of_not_gt h
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hθ.2 hg.continuousOn
      (show (0 : ℝ) ∈ Icc (g θ) (g Real.pi) by rw [hpi]; exact ⟨hlow, Real.pi_pos.le⟩)
    have ht0 := hz t hgt
    linarith [ht.1, hθ.1]
  · by_contra h
    have hhigh : Real.pi < g θ := lt_of_not_ge h
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hθ.1.le hg.continuousOn
      (show Real.pi ∈ Icc (g 0) (g θ) by rw [h0]; exact ⟨Real.pi_pos.le, hhigh.le⟩)
    have htpi := hp t hgt
    have hθpi : θ = Real.pi := by linarith [ht.2, hθ.2]
    rw [hθpi, hpi] at hhigh
    exact (lt_irrefl _ hhigh)

private theorem n07a_strip_reflection_zero {a b : ℝ} {F : PolarPoint → PolarPoint}
    (hR : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    {r : ℝ} (hr : r ∈ Ioo a b) : (F (r, 0)).2 = 0 := by
  have h := congrArg Prod.snd (hR (r, 0) ⟨hr, mem_univ _⟩)
  simp only [neg_zero] at h
  linarith

private theorem n07a_strip_reflection_pi {a b : ℝ} {F : PolarPoint → PolarPoint}
    (hR : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    (hP : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, Real.pi)) = F p + (0, Real.pi))
    {r : ℝ} (hr : r ∈ Ioo a b) : (F (r, Real.pi)).2 = Real.pi := by
  have h := congrArg Prod.snd (hP (r, 0) ⟨hr, mem_univ _⟩)
  simpa only [Prod.mk_add_mk, Prod.snd_add, add_zero, zero_add,
    n07a_strip_reflection_zero hR hr] using h

/-- The inverse inherits the actual period equivariance from the chart. -/
theorem n07a_strip_inverse_periodic {a b c d : ℝ} {F G : PolarPoint → PolarPoint}
    (hG : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hFG : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), F (G p) = p)
    (hP : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, Real.pi)) = F p + (0, Real.pi)) :
    ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p + (0, Real.pi)) = G p + (0, Real.pi) := by
  intro p hp
  have hgp := hG hp
  have hshift : G p + (0, Real.pi) ∈ Ioo a b ×ˢ (univ : Set ℝ) := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hgp.1, mem_univ _⟩
  have he := hP (G p) hgp
  rw [hFG p hp] at he
  rw [← he]
  exact hGF _ hshift

private theorem n07a_strip_row_continuous {a b : ℝ} {F : PolarPoint → PolarPoint}
    (hF : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    {r : ℝ} (hr : r ∈ Ioo a b) : Continuous (fun θ : ℝ => (F (r, θ)).2) := by
  exact (hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hr, mem_univ _⟩)).snd

private theorem n07a_strip_forward_half {a b c d : ℝ} {F G : PolarPoint → PolarPoint}
    (hF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hGF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hFs : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hFR : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    (hGR : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p.1, -p.2) = ((G p).1, -(G p).2))
    (hFP : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, Real.pi)) = F p + (0, Real.pi))
    (hGP : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p + (0, Real.pi)) = G p + (0, Real.pi)) :
    MapsTo F (Ioo a b ×ˢ Ioc (0 : ℝ) Real.pi) (Ioo c d ×ˢ Ioc (0 : ℝ) Real.pi) := by
  intro p hp
  have hpin : p ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
  refine ⟨(hF hpin).1, ?_⟩
  apply n07a_angle_Ioc_mapsTo (n07a_strip_row_continuous hFs hp.1)
    (n07a_strip_reflection_zero hFR hp.1) (n07a_strip_reflection_pi hFR hFP hp.1)
    (fun θ hθ => ?_) (fun θ hθ => ?_) hp.2
  · have hs : (p.1, θ) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
    have ht := hF hs
    have he : F (p.1, θ) = ((F (p.1, θ)).1, 0) := Prod.ext rfl hθ
    calc
      θ = (G (F (p.1, θ))).2 := (congrArg Prod.snd (hGF _ hs)).symm
      _ = (G ((F (p.1, θ)).1, 0)).2 := congrArg (fun q => (G q).2) he
      _ = 0 := n07a_strip_reflection_zero hGR ht.1
  · have hs : (p.1, θ) ∈ Ioo a b ×ˢ (univ : Set ℝ) := ⟨hp.1, mem_univ _⟩
    have ht := hF hs
    have he : F (p.1, θ) = ((F (p.1, θ)).1, Real.pi) := Prod.ext rfl hθ
    calc
      θ = (G (F (p.1, θ))).2 := (congrArg Prod.snd (hGF _ hs)).symm
      _ = (G ((F (p.1, θ)).1, Real.pi)).2 := congrArg (fun q => (G q).2) he
      _ = Real.pi := n07a_strip_reflection_pi hGR hGP ht.1

/-- Exact fundamental-domain image of a genuine reflected periodic strip
diffeomorphism. The assumptions are pointwise geometric identities. -/
theorem n07a_strip_image_half {a b c d : ℝ} {F G : PolarPoint → PolarPoint}
    (hF : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hG : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGF : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hFG : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), F (G p) = p)
    (hFs : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ (univ : Set ℝ)))
    (hGs : ContDiffOn ℝ ∞ G (Ioo c d ×ˢ (univ : Set ℝ)))
    (hFR : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p.1, -p.2) = ((F p).1, -(F p).2))
    (hGR : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p.1, -p.2) = ((G p).1, -(G p).2))
    (hFP : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), F (p + (0, Real.pi)) = F p + (0, Real.pi)) :
    F '' (Ioo a b ×ˢ Ioc (0 : ℝ) Real.pi) = Ioo c d ×ˢ Ioc (0 : ℝ) Real.pi := by
  have hGP := n07a_strip_inverse_periodic hG hGF hFG hFP
  have hf := n07a_strip_forward_half hF hGF hFs hFR hGR hFP hGP
  have hg := n07a_strip_forward_half hG hFG hGs hGR hFR hGP hFP
  apply Subset.antisymm (image_subset_iff.mpr hf)
  intro p hp
  exact ⟨G p, hg hp, hFG p ⟨hp.1, mem_univ _⟩⟩

end ContinuousFlexibility.Analysis
