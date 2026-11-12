import ContinuousFlexibility.Analysis.WholePositiveCanonicalFields

/-!
# The invariant buffered core between identity ambient collars

Injectivity alone prevents a map fixed on one closed half-plane from
mapping its opposite half-plane into the fixed interior. This gives the
actual buffered core for a positive component, shortening only an ambient
end. All other points lie in a genuine identity germ of the same fields.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

theorem injective_fixed_halfPlane_preserves_opposite
    {τ : PolarPoint → PolarPoint} (hinj : Function.Injective τ)
    (side : Bool) (c : ℝ)
    (hfix : ∀ p : PolarPoint, (if side then c ≤ p.1 else p.1 ≤ c) → τ p = p)
    {p : PolarPoint} (hp : if side then p.1 ≤ c else c ≤ p.1) :
    if side then (τ p).1 ≤ c else c ≤ (τ p).1 := by
  by_contra hn
  have hside : if side then c ≤ (τ p).1 else (τ p).1 ≤ c := by
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢ <;>
      exact (lt_of_not_ge hn).le
  have he : τ p = p := hinj (hfix (τ p) hside)
  exact hn (by simpa only [he] using hp)

theorem identityFields_germ_of_halfPlane
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ}
    (side : Bool) (c : ℝ)
    (hfix : ∀ q : PolarPoint, (if side then c ≤ q.1 else q.1 ≤ c) →
      τ q = q ∧ σ q = q ∧ Q q = 1)
    {p : PolarPoint} (hp : if side then c < p.1 else p.1 < c) :
    τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) ∧
      σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) ∧
      Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p,
      if side then c < q.1 else q.1 < c := by
    cases side
    · exact (continuous_fst.tendsto p).eventually (Iio_mem_nhds hp)
    · exact (continuous_fst.tendsto p).eventually (Ioi_mem_nhds hp)
  have hall : ∀ᶠ q : PolarPoint in 𝓝 p, τ q = q ∧ σ q = q ∧ Q q = 1 := by
    filter_upwards [hnear] with q hq
    apply hfix q
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq ⊢ <;> exact hq.le
  exact ⟨hall.mono (fun _ h => h.1), hall.mono (fun _ h => h.2.1),
    hall.mono (fun _ h => h.2.2)⟩

theorem exists_wholePositive_ambient_buffer
    {τ σ : PolarPoint → PolarPoint} {Q : PolarPoint → ℝ}
    {a l c d r b : ℝ}
    (hal : a ≤ l) (hlc : l < c) (hcd : c < d) (hdr : d < r) (hrb : r ≤ b)
    (hinj : Function.Injective τ)
    (hmap : MapsTo τ (Icc l r ×ˢ (univ : Set ℝ))
      (Icc l r ×ˢ (univ : Set ℝ)))
    (hambient : ∀ side : Bool,
      (if side then r else l) = (if side then b else a) →
      ∀ p : PolarPoint, (if side then d ≤ p.1 else p.1 ≤ c) →
        τ p = p ∧ σ p = p ∧ Q p = 1) :
    ∃ u v : ℝ, a < u ∧ u ≤ v ∧ v < b ∧
      MapsTo τ (Icc u v ×ˢ (univ : Set ℝ)) (Icc u v ×ˢ (univ : Set ℝ)) ∧
      (∀ side : Bool, (if side then r else l) ≠ (if side then b else a) →
        (if side then r else l) ∈ Icc u v) ∧
      ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ), p.1 ∉ Icc u v →
        τ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) ∧
        σ =ᶠ[𝓝 p] (id : PolarPoint → PolarPoint) ∧
        Q =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
  let u : ℝ := if l = a then c else l
  let v : ℝ := if r = b then d else r
  have hlu : l ≤ u := by
    by_cases h : l = a
    · simpa only [u, if_pos h] using hlc.le
    · simpa only [u, if_neg h] using (le_refl l)
  have huc : u ≤ c := by
    by_cases h : l = a
    · simpa only [u, if_pos h] using (le_refl c)
    · simpa only [u, if_neg h] using hlc.le
  have hdv : d ≤ v := by
    by_cases h : r = b
    · simpa only [v, if_pos h] using (le_refl d)
    · simpa only [v, if_neg h] using hdr.le
  have hvr : v ≤ r := by
    by_cases h : r = b
    · simpa only [v, if_pos h] using hdr.le
    · simpa only [v, if_neg h] using (le_refl r)
  have hau : a < u := by
    by_cases h : l = a
    · simpa only [u, h, ↓reduceIte] using hal.trans_lt hlc
    · simpa only [u, h, ↓reduceIte] using lt_of_le_of_ne hal (Ne.symm h)
  have huv : u ≤ v := huc.trans (hcd.le.trans hdv)
  have hvb : v < b := by
    by_cases h : r = b
    · simpa only [v, h, ↓reduceIte] using hdr.trans_le hrb
    · simpa only [v, h, ↓reduceIte] using lt_of_le_of_ne hrb h
  refine ⟨u, v, hau, huv, hvb, ?_, ?_, ?_⟩
  · intro p hp
    have hpwhole : p ∈ Icc l r ×ˢ (univ : Set ℝ) :=
      ⟨⟨hlu.trans hp.1.1, hp.1.2.trans hvr⟩, mem_univ _⟩
    have hwhole := hmap (x := p) hpwhole
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · by_cases h : l = a
      · have hc : c ≤ p.1 := by simpa only [u, h, ↓reduceIte] using hp.1.1
        have hf : ∀ q : PolarPoint, q.1 ≤ c → τ q = q :=
          fun q hq => (hambient false h q hq).1
        simpa only [u, h, ↓reduceIte] using
          injective_fixed_halfPlane_preserves_opposite hinj false c hf hc
      · simpa only [u, h, ↓reduceIte] using hwhole.1.1
    · by_cases h : r = b
      · have hd : p.1 ≤ d := by simpa only [v, h, ↓reduceIte] using hp.1.2
        have hf : ∀ q : PolarPoint, d ≤ q.1 → τ q = q :=
          fun q hq => (hambient true h q hq).1
        simpa only [v, h, ↓reduceIte] using
          injective_fixed_halfPlane_preserves_opposite hinj true d hf hd
      · simpa only [v, h, ↓reduceIte] using hwhole.1.2
  · intro side h
    cases side
    · change l ≠ a at h
      change l ∈ Icc u v
      have he : u = l := by simp only [u, h, ↓reduceIte]
      rw [← he]
      exact ⟨le_rfl, huv⟩
    · change r ≠ b at h
      change r ∈ Icc u v
      have he : v = r := by simp only [v, h, ↓reduceIte]
      rw [← he]
      exact ⟨huv, le_rfl⟩
  · intro p hp hnot
    by_cases hlow : p.1 < u
    · have h : l = a := by
        by_contra hn
        have he : u = l := by simp only [u, hn, ↓reduceIte]
        exact (not_lt_of_ge hp.1.1.le) (he ▸ hlow)
      have hc : p.1 < c := by simpa only [u, h, ↓reduceIte] using hlow
      exact identityFields_germ_of_halfPlane false c (hambient false h) hc
    · have hhigh : v < p.1 := lt_of_not_ge
        (fun hv => hnot ⟨le_of_not_gt hlow, hv⟩)
      have h : r = b := by
        by_contra hn
        have he : v = r := by simp only [v, hn, ↓reduceIte]
        exact (not_lt_of_ge hp.1.2.le) (he ▸ hhigh)
      have hd : d < p.1 := by simpa only [v, h, ↓reduceIte] using hhigh
      exact identityFields_germ_of_halfPlane true d (hambient true h) hd

end ContinuousFlexibility.Analysis
