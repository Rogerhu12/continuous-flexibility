import Mathlib.Analysis.Calculus.MeanValue

/-!
# Joint continuity of the actual geometric inverse

The parameter retains its given topology. A common spatial Lipschitz
bound and the actual inverse identities turn continuity of the forward
map into continuity of its chosen inverse. The forward map need not send
the whole fixed physical domain into the canonical target strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology NNReal

section MetricInverse

variable {P X Y : Type*} [TopologicalSpace P]
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {U : Set P} {V : Set X} {W : Set Y}
  {F : P × X → Y} {G : P × Y → X}

/-- Uniform spatial inverse stability gives joint continuity in the
original parameter topology, without assuming continuity of the inverse. -/
theorem n04NegativeGeometry_inverse_continuousOn_of_lipschitz
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hF : ContinuousOn F (U ×ˢ V))
    (hInj : ∀ p ∈ U, InjOn (fun x => F (p, x)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ q ∈ U ×ˢ W, F (q.1, G q) = q.2)
    (K : ℝ≥0) (hLip : ∀ p ∈ U, LipschitzOnWith K (fun y => G (p, y)) W) :
    ContinuousOn G (U ×ˢ W) := by
  intro q hq
  have hGq : G q ∈ V := hMaps hq
  have hforward : ContinuousAt (fun z : P × Y => F (z.1, G q)) q :=
    (hF.continuousAt ((hU.prod hV).mem_nhds ⟨hq.1, hGq⟩)).comp
      (continuousAt_fst.prodMk continuousAt_const)
  have htarget : ∀ᶠ z : P × Y in 𝓝 q, F (z.1, G q) ∈ W :=
    hforward.tendsto.eventually (by rw [hRight q hq]; exact hW.mem_nhds hq.2)
  have hdist : Tendsto (fun z : P × Y => dist z.2 (F (z.1, G q))) (𝓝 q) (𝓝 0) := by
    simpa only [hRight q hq, dist_self] using (continuousAt_snd.dist hforward).tendsto
  have hbound : ∀ᶠ z : P × Y in 𝓝 q,
      dist (G z) (G q) ≤ (K : ℝ) * dist z.2 (F (z.1, G q)) := by
    filter_upwards [(hU.prod hW).mem_nhds hq, htarget] with z hz htz
    have hleft : G (z.1, F (z.1, G q)) = G q := by
      apply hInj z.1 hz.1 (hMaps ⟨hz.1, htz⟩) hGq
      exact hRight (z.1, F (z.1, G q)) ⟨hz.1, htz⟩
    simpa only [hleft] using (hLip z.1 hz.1).dist_le_mul hz.2 htz
  have hlim : Tendsto (fun z : P × Y => (K : ℝ) * dist z.2 (F (z.1, G q)))
      (𝓝 q) (𝓝 0) := by
    simpa only [mul_zero] using hdist.const_mul (K : ℝ)
  have hcont : ContinuousAt G q :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound hlim)
  exact hcont.continuousWithinAt

end MetricInverse

section OrderedInverse

variable {P : Type*} [TopologicalSpace P]
  {U : Set P} {V : Set ℝ} {a b : ℝ} {F G : P × ℝ → ℝ}

/-- Trapping between two fixed interior radii gives joint continuity
of the actual inverse of a strictly increasing interval family. Neither
the parameter space nor the inverse family needs a norm or a derivative. -/
theorem n04NegativeGeometry_intervalInverse_continuousOn
    (hF : ContinuousOn F (U ×ˢ Ioo a b))
    (hMono : ∀ p ∈ U, StrictMonoOn (fun r => F (p, r)) (Ioo a b))
    (hMaps : MapsTo G (U ×ˢ V) (Ioo a b))
    (hRight : ∀ q ∈ U ×ˢ V, F (q.1, G q) = q.2) :
    ContinuousOn G (U ×ˢ V) := by
  have hfixed (r : ℝ) (hr : r ∈ Ioo a b) :
      ContinuousOn (fun q : P × ℝ => F (q.1, r)) (U ×ˢ V) :=
    hF.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq.1, hr⟩)
  intro q hq
  have hGq := hMaps hq
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let l : ℝ := (max a r + G q) / 2
    have hlG : l < G q := by
      have hmax : max a r < G q := max_lt_iff.mpr ⟨hGq.1, hr⟩
      dsimp only [l]
      linarith
    have hal : a < l := by
      have hamax := le_max_left a r
      dsimp only [l]
      linarith
    have hrl : r < l := by
      have hrmax := le_max_right a r
      dsimp only [l]
      linarith
    have hl : l ∈ Ioo a b := ⟨hal, hlG.trans hGq.2⟩
    have hlt : F (q.1, l) < q.2 := by
      rw [← hRight q hq]
      exact hMono q.1 hq.1 hl hGq hlG
    have he : ∀ᶠ z in 𝓝[U ×ˢ V] q, F (z.1, l) < z.2 :=
      Filter.Tendsto.eventually_lt (hfixed l hl q hq)
        continuous_snd.continuousWithinAt hlt
    filter_upwards [self_mem_nhdsWithin, he] with z hz hzt
    apply hrl.trans
    by_contra hn
    have hh := (hMono z.1 hz.1).monotoneOn (hMaps hz) hl (le_of_not_gt hn)
    rw [hRight z hz] at hh
    exact (not_le_of_gt hzt) hh
  · intro r hr
    let u : ℝ := (G q + min b r) / 2
    have hGu : G q < u := by
      have hmin : G q < min b r := lt_min hGq.2 hr
      dsimp only [u]
      linarith
    have hub : u < b := by
      have hminb := min_le_left b r
      dsimp only [u]
      linarith
    have hur : u < r := by
      have hminr := min_le_right b r
      dsimp only [u]
      linarith
    have hu : u ∈ Ioo a b := ⟨hGq.1.trans hGu, hub⟩
    have hlt : q.2 < F (q.1, u) := by
      rw [← hRight q hq]
      exact hMono q.1 hq.1 hGq hu hGu
    have he : ∀ᶠ z in 𝓝[U ×ˢ V] q, z.2 < F (z.1, u) :=
      Filter.Tendsto.eventually_lt continuous_snd.continuousWithinAt
        (hfixed u hu q hq) hlt
    filter_upwards [self_mem_nhdsWithin, he] with z hz hzt
    apply lt_trans ?_ hur
    by_contra hn
    have hh := (hMono z.1 hz.1).monotoneOn hu (hMaps hz) (le_of_not_gt hn)
    rw [hRight z hz] at hh
    exact (not_le_of_gt hzt) hh

end OrderedInverse

section DifferentiableInverse

variable {P X Y : Type*} [TopologicalSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set P} {V : Set X} {W : Set Y}
  {F : P × X → Y} {G : P × Y → X}

/-- A common spatial derivative bound on the convex target supplies
the inverse stability needed above. Only spatial inverse derivatives
appear in the hypotheses; parameter continuity is a conclusion. -/
theorem n04NegativeGeometry_inverse_continuousOn_of_spatial_derivative
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hconv : Convex ℝ W)
    (hF : ContinuousOn F (U ×ˢ V))
    (hInj : ∀ p ∈ U, InjOn (fun x => F (p, x)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ q ∈ U ×ˢ W, F (q.1, G q) = q.2)
    (K : ℝ≥0)
    (hDiff : ∀ p ∈ U, ∀ y ∈ W, DifferentiableAt ℝ (fun t => G (p, t)) y)
    (hbound : ∀ p ∈ U, ∀ y ∈ W, ‖fderiv ℝ (fun t => G (p, t)) y‖ ≤ (K : ℝ)) :
    ContinuousOn G (U ×ˢ W) := by
  apply n04NegativeGeometry_inverse_continuousOn_of_lipschitz
    hU hV hW hF hInj hMaps hRight K
  intro p hp
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le (hDiff p hp)
    (fun y hy => by exact_mod_cast hbound p hp y hy) hconv

end DifferentiableInverse

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_inverse_continuousOn_of_spatial_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_inverse_continuousOn_of_spatial_derivative
