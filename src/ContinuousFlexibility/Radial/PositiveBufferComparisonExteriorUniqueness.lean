import ContinuousFlexibility.Radial.PositiveBufferComparisonUniqueness
import ContinuousFlexibility.Radial.PositiveBufferComparisonDomains

/-!
# Exterior uniqueness at both physical buffer ends

The outward coordinate is the reflection of the existing normalized
inward coordinate. Ordinary derivatives at the cut transform with its
nonzero slope, so the physical conormal relation follows at either end.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem positiveBufferPoint_outward_hasDerivAt {B : BufferData} {i : Fin 2}
    {u : ℝ → ℝ} {r d : ℝ}
    (hu : HasDerivAt u d (positiveBufferPoint B i (-r))) :
    HasDerivAt (fun t => u (positiveBufferPoint B i (-t)))
      ((bufferSign i / B.mass i) * d) r := by
  have hd : HasDerivAt u d (bufferCut B i + (bufferSign i / B.mass i) * r) := by
    simpa only [← positiveBufferPoint_outward_affine] using hu
  simpa only [← positiveBufferPoint_outward_affine] using
    positiveBuffer_affine_hasDerivAt hd

theorem positiveBufferPoint_outward_classical {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ x ∈ bufferExterior B i,
      -deriv (deriv u) x + B.potential x * u x = 0) :
    ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s => u (positiveBufferPoint B i (-s)))
          ((bufferSign i / B.mass i) * deriv u (positiveBufferPoint B i (-t))) t ∧
      HasDerivAt (fun s => (bufferSign i / B.mass i) * deriv u (positiveBufferPoint B i (-s)))
        ((B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2) *
          u (positiveBufferPoint B i (-t))) t := by
  have hdu : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hu' : ∀ x ∈ bufferExterior B i, HasDerivAt u (deriv u x) x :=
    fun x _ => (hu.differentiable (by simp) x).hasDerivAt
  have hdu' : ∀ x ∈ bufferExterior B i, HasDerivAt (deriv u) (B.potential x * u x) x := by
    intro x hx
    have heq : deriv (deriv u) x = B.potential x * u x := by linarith [hODE x hx]
    rw [← heq]
    exact (hdu.differentiable (by simp) x).hasDerivAt
  intro t ht
  have hx : positiveBufferPoint B i (-t) ∈ bufferExterior B i := by
    change t ∈ (fun s : ℝ => positiveBufferPoint B i (-s)) ⁻¹' bufferExterior B i
    rw [positiveBufferPoint_outward_preimage_exterior hB i]
    exact ht
  have h := positiveBuffer_affine_homogeneous hu' hdu'
    (bufferCut B i) (bufferSign i / B.mass i) (t := t)
    (by simpa only [← positiveBufferPoint_outward_affine] using hx)
  simp only [← positiveBufferPoint_outward_affine, div_pow, bufferSign_sq] at h
  have hcoeff (x : ℝ) : (1 / B.mass i ^ 2) * B.potential x =
      B.potential x / B.mass i ^ 2 := by ring
  simpa only [hcoeff] using h

theorem positiveBuffer_exterior_proportional {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {u p : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p)
    (huODE : ∀ x ∈ bufferExterior B i, -deriv (deriv u) x + B.potential x * u x = 0)
    (hpODE : ∀ x ∈ bufferExterior B i, -deriv (deriv p) x + B.potential x * p x = 0)
    (hp0 : p (bufferCut B i) = 1) {Mu Mp : ℝ} (hMu : 0 ≤ Mu) (hMp : 0 ≤ Mp)
    (hub : ∀ x ∈ closure (bufferExterior B i), |u x| ≤ Mu)
    (hpb : ∀ x ∈ closure (bufferExterior B i), |p x| ≤ Mp) :
    EqOn u (fun x => u (bufferCut B i) * p x) (closure (bufferExterior B i)) ∧
      deriv u (bufferCut B i) = u (bufferCut B i) * deriv p (bufferCut B i) := by
  let v : ℝ → ℝ := fun t => u (positiveBufferPoint B i (-t))
  let dv : ℝ → ℝ := fun t => (bufferSign i / B.mass i) * deriv u (positiveBufferPoint B i (-t))
  let w : ℝ → ℝ := fun t => p (positiveBufferPoint B i (-t))
  let dw : ℝ → ℝ := fun t => (bufferSign i / B.mass i) * deriv p (positiveBufferPoint B i (-t))
  let q : ℝ → ℝ := fun t => B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2
  have hv : ContDiff ℝ ∞ v := by
    simpa only [v, ← positiveBufferPoint_outward_affine] using
      positiveBuffer_affine_contDiff hu (bufferCut B i) (bufferSign i / B.mass i)
  have hw : ContDiff ℝ ∞ w := by
    simpa only [w, ← positiveBufferPoint_outward_affine] using
      positiveBuffer_affine_contDiff hp (bufferCut B i) (bufferSign i / B.mass i)
  have hclassu := positiveBufferPoint_outward_classical hB i hu huODE
  have hclassp := positiveBufferPoint_outward_classical hB i hp hpODE
  have hq : ∀ t ∈ Ioi (0 : ℝ), (1 : ℝ) ^ 2 ≤ q t := by
    intro t ht
    have ht' : 0 < t := ht
    have hσ := buffer_action_pos hB i
    simpa only [one_pow, q] using
      positiveBufferPoint_normalized_potential_lower hB i (t := -t) (by linarith)
  have hmem (t : ℝ) (ht : t ∈ Ici 0) :
      positiveBufferPoint B i (-t) ∈ closure (bufferExterior B i) := by
    change t ∈ (fun s : ℝ => positiveBufferPoint B i (-s)) ⁻¹' closure (bufferExterior B i)
    rw [positiveBufferPoint_outward_preimage_exterior_closure hB i]
    exact ht
  have hw0 : w 0 = 1 := by simpa only [w, neg_zero, positiveBufferPoint_zero] using hp0
  have hvb : ∀ t ∈ Ici 0, |v t| ≤ Mu := fun t ht => hub _ (hmem t ht)
  have hwb : ∀ t ∈ Ici 0, |w t| ≤ Mp := fun t ht => hpb _ (hmem t ht)
  have hprop := positiveBuffer_halfline_proportional
    (u := v) (du := dv) (p := w) (dp := dw) (q := q) (m := 1)
    (by norm_num) hMu hMp hv.continuous.continuousOn hw.continuous.continuousOn
    (fun t ht => (hclassu t ht).1) (fun t ht => (hclassu t ht).2)
    (fun t ht => (hclassp t ht).1) (fun t ht => (hclassp t ht).2)
    hq hw0 hvb hwb
  have hv0 : HasDerivAt v (dv 0) 0 :=
    positiveBufferPoint_outward_hasDerivAt
      ((hu.differentiable (by simp) (positiveBufferPoint B i (-0))).hasDerivAt)
  have hw0d : HasDerivAt w (dw 0) 0 :=
    positiveBufferPoint_outward_hasDerivAt
      ((hp.differentiable (by simp) (positiveBufferPoint B i (-0))).hasDerivAt)
  have hderiv := positiveBuffer_halfline_proportional_derivative
    (u := v) (du := dv) (p := w) (dp := dw) (q := q) (m := 1)
    (by norm_num) hMu hMp hv.continuous.continuousOn hw.continuous.continuousOn
    (fun t ht => (hclassu t ht).1) (fun t ht => (hclassu t ht).2)
    (fun t ht => (hclassp t ht).1) (fun t ht => (hclassp t ht).2)
    hq hw0 hvb hwb hv0 hw0d
  refine ⟨?_, ?_⟩
  · intro x hx
    let t : ℝ := -positiveBufferCoordinate B i x
    have hpoint : positiveBufferPoint B i (-t) = x := by
      dsimp [t]
      rw [neg_neg, positiveBufferPoint_coordinate hB i x]
    have ht : t ∈ Ici 0 := by
      rw [← positiveBufferPoint_outward_preimage_exterior_closure hB i]
      change positiveBufferPoint B i (-t) ∈ closure (bufferExterior B i)
      rw [hpoint]
      exact hx
    have h := hprop t ht
    change u (positiveBufferPoint B i (-t)) =
      u (positiveBufferPoint B i (-0)) * p (positiveBufferPoint B i (-t)) at h
    simpa only [hpoint, neg_zero, positiveBufferPoint_zero] using h
  · have hm := buffer_mass_pos hB i
    have hb : bufferSign i / B.mass i ≠ 0 := by
      apply abs_ne_zero.mp
      rw [abs_div, abs_bufferSign, abs_of_pos hm]
      exact (one_div_pos.mpr hm).ne'
    simp only [dv, dw, v, neg_zero, positiveBufferPoint_zero] at hderiv
    apply mul_left_cancel₀ hb
    calc
      _ = u (bufferCut B i) * ((bufferSign i / B.mass i) * deriv p (bufferCut B i)) := hderiv
      _ = _ := by ring

end ContinuousFlexibility.Radial
