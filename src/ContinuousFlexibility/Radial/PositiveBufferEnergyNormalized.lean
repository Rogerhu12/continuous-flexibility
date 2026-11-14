module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyMass
public import ContinuousFlexibility.Radial.PositiveBufferComparisonDomains

/-!
# Normalizing the actual endpoint profiles

The physical smooth minimizers are transported to the common inward
coordinate and the reflected outward coordinate. Ordinary derivatives,
the homogeneous equation and the conormal normalization are transported
with the actual affine slopes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_affine_homogeneous_equation {p V : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (a b t : ℝ)
    (hODE : -deriv (deriv p) (a + b * t) + V (a + b * t) * p (a + b * t) = 0) :
    -deriv (deriv (fun s => p (a + b * s))) t +
      (b ^ 2 * V (a + b * t)) * p (a + b * t) = 0 := by
  have hpd := (contDiff_infty_iff_deriv.mp hp).2
  have hfirst : deriv (fun s => p (a + b * s)) =
      fun s => b * deriv p (a + b * s) := by
    funext s
    exact (positiveBuffer_affine_hasDerivAt
      (hp.differentiable (by simp) (a + b * s)).hasDerivAt).deriv
  have hsecond : HasDerivAt (deriv p) (V (a + b * t) * p (a + b * t)) (a + b * t) := by
    convert (hpd.differentiable (by simp) (a + b * t)).hasDerivAt using 1
    linarith
  have hscaled := (positiveBuffer_affine_hasDerivAt hsecond).const_mul b
  rw [hfirst, hscaled.deriv]
  ring

theorem positiveBuffer_normalized_inner_contDiff {B : BufferData} (i : Fin 2)
    {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun t => p (positiveBufferPoint B i t)) := by
  simpa only [← positiveBufferPoint_affine] using
    positiveBuffer_affine_contDiff hp (bufferCut B i) (-bufferSign i / B.mass i)

theorem positiveBuffer_normalized_outer_contDiff {B : BufferData} (i : Fin 2)
    {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun t => p (positiveBufferPoint B i (-t))) := by
  simpa only [← positiveBufferPoint_outward_affine] using
    positiveBuffer_affine_contDiff hp (bufferCut B i) (bufferSign i / B.mass i)

theorem positiveBuffer_normalized_inner_deriv_zero {B : BufferData} (i : Fin 2)
    {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    deriv (fun t => p (positiveBufferPoint B i t)) 0 =
      (-bufferSign i / B.mass i) * deriv p (bufferCut B i) := by
  have h := positiveBufferPoint_hasDerivAt (B := B) (i := i) (t := 0)
    (hp.differentiable (by simp) (positiveBufferPoint B i 0)).hasDerivAt
  simpa only [positiveBufferPoint_zero] using h.deriv

theorem positiveBuffer_normalized_outer_deriv_zero {B : BufferData} (i : Fin 2)
    {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) :
    deriv (fun t => p (positiveBufferPoint B i (-t))) 0 =
      (bufferSign i / B.mass i) * deriv p (bufferCut B i) := by
  have h := positiveBuffer_affine_hasDerivAt
    (a := bufferCut B i) (b := bufferSign i / B.mass i) (x := 0)
    (hp.differentiable (by simp) (bufferCut B i + (bufferSign i / B.mass i) * 0)).hasDerivAt
  simpa only [← positiveBufferPoint_outward_affine, neg_zero, positiveBufferPoint_zero] using h.deriv

theorem positiveBuffer_normalized_inner_equation {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (hODE : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0) :
    ∀ t ∈ Ioo 0 (B.action i + 6),
      -deriv (deriv (fun s => p (positiveBufferPoint B i s))) t +
        (B.potential (positiveBufferPoint B i t) / B.mass i ^ 2) *
          p (positiveBufferPoint B i t) = 0 := by
  intro t ht
  have he := hODE _ (positiveBufferPoint_mem_openSpan hB i ht)
  have h := positiveBuffer_affine_homogeneous_equation hp (bufferCut B i)
    (-bufferSign i / B.mass i) t
    (by simpa only [← positiveBufferPoint_affine] using he)
  simp only [← positiveBufferPoint_affine, positiveBufferPoint_slope_sq] at h
  have hcoeff :
      (1 / B.mass i ^ 2) * B.potential (positiveBufferPoint B i t) =
        B.potential (positiveBufferPoint B i t) / B.mass i ^ 2 := by ring
  simpa only [hcoeff] using h

theorem positiveBuffer_normalized_outer_equation {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (hODE : ∀ x ∈ bufferExterior B i, -deriv (deriv p) x + B.potential x * p x = 0) :
    ∀ t ∈ Ioi 0,
      -deriv (deriv (fun s => p (positiveBufferPoint B i (-s)))) t +
        (B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2) *
          p (positiveBufferPoint B i (-t)) = 0 := by
  intro t ht
  have hx : positiveBufferPoint B i (-t) ∈ bufferExterior B i := by
    have hmem : t ∈ (fun s : ℝ => positiveBufferPoint B i (-s)) ⁻¹' bufferExterior B i := by
      rwa [positiveBufferPoint_outward_preimage_exterior hB i]
    exact hmem
  have he := hODE _ hx
  have h := positiveBuffer_affine_homogeneous_equation hp (bufferCut B i)
    (bufferSign i / B.mass i) t
    (by simpa only [← positiveBufferPoint_outward_affine] using he)
  have hslope : (bufferSign i / B.mass i) ^ 2 = 1 / B.mass i ^ 2 := by
    rw [div_pow, bufferSign_sq]
  simp only [← positiveBufferPoint_outward_affine, hslope] at h
  have hcoeff :
      (1 / B.mass i ^ 2) * B.potential (positiveBufferPoint B i (-t)) =
        B.potential (positiveBufferPoint B i (-t)) / B.mass i ^ 2 := by ring
  simpa only [hcoeff] using h

theorem positiveBuffer_normalized_conormal_sum {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {pin pout : ℝ → ℝ} {αin αout : ℝ}
    (hpin : ContDiff ℝ ∞ pin) (hpout : ContDiff ℝ ∞ pout)
    (hin : αin = bufferSign i * deriv pin (bufferCut B i))
    (hout : αout = -bufferSign i * deriv pout (bufferCut B i)) :
    αin + αout = B.mass i *
      (-deriv (fun t => pout (positiveBufferPoint B i (-t))) 0 -
        deriv (fun t => pin (positiveBufferPoint B i t)) 0) := by
  rw [positiveBuffer_normalized_outer_deriv_zero i hpout,
    positiveBuffer_normalized_inner_deriv_zero i hpin, hin, hout]
  field_simp [(buffer_mass_pos hB i).ne']
  <;> ring

end ContinuousFlexibility.Radial
