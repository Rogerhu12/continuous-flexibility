import ContinuousFlexibility.Radial.PositiveBufferComparisonTrace
import ContinuousFlexibility.Radial.PositiveBufferComparisonGreenRegularity

/-!
# The sharp trace of a full-model correction at either cut

One outward affine coordinate handles both physical endpoints. The
comparison uses a preceding normalized interval of length one, hence
only the actual L² norm appears on the right-hand side.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_oriented_cut_trace_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {U : ℝ → ℝ}
    (hU : ContDiff ℝ ∞ U) (F : RadialL2)
    (hrep : (F : ℝ → ℝ) =ᵐ[volume] U) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |U x| ≤ M)
    (hhom : ∀ t : ℝ, t < B.action i + 2 →
      -deriv (deriv U) (positiveBufferPoint B i t) +
        B.potential (positiveBufferPoint B i t) * U (positiveBufferPoint B i t) = 0) :
    |U (bufferCut B i)| ≤ sqrt (B.mass i) * exp (-B.action i) * ‖F‖ := by
  have hm := buffer_mass_pos hB i
  have hσ := buffer_action_pos hB i
  let b : ℝ := bufferSign i / B.mass i
  let a : ℝ := -(B.action i + 1)
  let v : ℝ → ℝ := fun r => U (bufferCut B i + b * r)
  let dv : ℝ → ℝ := fun r => b * deriv U (bufferCut B i + b * r)
  let q : ℝ → ℝ := fun r => B.potential (bufferCut B i + b * r) / B.mass i ^ 2
  have hbabs : |b| = 1 / B.mass i := by
    dsimp [b]
    rw [abs_div, abs_bufferSign, abs_of_pos hm]
  have hb : b ≠ 0 := by
    apply abs_ne_zero.mp
    rw [hbabs]
    exact (one_div_pos.mpr hm).ne'
  have hbsq : b ^ 2 = 1 / B.mass i ^ 2 := by
    dsimp [b]
    rw [div_pow, bufferSign_sq]
  have hdU : ContDiff ℝ ∞ (deriv U) := (contDiff_infty_iff_deriv.mp hU).2
  have hv : Continuous v := hU.continuous.comp
    (continuous_const.add (continuous_const.mul continuous_id))
  have hvderiv : ∀ r ∈ Ioi a, HasDerivAt v (dv r) r := by
    intro r _
    exact positiveBuffer_affine_hasDerivAt
      ((hU.differentiable (by simp) (bufferCut B i + b * r)).hasDerivAt)
  have hdvderiv : ∀ r ∈ Ioi a, HasDerivAt dv (q r * v r) r := by
    intro r hr
    have htr : -r < B.action i + 2 := by change a < r at hr; dsimp [a] at hr; linarith
    have heq := hhom (-r) htr
    rw [positiveBufferPoint_outward_affine] at heq
    have hscalarODE : deriv (deriv U) (bufferCut B i + b * r) =
        B.potential (bufferCut B i + b * r) * U (bufferCut B i + b * r) := by
      change -deriv (deriv U) (bufferCut B i + b * r) +
        B.potential (bufferCut B i + b * r) * U (bufferCut B i + b * r) = 0 at heq
      linarith
    have hbase : HasDerivAt (deriv U)
        (B.potential (bufferCut B i + b * r) * U (bufferCut B i + b * r))
        (bufferCut B i + b * r) := by
      rw [← hscalarODE]
      exact (hdU.differentiable (by simp) _).hasDerivAt
    have hscalar : q r * v r =
        b * (b * (B.potential (bufferCut B i + b * r) * U (bufferCut B i + b * r))) := by
      calc
        _ = (b ^ 2 * B.potential (bufferCut B i + b * r)) * U (bufferCut B i + b * r) := by
          dsimp [q, v]
          rw [hbsq]
          ring
        _ = _ := by ring
    change HasDerivAt (fun s => b * deriv U (bufferCut B i + b * s)) (q r * v r) r
    rw [hscalar]
    exact (positiveBuffer_affine_hasDerivAt hbase).const_mul b
  have hq : ∀ r ∈ Ioi a, (1 : ℝ) ^ 2 ≤ q r := by
    intro r hr
    have ht : -r ≤ B.action i + 6 := by change a < r at hr; dsimp [a] at hr; linarith
    have h := positiveBufferPoint_normalized_potential_lower hB i ht
    rw [positiveBufferPoint_outward_affine] at h
    simpa only [one_pow, q, b] using h
  have hfU : MemLp U 2 volume := (memLp_congr_ae hrep).mp (Lp.memLp F)
  have hUto : hfU.toLp U = F := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hfU).trans hrep.symm
  have hfg : MemLp v 2 volume := positiveBuffer_affine_memLp_two hU.continuous hfU
    (bufferCut B i) hb
  let g : RadialL2 := hfg.toLp v
  have hgrep : (g : ℝ → ℝ) =ᵐ[volume.restrict (Ici a)] v :=
    ae_restrict_of_ae (MemLp.coeFn_toLp hfg)
  have hgnorm : ‖g‖ = sqrt (B.mass i) * ‖F‖ := by
    change ‖(positiveBuffer_affine_memLp_two hU.continuous hfU
      (bufferCut B i) hb).toLp (fun r => U (bufferCut B i + b * r))‖ = _
    rw [positiveBuffer_affine_toLp_norm hU.continuous hfU (bufferCut B i) hb,
      hbabs, one_div, inv_inv, hUto]
  have htrace := positiveBuffer_halfline_l2_trace_bound
    (a := a) (m := 1) (r := a) (c := 0) (σ := B.action i)
    (by norm_num) hM hv.continuousOn hvderiv hdvderiv hq
    (fun r _ => hbound (bufferCut B i + b * r)) g hgrep le_rfl
    (by dsimp [a]; norm_num <;> linarith)
    (by dsimp [a]; norm_num <;> linarith)
  rw [hgnorm] at htrace
  simpa only [v, mul_zero, zero_mul, add_zero, sqrt_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using htrace

/-- The inverse norm supplies the source size independently of the observation cut. -/
theorem positiveBuffer_oriented_correction_trace_bound {B : BufferData}
    (hB : BufferHypotheses B) (i : Fin 2) {U : ℝ → ℝ}
    (hU : ContDiff ℝ ∞ U) (F : RadialL2)
    (hrep : (F : ℝ → ℝ) =ᵐ[volume] U) {M N : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x : ℝ, |U x| ≤ M) (hFnorm : ‖F‖ ≤ N)
    (hhom : ∀ t : ℝ, t < B.action i + 2 →
      -deriv (deriv U) (positiveBufferPoint B i t) +
        B.potential (positiveBufferPoint B i t) * U (positiveBufferPoint B i t) = 0) :
    |U (bufferCut B i)| ≤ sqrt (B.mass i) * exp (-B.action i) * N := by
  exact (positiveBuffer_oriented_cut_trace_bound hB i hU F hrep hM hbound hhom).trans
    (mul_le_mul_of_nonneg_left hFnorm (by positivity))

end ContinuousFlexibility.Radial
