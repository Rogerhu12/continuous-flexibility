import ContinuousFlexibility.Radial.InnerBufferPoisson
import ContinuousFlexibility.Radial.InnerRadialL2Mass

/-!
# The leading buffer column and its exact energy cost

The leading column is the cutoff of the same Dirichlet buffer solution
used by compression. The potential lower bound on that buffer controls
its L² mass by the actual inward boundary energy. This keeps the inverse
mass factor before the physical Liouville change of coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerL2_interval_energy_bound {a b m : ℝ} {V p : ℝ → ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hV : ∀ x ∈ Icc a b, m ^ 2 ≤ V x)
    (hE : IntervalIntegrable (fun x => deriv p x ^ 2 + V x * p x ^ 2) volume a b)
    (L : RadialL2)
    (hpoint : ∀ᵐ x ∂volume, x ∈ Icc a b → |L x| ≤ |p x|)
    (hsupport : ∀ᵐ x ∂volume, x ∉ Icc a b → L x = 0) :
    m ^ 2 * ‖L‖ ^ 2 ≤ ∫ x in a..b, deriv p x ^ 2 + V x * p x ^ 2 := by
  let E : ℝ → ℝ := fun x => deriv p x ^ 2 + V x * p x ^ 2
  have hEint : Integrable ((Icc a b).indicator E) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hE)
  have hLint : Integrable (fun x => m ^ 2 * L x ^ 2) volume :=
    (Lp.memLp L).integrable_sq.const_mul _
  have hle : (fun x => m ^ 2 * L x ^ 2) ≤ᵐ[volume] (Icc a b).indicator E := by
    filter_upwards [hpoint, hsupport] with x hp hz
    by_cases hx : x ∈ Icc a b
    · rw [Set.indicator_of_mem hx]
      have hsq : L x ^ 2 ≤ p x ^ 2 := sq_le_sq.mpr (hp hx)
      calc
        m ^ 2 * L x ^ 2 ≤ m ^ 2 * p x ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ ≤ V x * p x ^ 2 := mul_le_mul_of_nonneg_right (hV x hx) (sq_nonneg _)
        _ ≤ deriv p x ^ 2 + V x * p x ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
    · rw [hz hx, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        Set.indicator_of_notMem hx]
  have h := integral_mono_ae hLint hEint hle
  rw [integral_const_mul, ← innerL2_norm_sq_eq_integral volume L,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab] at h
  exact h

theorem innerL2_norm_le_sqrt_energy {m E : ℝ} (hm : 0 < m) (L : RadialL2)
    (h : m ^ 2 * ‖L‖ ^ 2 ≤ E) : ‖L‖ ≤ sqrt E / m := by
  have hE : 0 ≤ E := (mul_nonneg (sq_nonneg m) (sq_nonneg ‖L‖)).trans h
  apply (le_div_iff₀ hm).mpr
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg L) hm.le) (sqrt_nonneg E)).mp
  calc
    (‖L‖ * m) ^ 2 = m ^ 2 * ‖L‖ ^ 2 := by ring
    _ ≤ E := h
    _ = (sqrt E) ^ 2 := (sq_sqrt hE).symm

/-- The R09 positive-potential assumption holds on the entire closed
buffer, including both of its endpoints and either orientation. -/
theorem innerBuffer_potential_lower_closed {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc (bufferCut B i) (bufferInnerWall B i)) :
    B.mass i ^ 2 ≤ B.potential x := by
  have hW := innerBuffer_walls_inside hB
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _⟩
  fin_cases i
  · have hx' : x ∈ uIcc B.l (bufferInnerWall B 0) := by
      simpa only [bufferCut, if_pos rfl] using hx
    rw [uIcc_of_le hW.1.le] at hx'
    apply hlo 0
    simpa only [bufferInnerWall, bufferCut, bufferSign, if_pos rfl, neg_mul,
      one_mul, neg_div, sub_neg_eq_add] using hx'.2
  · have hx' : x ∈ uIcc B.h (bufferInnerWall B 1) := by
      simpa only [bufferCut, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hx
    rw [uIcc_of_ge hW.2.2.le] at hx'
    apply hlo 1
    simpa only [bufferInnerWall, bufferCut, bufferSign,
      if_neg (by decide : (1 : Fin 2) ≠ 0), one_mul] using hx'.1

/-- The actual leading cutoff has no larger height than its buffer
column and is supported in that same buffer. -/
theorem innerBufferLeading_point_support {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (p : ℝ → ℝ) (L : RadialL2)
    (hL : (L : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator (fun x => innerBufferCutoff B i x * p x)) :
    (∀ᵐ x ∂volume, |L x| ≤ |p x|) ∧
      (∀ᵐ x ∂volume, x ∉ uIcc (bufferCut B i) (bufferInnerWall B i) → L x = 0) := by
  constructor
  · filter_upwards [hL] with x hx
    rw [hx]
    by_cases hi : x ∈ Ioo B.l B.h
    · rw [Set.indicator_of_mem hi, abs_mul,
        abs_of_nonneg (innerBufferCutoff_nonneg B i x)]
      exact (mul_le_mul_of_nonneg_right (innerBufferCutoff_le_one B i x)
        (abs_nonneg (p x))).trans_eq (one_mul _)
    · rw [Set.indicator_of_notMem hi, abs_zero]
      exact abs_nonneg _
  · filter_upwards [hL] with x hx hout
    rw [hx]
    by_cases hi : x ∈ Ioo B.l B.h
    · rw [Set.indicator_of_mem hi]
      have hχ : innerBufferCutoff B i x = 0 := by
        by_contra hne
        have hs : x ∈ tsupport (innerBufferCutoff B i) := subset_closure hne
        rcases innerBufferCutoff_tsupport_retained hB i (Ioo_subset_Icc_self hi) hs with
            hcut | hbuffer
        · exact hout (hcut ▸ left_mem_uIcc)
        · exact hout (Ioo_subset_Icc_self hbuffer)
      rw [hχ, zero_mul]
    · rw [Set.indicator_of_notMem hi]

/-- The inward flux energy controls the actual leading L² column with
the inverse mass factor. This uses the same alpha-in as R09. -/
theorem innerBufferLeading_norm_bound {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ} {αin : ℝ}
    (hE : IntervalIntegrable (fun x => deriv p x ^ 2 + B.potential x * p x ^ 2)
      volume (bufferCut B i) (bufferInnerWall B i))
    (hα : αin = ∫ x in min (bufferCut B i) (bufferInnerWall B i)..
      max (bufferCut B i) (bufferInnerWall B i),
        deriv p x ^ 2 + B.potential x * p x ^ 2)
    (L : RadialL2)
    (hL : (L : ℝ → ℝ) =ᵐ[volume]
      (Ioo B.l B.h).indicator (fun x => innerBufferCutoff B i x * p x)) :
    ‖L‖ ≤ sqrt αin / B.mass i := by
  have hnorm := innerBufferLeading_point_support hB i p L hL
  have hE' : IntervalIntegrable (fun x => deriv p x ^ 2 + B.potential x * p x ^ 2)
      volume (min (bufferCut B i) (bufferInnerWall B i))
        (max (bufferCut B i) (bufferInnerWall B i)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (min_le_max _ _)]
    exact (intervalIntegrable_iff').mp hE
  apply innerL2_norm_le_sqrt_energy (buffer_mass_pos hB i) L
  rw [hα]
  apply innerL2_interval_energy_bound (min_le_max _ _) (buffer_mass_pos hB i)
    (fun x hx => innerBuffer_potential_lower_closed hB i hx) hE' L
  · filter_upwards [hnorm.1] with x hx _
    exact hx
  · exact hnorm.2

end ContinuousFlexibility.Radial
