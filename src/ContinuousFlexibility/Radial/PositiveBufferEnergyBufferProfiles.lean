module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyExterior
public import ContinuousFlexibility.Radial.PositiveBufferGeometry

/-!
# The finite and exterior profiles of the frozen buffer data

This module applies the actual variational construction to both cuts in
`BufferData`.  It constructs the finite and exterior Poisson profiles,
their physical conormal coefficients, and uniform comparison with the
barrier masses.  The only upper-potential information used is the given
bound in the cut layers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_innerWall_order {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) :
    if i = 0 then bufferCut B i < bufferInnerWall B i
    else bufferInnerWall B i < bufferCut B i := by
  have hm := buffer_mass_pos hB i
  have ha := buffer_action_pos hB i
  have hlen : 0 < (B.action i + 6) / B.mass i := div_pos (by linarith) hm
  by_cases hi : i = 0
  · simpa only [bufferInnerWall, bufferCut, bufferSign, hi, ite_true,
      neg_mul, one_mul, neg_div, sub_neg_eq_add, lt_add_iff_pos_right] using hlen
  · simpa only [bufferInnerWall, bufferCut, bufferSign, hi, ite_false, one_mul,
      sub_lt_self_iff] using hlen

theorem positiveBuffer_innerWall_distance_lower {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) : 2 / B.mass i ≤ |bufferInnerWall B i - bufferCut B i| := by
  have hm := buffer_mass_pos hB i
  have ha := buffer_action_pos hB i
  have hd := positiveBufferPoint_distance hB i (B.action i + 6) 0
  rw [positiveBufferPoint_innerWall, positiveBufferPoint_zero, sub_zero,
    abs_of_pos (by linarith : 0 < B.action i + 6)] at hd
  rw [hd]
  exact (div_le_div_iff_of_pos_right hm).mpr (by linarith)

theorem positiveBuffer_potential_lower_span {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ} (hx : x ∈ uIcc (bufferCut B i) (bufferInnerWall B i)) :
    B.mass i ^ 2 ≤ B.potential x := by
  have hord := positiveBuffer_innerWall_order hB i
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _⟩
  apply hlo i x
  by_cases hi : i = 0
  · have hlt : bufferCut B i < bufferInnerWall B i := by simpa only [hi, ite_true] using hord
    have hc := hlt.le
    rw [uIcc_of_le hc] at hx
    simpa only [bufferInnerWall, bufferCut, bufferSign, hi, ite_true, neg_mul,
      one_mul, neg_div, sub_neg_eq_add] using hx.2
  · have hlt : bufferInnerWall B i < bufferCut B i := by simpa only [hi, ite_false] using hord
    have hc := hlt.le
    rw [uIcc_of_ge hc] at hx
    simpa only [bufferInnerWall, bufferCut, bufferSign, hi, ite_false, one_mul] using hx.1

theorem positiveBuffer_potential_lower_cutLayer {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ} (hx : |x - bufferCut B i| ≤ 2 / B.mass i) :
    B.mass i ^ 2 ≤ B.potential x := by
  have hm := buffer_mass_pos hB i
  have ha := buffer_action_pos hB i
  have hlen : 2 / B.mass i ≤ (B.action i + 6) / B.mass i :=
    (div_le_div_iff_of_pos_right hm).mpr (by linarith)
  have hx' := abs_le.mp hx
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _⟩
  apply hlo i x
  by_cases hi : i = 0
  · simp only [hi] at hlen
    simp only [bufferCut, hi, ite_true] at hx'
    simp only [hi, ite_true]
    linarith [hx'.2]
  · simp only [bufferCut, hi, ite_false] at hx'
    simp only [hi, ite_false]
    linarith [hx'.1]

theorem positiveBuffer_potential_lower_exterior {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ} (hx : x ∈ closure (bufferExterior B i)) :
    B.mass i ^ 2 ≤ B.potential x := by
  have hm := buffer_mass_pos hB i
  have ha := buffer_action_pos hB i
  have hlen : 0 ≤ (B.action i + 6) / B.mass i := div_nonneg (by linarith) hm.le
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _⟩
  apply hlo i x
  by_cases hi : i = 0
  · simp only [hi] at hlen
    simp only [bufferExterior, hi, ite_true, closure_Iio, mem_Iic] at hx
    simp only [hi, ite_true]
    linarith
  · simp only [bufferExterior, hi, ite_false, closure_Ioi, mem_Ici] at hx
    simp only [hi, ite_false]
    linarith

theorem positiveBuffer_potential_upper_cutLayer {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {x : ℝ} (hx : |x - bufferCut B i| ≤ 2 / B.mass i) :
    B.potential x ≤ B.layerBound * B.mass i ^ 2 := by
  have hm := buffer_mass_pos hB i
  rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hup, _⟩
  apply hup i x
  exact Or.inl (hx.trans ((div_le_div_iff_of_pos_right hm).mpr (by norm_num)))

/-- The actual finite and exterior unit-trace profiles required at the two
cuts. Their conormals are their physical energies, and each lies between
the barrier mass and a common constant times that mass. -/
theorem positiveBuffer_exists_buffer_profiles {B : BufferData} (hB : BufferHypotheses B) :
    ∃ pin pout : Fin 2 → ℝ → ℝ, ∃ αin αout : Fin 2 → ℝ,
      ∀ i,
        ContDiff ℝ ∞ (pin i) ∧ ContDiff ℝ ∞ (pout i) ∧
        IntervalIntegrable (fun x => deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2)
          volume (bufferCut B i) (bufferInnerWall B i) ∧
        IntegrableOn (fun x => deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2)
          (bufferExterior B i) volume ∧
        pin i (bufferCut B i) = 1 ∧ pin i (bufferInnerWall B i) = 0 ∧
        pout i (bufferCut B i) = 1 ∧
        MemLp (pout i) 2 (volume.restrict (bufferExterior B i)) ∧
        (∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
          -deriv (deriv (pin i)) x + B.potential x * pin i x = 0) ∧
        (∀ x ∈ bufferExterior B i,
          -deriv (deriv (pout i)) x + B.potential x * pout i x = 0) ∧
        αin i = bufferSign i * deriv (pin i) (bufferCut B i) ∧
        αout i = -bufferSign i * deriv (pout i) (bufferCut B i) ∧
        αin i = (∫ x in min (bufferCut B i) (bufferInnerWall B i)..
          max (bufferCut B i) (bufferInnerWall B i),
            deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2) ∧
        αout i = (∫ x in bufferExterior B i,
          deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2) ∧
        B.mass i ≤ αin i ∧
        αin i ≤ 4 * (morseCutoffDerivativeConstant ^ 2 + B.layerBound) * B.mass i ∧
        B.mass i ≤ αout i ∧
        αout i ≤ 4 * (morseCutoffDerivativeConstant ^ 2 + B.layerBound) * B.mass i := by
  have hV := hB.2.2.2.2.1
  have hreal := hB.2.2.2.2.2.1
  have hC₀ : 0 ≤ B.layerBound := hB.2.2.2.1.le
  have hcut (i : Fin 2) (x : ℝ)
      (hx : x ∈ Icc (bufferCut B i - 2 / B.mass i) (bufferCut B i + 2 / B.mass i)) :
      B.mass i ^ 2 ≤ B.potential x := by
    apply positiveBuffer_potential_lower_cutLayer hB i
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpin (i : Fin 2) := positiveBuffer_exists_finite_unit_profile hreal hV
    (buffer_mass_pos hB i) hC₀ (positiveBuffer_innerWall_distance_lower hB i)
    (fun x hx => hx.elim (positiveBuffer_potential_lower_span hB i) (hcut i x))
    (fun x hx => positiveBuffer_potential_upper_cutLayer hB i hx)
  have hside (i : Fin 2) : bufferExterior B i = Ioi (bufferCut B i) ∨
      bufferExterior B i = Iio (bufferCut B i) := by
    by_cases hi : i = 0
    · exact Or.inr (by simp only [bufferExterior, bufferCut, hi, ite_true])
    · exact Or.inl (by simp only [bufferExterior, bufferCut, hi, ite_false])
  have hpout (i : Fin 2) := positiveBuffer_exists_exterior_unit_profile hreal hV (hside i)
    (buffer_mass_pos hB i) hC₀
    (fun x hx => hx.elim (positiveBuffer_potential_lower_exterior hB i) (hcut i x))
    (fun x hx => positiveBuffer_potential_upper_cutLayer hB i hx)
  choose pin hpin_sm hpin_cut hpin_wall hpin_ODE hpin_flux hpin_low hpin_upper using hpin
  choose pout hpout_sm hpout_cut hpout_Lp hpout_E hpout_ODE hpout_flux hpout_low hpout_upper using hpout
  let αin (i : Fin 2) := bufferSign i * deriv (pin i) (bufferCut B i)
  let αout (i : Fin 2) := -bufferSign i * deriv (pout i) (bufferCut B i)
  have hin (i : Fin 2) : αin i =
      ∫ x in min (bufferCut B i) (bufferInnerWall B i)..max (bufferCut B i) (bufferInnerWall B i),
        deriv (pin i) x ^ 2 + B.potential x * pin i x ^ 2 := by
    rw [hpin_flux i]
    have hord := positiveBuffer_innerWall_order hB i
    by_cases hi : i = 0
    · have hc : bufferCut B i < bufferInnerWall B i := by simpa only [hi, ite_true] using hord
      rw [if_pos hc]
      simp only [αin, bufferSign, hi, ite_true, neg_mul, one_mul]
    · have hlt : bufferInnerWall B i < bufferCut B i := by simpa only [hi, ite_false] using hord
      have hc : ¬bufferCut B i < bufferInnerWall B i := hlt.not_gt
      rw [if_neg hc]
      simp only [αin, bufferSign, hi, ite_false, one_mul]
  have hout (i : Fin 2) : αout i =
      ∫ x in bufferExterior B i, deriv (pout i) x ^ 2 + B.potential x * pout i x ^ 2 := by
    rw [hpout_flux i]
    by_cases hi : i = 0
    · have hne : bufferExterior B i ≠ Ioi (bufferCut B i) := by
        simp only [bufferExterior, bufferCut, hi, ite_true]
        intro heq
        have hx : B.l - 1 ∈ Ioi B.l := heq ▸ (show B.l - 1 ∈ Iio B.l by simp)
        linarith [mem_Ioi.mp hx]
      rw [if_neg hne]
      simp only [αout, bufferSign, hi, ite_true, neg_neg, one_mul]
    · have heq : bufferExterior B i = Ioi (bufferCut B i) := by
        simp only [bufferExterior, bufferCut, hi, ite_false]
      rw [if_pos heq]
      simp only [αout, bufferSign, hi, ite_false, neg_mul, one_mul]
  refine ⟨pin, pout, αin, αout, ?_⟩
  intro i
  have hpd := (contDiff_infty_iff_deriv.mp (hpin_sm i)).2
  refine ⟨hpin_sm i, hpout_sm i, ?_, hpout_E i, hpin_cut i, hpin_wall i,
    hpout_cut i, hpout_Lp i, hpin_ODE i, hpout_ODE i, rfl, rfl, hin i, hout i, ?_, ?_, ?_, ?_⟩
  · exact ((hpd.continuous.pow 2).add (hV.continuous.mul ((hpin_sm i).continuous.pow 2))).intervalIntegrable _ _
  · rw [hin i]
    exact hpin_low i
  · rw [hin i]
    exact hpin_upper i
  · rw [hout i]
    exact hpout_low i
  · rw [hout i]
    exact hpout_upper i

end ContinuousFlexibility.Radial
