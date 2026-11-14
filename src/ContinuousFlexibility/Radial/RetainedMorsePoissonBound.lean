module

public import ContinuousFlexibility.Radial.RetainedMorseModelChart
public import ContinuousFlexibility.Radial.InnerMorsePhysicalPoisson
public import ContinuousFlexibility.Radial.MatchedInnerUnitWeights

/-!
# The original normalized Morse Poisson estimate on the retained profile

The two independent radial dilations cancel in the logarithmic
velocity. The original localized witness and its normalized remainder
are kept unchanged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

namespace SeedRetainedPair

variable {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
  (P : SeedRetainedPair S K q length) {D : ReferenceData}
  (hw : D.w = P.pair.profile) (hS : IsSelectedTail S)
  (G₀ : MorseChainGeometryWitness S.chain)
  (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2)
  {n : ℕ} (H : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : S.chain.index ≤ m) (haway : piece ≠ central)
  (hleft : H.left piece = P.sideRadius side * innerMorseChainCut S.chain side m 0)
  (hright : H.right piece = P.sideRadius side * innerMorseChainCut S.chain side m 1)
  {Cmodel Kmodel : ℝ}
  (hB : BufferHypotheses
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
      j (8 * (S.chain.d m : ℝ) ^ 9)) Cmodel Kmodel)


theorem retainedMorseModelChart_column_bound (hj : 1 ≤ j) (hC : 0 < Cmodel)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j) (i : Fin 2) :
    ‖(sqrt ((P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
        side m hm haway hleft hright hB M).kappa i))⁻¹ •
      (P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
        side m hm haway hleft hright hB M).column i‖ ≤ innerMorsePoissonConstant / j := by
  let A := P.retainedMorseModelChart hw hS G₀ hband H bordered j central piece column
    side m hm haway hleft hright hB M
  let B := innerMorseBufferData (morseChainA S.chain m) (morseChainB S.chain m)
    j (8 * (S.chain.d m : ℝ) ^ 9)
  let Ucap : ℝ := (30000 / j) * B.mass i
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hindex : 10 ≤ S.chain.index := (by norm_num : 10 ≤ 100).trans G₀.start_large
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hmass := buffer_mass_pos hB i
  have hk := (M.energies_pos hB hC i).1
  have hUcap : 0 ≤ Ucap := mul_nonneg (div_nonneg (by norm_num) hjpos.le) hmass.le
  have hbuffer (x : ℝ) (hx : x ∈ uIcc (bufferCut B i) (bufferInnerWall B i)) :
      |deriv A.radius x / A.radius x| ≤ Ucap := by
    have hr := hreal.radius_positive side m hm x
      (innerMorseChain_buffer_subset hreal side hm (innerBuffer_closedSpan_subset hB i hx))
    have he : deriv A.radius x / A.radius x =
        deriv (S.chain.radius side m) x / S.chain.radius side m x := by
      change deriv (fun y => P.sideRadius side * S.chain.radius side m y) x /
        (P.sideRadius side * S.chain.radius side m x) = _
      rw [deriv_const_mul_field]
      field_simp [(P.sideRadius_pos side).ne', hr.ne'] <;> ring
    rw [he]
    exact (div_le_iff₀ hmass).mp
      (innerMorseChain_buffer_cap_ratio hreal side hindex hm hjpos
        (8 * (S.chain.d m : ℝ) ^ 9) i hx)
  have hvelocity : Ucap / B.mass i ≤ 30000 / j := by
    dsimp only [Ucap]
    exact (mul_div_cancel_right₀ _ hmass.ne').le
  have hE : (1 : ℝ) ≤ radialE m := by
    change 1 ≤ exp (radialQ m)
    apply one_le_exp
    exact (sq_nonneg (m : ℝ)).trans (radial_nat_sq_le_Q m)
  have hnorm := innerModelPhysicalPoissonColumn_frequency_bound D hB M A.height_pos
    A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
    14 (by norm_num) A.log_deriv_bound
    (fun _ => 1) measurable_const 1 (by simp) i
    (ratio := radialE m) (w := 1) (Ucap := Ucap)
    (k := (M.column i).inwardEnergy) (j := j) (Kcap := 30000)
    (exp_pos _).le zero_lt_one hUcap hk hjpos (by norm_num)
    (fun _ => rfl) (fun _ _ => rfl) hbuffer
    (by intro x hx; simpa only [abs_one, mul_one] using hE)
    (by linarith only [hk]) hvelocity
    (by simpa only [innerMorseModelNormalizedRemainder] using hrem i)
  rw [retainedMorseModelChart_kappa]
  simpa only [A, retainedMorseModelChart,
    InnerRadialModelChart.column, one_pow, mul_one, one_mul,
    innerBorderFieldMap_weight_one_unit, ContinuousLinearMap.id_apply,
    innerMorsePoissonConstant] using hnorm

end SeedRetainedPair

end ContinuousFlexibility.Radial
