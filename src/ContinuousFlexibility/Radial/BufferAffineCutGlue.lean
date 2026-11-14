module

public import ContinuousFlexibility.Radial.BufferCutGlue
public import ContinuousFlexibility.Radial.BufferEnergyDensity

/-!
# Affine gluing and the physical point-source normalization
A single affine coordinate handles both cuts. Reflection exchanges the two branches
and changes the sign of each first derivative, so the jump transforms by the absolute slope.
-/

@[expose] public section
noncomputable section
namespace ContinuousFlexibility.Radial
open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem bufferCutGlue_affine_ae (c k : ℝ) {b : ℝ} (hb : b ≠ 0) (f g : ℝ → ℝ) :
    (fun x => k * bufferCutGlue 0 f g (b * (x - c))) =ᵐ[volume]
      bufferCutGlue c
        (fun x => k * (if 0 < b then f else g) (b * (x - c)))
        (fun x => k * (if 0 < b then g else f) (b * (x - c))) := by
  filter_upwards [volume.ae_ne c] with x hxc
  by_cases hleft : x < c
  · by_cases hbpos : 0 < b
    · have ht : b * (x - c) < 0 := mul_neg_of_pos_of_neg hbpos (sub_neg.mpr hleft)
      simp [bufferCutGlue, hleft.le, hbpos, ht.le]
    · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
      have ht : 0 < b * (x - c) := mul_pos_of_neg_of_neg hbneg (sub_neg.mpr hleft)
      simp [bufferCutGlue, hleft.le, hbpos, not_le.mpr ht]
  · have hright : c < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hxc)
    by_cases hbpos : 0 < b
    · have ht : 0 < b * (x - c) := mul_pos hbpos (sub_pos.mpr hright)
      simp [bufferCutGlue, not_le.mpr hright, hbpos, not_le.mpr ht]
    · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
      have ht : b * (x - c) < 0 := mul_neg_of_neg_of_pos hbneg (sub_pos.mpr hright)
      simp [bufferCutGlue, not_le.mpr hright, hbpos, ht.le]

theorem bufferAffineBranch_hasDerivAt {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (c k b x : ℝ) :
    HasDerivAt (fun y => k * p (b * (y - c)))
      (k * b * deriv p (b * (x - c))) x := by
  have hd := (((hp.differentiable (by simp) (b * (x - c))).hasDerivAt).comp x
    (((hasDerivAt_id x).sub_const c).const_mul b)).const_mul k
  convert hd using 1 <;> simp only [Function.comp_def, id_eq, mul_one] <;> ring

theorem bufferAffineBranch_second_hasDerivAt {p : ℝ → ℝ} (hp : ContDiff ℝ ∞ p)
    (c k b x : ℝ) :
    HasDerivAt (fun y => k * b * deriv p (b * (y - c)))
      (k * b ^ 2 * deriv (deriv p) (b * (x - c))) x := by
  have hd := bufferAffineBranch_hasDerivAt (contDiff_infty_iff_deriv.mp hp).2 c (k * b) b x
  convert hd using 1 <;> ring

theorem bufferCutGlue_affine_energy_identity {V : ℝ → ℝ} (hV : Continuous V)
    {u d f : RadialL2} {pL pR : ℝ → ℝ}
    (hpL : ContDiff ℝ ∞ pL) (hpR : ContDiff ℝ ∞ pR)
    (c k : ℝ) {b : ℝ} (hb : b ≠ 0) (hmatch : pL 0 = pR 0)
    (hu : (u : ℝ → ℝ) =ᵐ[volume]
      (fun x => k * bufferCutGlue 0 pL pR (b * (x - c))))
    (hd : (d : ℝ → ℝ) =ᵐ[volume]
      (fun x => k * b * bufferCutGlue 0 (deriv pL) (deriv pR) (b * (x - c))))
    (hr : (fun x => k * b ^ 2 *
      bufferCutGlue 0 (deriv (deriv pL)) (deriv (deriv pR)) (b * (x - c)))
        =ᵐ[volume] (fun x => V x * u x - f x)) :
    WeakRadialDerivative u d ∧
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x : ℝ, d x * deriv φ x) + (∫ x : ℝ, V x * u x * φ x) =
          (∫ x : ℝ, f x * φ x) +
            (k * |b| * (deriv pL 0 - deriv pR 0)) * φ c := by
  let L : ℝ → ℝ := if 0 < b then pL else pR
  let R : ℝ → ℝ := if 0 < b then pR else pL
  have hL : ContDiff ℝ ∞ L := by dsimp [L]; split_ifs <;> assumption
  have hR : ContDiff ℝ ∞ R := by dsimp [R]; split_ifs <;> assumption
  have hL' := (contDiff_infty_iff_deriv.mp hL).2
  have hR' := (contDiff_infty_iff_deriv.mp hR).2
  have hL'' := (contDiff_infty_iff_deriv.mp hL').2
  have hR'' := (contDiff_infty_iff_deriv.mp hR').2
  let UL (x : ℝ) := k * L (b * (x - c))
  let UR (x : ℝ) := k * R (b * (x - c))
  let DL (x : ℝ) := k * b * deriv L (b * (x - c))
  let DR (x : ℝ) := k * b * deriv R (b * (x - c))
  let RL (x : ℝ) := k * b ^ 2 * deriv (deriv L) (b * (x - c))
  let RR (x : ℝ) := k * b ^ 2 * deriv (deriv R) (b * (x - c))
  have hcoord : Continuous (fun x : ℝ => b * (x - c)) :=
    (continuous_id.sub continuous_const).const_mul b
  have hUL : Continuous UL := (hL.continuous.comp hcoord).const_mul k
  have hUR : Continuous UR := (hR.continuous.comp hcoord).const_mul k
  have hDL : Continuous DL := (hL'.continuous.comp hcoord).const_mul (k * b)
  have hDR : Continuous DR := (hR'.continuous.comp hcoord).const_mul (k * b)
  have hRL : Continuous RL := (hL''.continuous.comp hcoord).const_mul (k * b ^ 2)
  have hRR : Continuous RR := (hR''.continuous.comp hcoord).const_mul (k * b ^ 2)
  have hu' : (u : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c UL UR :=
    hu.trans (bufferCutGlue_affine_ae c k hb pL pR)
  have hd' : (d : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c DL DR := by
    have h := hd.trans (bufferCutGlue_affine_ae c (k * b) hb (deriv pL) (deriv pR))
    by_cases hbpos : 0 < b
    · simpa only [L, R, DL, DR, if_pos hbpos] using h
    · simpa only [L, R, DL, DR, if_neg hbpos] using h
  have hr' : bufferCutGlue c RL RR =ᵐ[volume] (fun x => V x * u x - f x) := by
    have h := (bufferCutGlue_affine_ae c (k * b ^ 2) hb
      (deriv (deriv pL)) (deriv (deriv pR))).symm.trans hr
    by_cases hbpos : 0 < b
    · simpa only [L, R, RL, RR, if_pos hbpos] using h
    · simpa only [L, R, RL, RR, if_neg hbpos] using h
  have hULc : UL c = UR c := by
    dsimp [UL, UR, L, R]
    by_cases hbpos : 0 < b <;> simp [hbpos, hmatch]
  have hjump : DL c - DR c = k * |b| * (deriv pL 0 - deriv pR 0) := by
    dsimp [DL, DR, L, R]
    by_cases hbpos : 0 < b
    · simp only [if_pos hbpos, sub_self, mul_zero, abs_of_pos hbpos]
      ring
    · have hbneg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb
      simp only [if_neg hbpos, sub_self, mul_zero, abs_of_neg hbneg]
      ring
  refine ⟨bufferCutGlue_weakDerivative c hUL hUR hDL.locallyIntegrable hDR.locallyIntegrable
    (fun x _ => bufferAffineBranch_hasDerivAt hL c k b x)
    (fun x _ => bufferAffineBranch_hasDerivAt hR c k b x) hULc hu' hd', ?_⟩
  intro φ hφ hcφ
  have h := bufferCutGlue_delta_energy hV c hDL hDR hRL.locallyIntegrable hRR.locallyIntegrable
    (fun x _ => bufferAffineBranch_second_hasDerivAt hL c k b x)
    (fun x _ => bufferAffineBranch_second_hasDerivAt hR c k b x) hd' hr' φ hφ hcφ
  rwa [hjump] at h

theorem positiveBuffer_delta_energy_of_integral_compact {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    (e : PositiveBufferEnergy V) (f : RadialL2) (c jump : ℝ)
    (hcompact : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ, positiveBufferEnergyCoordinate V 1 e x * deriv φ x) +
        (∫ x : ℝ, V x * positiveBufferEnergyCoordinate V 0 e x * φ x) =
          (∫ x : ℝ, f x * φ x) + jump * φ c)
    (v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV e v =
      inner (𝕜 := ℝ) f (positiveBufferEnergyCoordinate V 0 v) +
        jump * positiveBufferTraceAt V c v := by
  apply positiveBuffer_delta_energy_of_compact hreal hV e f c jump ?_ v
  intro φ hφ hcφ
  rw [positiveBufferEnergyForm_compact_right, positiveBufferL2_inner_integral]
  have hsource : (∫ x : ℝ, f x *
      positiveBufferEnergyCoordinate V 0 (positiveBufferCompactEnergyLift V hV φ hφ hcφ) x) =
        ∫ x : ℝ, f x * φ x := by
    apply integral_congr_ae
    filter_upwards [positiveBufferCompactEnergyLift_base_ae V hV φ hφ hcφ]
      with x hx using congrArg (fun a : ℝ => f x * a) hx
  rw [hsource]
  exact hcompact φ hφ hcφ
end ContinuousFlexibility.Radial
