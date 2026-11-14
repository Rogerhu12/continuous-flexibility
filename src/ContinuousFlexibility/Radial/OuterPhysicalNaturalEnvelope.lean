module

public import ContinuousFlexibility.Radial.OuterTailPointwiseBounds
public import ContinuousFlexibility.Radial.OuterKernelEnvelopeAlgebra

/-!
# Uniform pointwise decay of the actual normalized natural solution

The reciprocal entrance gauge and the physical gauge are both bounded
on the actual short tail. This removes all frequency-dependent entrance
normalizations from the relative pointwise decay, including the initial
resistance interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

def outerPhysicalNaturalExponent (A : ℝ) : ℝ := 4 * exp 2 + outerPhysicalDecayCost A

theorem outerPhysicalNaturalExponent_pos {A : ℝ} (hA : 0 ≤ A) :
    0 < outerPhysicalNaturalExponent A :=
  add_pos_of_pos_of_nonneg (by positivity) (outerPhysicalDecayCost_nonneg hA)

theorem MorsePhysicalTailBasis.physical_natural_point_envelope
    {M : MorseChainData} {D : ReferenceData} {right : Bool} {j start : ℕ}
    {entrance η K : ℝ}
    (F : MorsePhysicalTailBasis M D right j start entrance η K)
    (hD : RadialProfileGeometry D) (hentry : 0 < entrance)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    (hη : η ≤ 1 / 16) (hK : 32 ≤ K) (hj : 2 ≤ j) (hstart : 1 ≤ start)
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start entrance η K) right j start)
    (hclose : (morsePhysicalDeepTail M D right j start entrance η K).endpoint -
      (morsePhysicalDeepTail M D right j start entrance η K).entrance ≤
        (2 * (j : ℝ) ^ 2)⁻¹)
    {A : ℝ} (hA : 0 ≤ A)
    (hden : ∀ k, exp (2 * ((start + k : ℕ) : ℝ) ^ 2 -
      A * (((start + k : ℕ) : ℝ) ^ (3 / 2 : ℝ) + (start + k : ℕ))) ≤
        (morsePhysicalDeepTail M D right j start entrance η K).Λ *
          tailMass (morsePhysicalDeepTail M D right j start entrance η K) (k + 1) *
          tailResistance (morsePhysicalDeepTail M D right j start entrance η K) k)
    {n : ℕ} {x : ℝ}
    (hx : OuterTailPoint (morsePhysicalDeepTail M D right j start entrance η K) n x) :
    |F.P (outerOutwardLogRadius right x)| ≤
      radialE (start + n) ^ outerPhysicalNaturalExponent A *
        exp (-|radialS (start + n) - radialS start|) := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let W := radialE (start + n) ^ outerPhysicalDecayCost A *
    exp (-|radialS (start + n) - radialS start|)
  have hW : 0 ≤ W := mul_nonneg
    (rpow_nonneg (show 0 ≤ radialE (start + n) from (exp_pos _).le) _) (exp_pos _).le
  have hcost := outerPhysicalDecayCost_nonneg hA
  have he := F.logP_entry_abs_le hD hentry hj hT hphysical hclose
  have hlog : |F.logP x| ≤ 4 * |F.logP (tailPhysicalLog right entrance)| * W := by
    rcases hx with ⟨rfl, hx⟩ | hx
    · have hi := F.logP_initial_bound hT hη hK hx
      have hE := outer_envelope_one_le start hcost
      have hh := hi.trans (le_mul_of_one_le_right
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg _)) hE)
      change |F.logP x| ≤ 4 * |F.logP (tailPhysicalLog right entrance)| *
        radialE start ^ outerPhysicalDecayCost A at hh
      simpa only [W, Nat.add_zero, sub_self, abs_zero, neg_zero, exp_zero, mul_one] using hh
    · exact F.logP_edge_envelope hT hη hK hA hden n hx
  have hphys := outer_tail_physical_lift_bound hD hj hphysical hclose
    (outerTailPoint_mem hT hx) hlog
  have he2 : exp 1 * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  change |outerTailOutwardLift D right j F.logP (outerOutwardLogRadius right x)| ≤ _
  calc
    _ ≤ exp 1 * (4 * |F.logP (tailPhysicalLog right entrance)| * W) := hphys
    _ ≤ exp 1 * (4 * exp 1 * W) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hW)
      (exp_pos 1).le
    _ = 4 * (exp 1 * exp 1) * W := by ring
    _ = (4 * exp 2 * radialE (start + n) ^ outerPhysicalDecayCost A) *
        exp (-|radialS (start + n) - radialS start|) := by rw [he2]; dsimp only [W]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (outer_envelope_prefactor (hstart.trans (Nat.le_add_right start n))
        (by positivity : 0 ≤ 4 * exp 2)) (exp_pos _).le

/-- Moving the entrance reference from the first tail label to the core
label changes only a coefficient power, preserving the full exponent. -/
theorem outer_attenuation_from_core {N p : ℕ} (hN : 1 ≤ N) (hp : N + 1 ≤ p) :
    exp (-|radialS p - radialS (N + 1)|) ≤
      radialE p ^ (18 : ℝ) * exp (-|radialS p - radialS N|) := by
  have hnear := outer_radialS_nearby_bound (show 1 ≤ N + 1 by omega) hN
    (show N + 1 ≤ N + 2 by omega) (show N ≤ N + 1 + 2 by omega)
  have hQ : 18 * radialQ N ≤ 18 * radialQ p :=
    mul_le_mul_of_nonneg_left (radialQ_monotone (by omega : N ≤ p)) (by norm_num)
  have htri := abs_sub_le (radialS p) (radialS (N + 1)) (radialS N)
  rw [outer_radialE_rpow, ← exp_add]
  exact exp_le_exp.mpr (by linarith only [hnear, hQ, htri])

end ContinuousFlexibility.Radial
