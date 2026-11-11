import ContinuousFlexibility.Analysis.N04bFieldRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The actual characteristic speeds of the corrected field

The drift and positive half-gap are defined from the actual three
coefficient functions. Their smoothness, type, periodicity and reflection
follow from raw field regularity and the cumulative N03 symmetry. The
coefficient factorization used by characteristic coordinates is a
consequence, rather than an independent assumption.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

def n04bCharacteristicDrift (A : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  A.b p / A.a p

def n04bCharacteristicHalfGap (A : SymmetricCoefficients) (p : PolarPoint) : ℝ :=
  Real.sqrt (A.b p ^ 2 - A.a p * A.c p) / A.a p

theorem n04b_characteristic_coefficients
    (A : SymmetricCoefficients) {p : PolarPoint}
    (ha : A.a p ≠ 0) (hdisc : 0 ≤ A.b p ^ 2 - A.a p * A.c p) :
    A.b p = A.a p * n04bCharacteristicDrift A p ∧
      A.c p = A.a p *
        (n04bCharacteristicDrift A p ^ 2 - n04bCharacteristicHalfGap A p ^ 2) := by
  have hsq := Real.sq_sqrt hdisc
  dsimp only [n04bCharacteristicDrift, n04bCharacteristicHalfGap]
  constructor
  · field_simp [ha]
    <;> ring
  · rw [div_pow, div_pow, hsq]
    field_simp [ha]
    <;> ring

theorem n04b_characteristic_speed_factorization
    (A : SymmetricCoefficients) (p : PolarPoint) :
    minusCharacteristicSpeed A p =
        n04bCharacteristicDrift A p - n04bCharacteristicHalfGap A p ∧
      plusCharacteristicSpeed A p =
        n04bCharacteristicDrift A p + n04bCharacteristicHalfGap A p := by
  constructor <;> rfl

theorem n04b_characteristic_halfGap_pos
    (A : SymmetricCoefficients) {p : PolarPoint}
    (ha : 0 < A.a p) (hdisc : 0 < A.b p ^ 2 - A.a p * A.c p) :
    0 < n04bCharacteristicHalfGap A p :=
  div_pos (Real.sqrt_pos.mpr hdisc) ha

theorem n04b_characteristic_contDiffAt
    (A : SymmetricCoefficients) {p : PolarPoint}
    (ha : ContDiffAt ℝ ∞ A.a p)
    (hb : ContDiffAt ℝ ∞ A.b p)
    (hc : ContDiffAt ℝ ∞ A.c p)
    (ha0 : A.a p ≠ 0) (hdisc : 0 < A.b p ^ 2 - A.a p * A.c p) :
    ContDiffAt ℝ ∞ (n04bCharacteristicDrift A) p ∧
      ContDiffAt ℝ ∞ (n04bCharacteristicHalfGap A) p ∧
      ContDiffAt ℝ ∞ (minusCharacteristicSpeed A) p ∧
      ContDiffAt ℝ ∞ (plusCharacteristicSpeed A) p := by
  have hd : ContDiffAt ℝ ∞ (n04bCharacteristicDrift A) p := hb.div ha ha0
  have hv : ContDiffAt ℝ ∞ (n04bCharacteristicHalfGap A) p :=
    (((hb.pow 2).sub (ha.mul hc)).sqrt hdisc.ne').div ha ha0
  exact ⟨hd, hv, hd.sub hv, hd.add hv⟩

theorem n04b_characteristic_periodic
    (A : SymmetricCoefficients) (r P : ℝ)
    (ha : Function.Periodic (fun θ => A.a (r, θ)) P)
    (hb : Function.Periodic (fun θ => A.b (r, θ)) P)
    (hc : Function.Periodic (fun θ => A.c (r, θ)) P) :
    Function.Periodic (fun θ => n04bCharacteristicDrift A (r, θ)) P ∧
      Function.Periodic (fun θ => n04bCharacteristicHalfGap A (r, θ)) P := by
  constructor
  · intro θ
    dsimp only [n04bCharacteristicDrift]
    rw [ha θ, hb θ]
  · intro θ
    dsimp only [n04bCharacteristicHalfGap]
    rw [ha θ, hb θ, hc θ]

theorem n04b_characteristic_reflection
    (A : SymmetricCoefficients) (r θ : ℝ)
    (ha : A.a (r, -θ) = A.a (r, θ))
    (hb : A.b (r, -θ) = -A.b (r, θ))
    (hc : A.c (r, -θ) = A.c (r, θ)) :
    n04bCharacteristicDrift A (r, -θ) = -n04bCharacteristicDrift A (r, θ) ∧
      n04bCharacteristicHalfGap A (r, -θ) = n04bCharacteristicHalfGap A (r, θ) ∧
      minusCharacteristicSpeed A (r, -θ) = -plusCharacteristicSpeed A (r, θ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [n04bCharacteristicDrift, ha, hb, neg_div]
  · simp only [n04bCharacteristicHalfGap, ha, hb, hc, neg_sq]
  · simp only [minusCharacteristicSpeed, plusCharacteristicSpeed,
      ha, hb, hc, neg_sq, neg_div]
    ring

/-- Raw field regularity gives smooth actual speeds at every point of the
entire negative component, not only on an active correction collar. -/
theorem n04b_corrected_characteristics_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ)
    {p : PolarPoint} (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    ContDiffAt ℝ ∞ (n04bCharacteristicDrift (L.coefficients z)) p ∧
      ContDiffAt ℝ ∞ (n04bCharacteristicHalfGap (L.coefficients z)) p ∧
      ContDiffAt ℝ ∞ (minusCharacteristicSpeed (L.coefficients z)) p ∧
      ContDiffAt ℝ ∞ (plusCharacteristicSpeed (L.coefficients z)) p := by
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1.1,
      hp.1.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hreg := hfield.smooth_coefficients z hz hs
  have hnhds := (isOpen_Ioo.prod isOpen_univ).mem_nhds hpD
  exact n04b_characteristic_contDiffAt (L.coefficients z)
    (hreg.1.contDiffAt hnhds) (hreg.2.1.contDiffAt hnhds)
    (hreg.2.2.contDiffAt hnhds) (hfield.positive_a z hz hs p hpD).ne'
    (hfield.negative_discriminant z hz hs m p hp)

end ContinuousFlexibility.Analysis
