import ContinuousFlexibility.Analysis.N01JetBounds
import ContinuousFlexibility.Analysis.N01CommonRootCharacteristicStrip
import ContinuousFlexibility.Analysis.CanonicalFieldJetReduction
import ContinuousFlexibility.Analysis.ReferenceCircleFlow

/-!
# Actual coefficient values and spatial regularity from N01

The zeroth variation bound in the frozen N01 clause is a spatial jet
bound for the actual difference from the reference coefficients.
Its existing common base and loss are retained exactly. Positivity
in the same sector neighborhood also gives actual coefficient
smoothness throughout the physical annulus.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def N01CoefficientValueBoundAtOrder (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (s : ℕ) (B : ℝ) : Prop :=
  ∀ m i a b q, a + b ≤ s → q.1 ∈ D.cells m →
    ∀ z ∈ stateNeighborhood S C base ε,
      |coefficientFamily D S C i a b q z| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (1 + pairGrading (stateGrading S) realGrading (s + loss)
            (z - (C.referenceState, 0)))

/-- No first-variation integration or state-dependent choice of the loss
is needed for the zeroth variation of the actual coefficient family. -/
theorem coefficientFamily_value_bound_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ N01CoefficientValueBoundAtOrder D T S C base loss ε s B := by
  obtain ⟨B, hB, hbound⟩ := (n01CoefficientJetBounds_of_properties hN) 0 s
  refine ⟨B, hB, ?_⟩
  intro m i a b q hab hq z hz
  obtain ⟨J, hJ⟩ := hbound m i a b q hab hq
  have hj := hJ z hz Fin.elim0
  rw [J.zero z hz] at hj
  simpa only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero] using hj

/-- Every selected original coefficient is genuinely smooth in physical
coordinates on the original common sector neighborhood. -/
theorem contDiffOn_originalCoefficientComponent_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) :
    ContDiffOn ℝ ∞
      (canonicalCoefficientComponent i (originalCoefficients D S C z)) (annularOpen D) := by
  obtain ⟨_, hD⟩ := hN.1.1
  have ha : 0 < D.a := hD.1.1
  have hwref : ∀ r ∈ Ioo D.a D.b, 0 < D.w r := hD.1.2.2.2.2.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  intro q hq
  have hlow := hN.2.2.2.2.2.2.2.2.2.1 z hz hsector q hq
  have hwp : 0 < stateProfile D S C z.1 q.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (hwref q.1 hq.1)).trans_le
      ((le_div_iff₀ (hwref q.1 hq.1)).mp hlow.1)
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) q)
      (heightRadial (stateHeight D S C z) q)
      (angularPartial (heightAngular (stateHeight D S C z)) q) :=
    (mul_pos (by norm_num : (0 : ℝ) < 7 / 8) hwp).trans_le
      ((le_div_iff₀ hwp).mp hlow.2.2.1)
  have hdisc : 0 < polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) q :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlow.2.2.2.2.1
  have hs := contDiffAt_heightLinearCoefficients
    hw.contDiffAt hZ.contDiffAt (ha.trans hq.1.1).ne' hdisc hQ.ne'
  unfold canonicalCoefficientComponent
  split_ifs
  · exact hs.1.contDiffWithinAt
  · exact hs.2.1.contDiffWithinAt
  · exact hs.2.2.2.1.contDiffWithinAt

/-- At zero height parameter the actual reference coefficient fields
are angularly constant, with no hypothesis on an artificial extension. -/
theorem originalCoefficientComponent_zeroParameter_angle_invariant
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (x : AnnularState S) (i : Fin 3) (r θ ψ : ℝ) :
    canonicalCoefficientComponent i (originalCoefficients D S C (x, 0)) (r, θ) =
      canonicalCoefficientComponent i (originalCoefficients D S C (x, 0)) (r, ψ) := by
  have hh : stateHeight D S C (x, 0) =
      radialHeightField (stateRadialHeight D S C x) := by
    funext p
    simp only [stateHeight, zero_mul, add_zero, radialHeightField]
  obtain ⟨ha, hb, hc⟩ := polarCoefficients_radialHeightField_angular_invariant
    (stateProfile D S C x) (stateRadialHeight D S C x) r θ ψ
  unfold canonicalCoefficientComponent
  split_ifs
  · simpa only [originalCoefficients, hh] using ha
  · simpa only [originalCoefficients, hh] using hb
  · simpa only [originalCoefficients, hh] using hc

end ContinuousFlexibility.Analysis
