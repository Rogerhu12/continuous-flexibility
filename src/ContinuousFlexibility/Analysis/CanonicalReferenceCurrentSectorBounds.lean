import ContinuousFlexibility.Analysis.CanonicalReferenceCurrentAbsoluteJets
import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds
import ContinuousFlexibility.Analysis.N07aScalarSolution
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.CanonicalCoordinateCompletion

/-!
# The actual potential and divided estimates from primitive jets

The inverse canonical affine scale has its own reference atom. Its cost
changes the material exponent, while the state loss stays fixed. Four
literal atoms then give the exact sector estimate on the same atlas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

private theorem n04Coordinates_inverse_affine_power_cost
    {c E B : ℝ} (hc : 0 ≤ c) (hE : 1 ≤ E) (hB : 0 ≤ B)
    (hbound : c ≤ B * E ^ B) {i s : ℕ} (hi : i ≤ s) :
    c ^ i ≤ (1 + B) ^ s * E ^ (B * (s : ℝ)) := by
  let W : ℝ := (1 + B) * E ^ B
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hW : 1 ≤ W := by
    have h := mul_le_mul (show (1 : ℝ) ≤ 1 + B by linarith)
      (Real.one_le_rpow hE hB) (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ 1 + B)
    simpa only [one_mul] using h
  have hcW : c ≤ W := hbound.trans
    (mul_le_mul_of_nonneg_right (by linarith : B ≤ 1 + B)
      (Real.rpow_nonneg hE0 B))
  calc
    c ^ i ≤ W ^ i := pow_le_pow_left₀ hc hcW i
    _ ≤ W ^ s := pow_le_pow_right₀ hW hi
    _ = (1 + B) ^ s * E ^ (B * (s : ℝ)) := by
      dsimp only [W]
      rw [mul_pow, Real.rpow_mul_natCast hE0]

/-- Every genuine unit atom has the explicit original-coordinate cost. -/
theorem n04Coordinates_canonicalAtom_absolute_envelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m v y,
        y ∈ canonicalOpen S K m → ∀ i j : ℕ, i + j ≤ s →
          |mixedDerivative i j (n07aCanonicalAtomField D T S C L K v z m) y| ≤
            A * T.E0 (T.sample (K.cell m)) ^ B *
              (1 + CanonicalGeometry.parameterGrading S (s + loss) z) := by
  have hunitBounds := n04Coordinates_unitAtom_absolute_envelope
    (D := D) (T := T) (S := S) (C := C) (L := L) (K := K)
    (base := base) (ε := ε) hD hT hfloor href hcur
  let loss : ℕ := hunitBounds.choose
  have hunit := hunitBounds.choose_spec
  have hlengthBounds := n04Coordinates_reference_canonicalLengthInverse_envelope href
  let BL : ℝ := hlengthBounds.choose
  have hBL : 0 < BL := hlengthBounds.choose_spec.1
  have hlength := hlengthBounds.choose_spec.2
  refine ⟨loss, fun s => ?_⟩
  let A : ℝ := (hunit s).choose
  let B : ℝ := (hunit s).choose_spec.choose
  have hA : 0 < A := (hunit s).choose_spec.choose_spec.1
  have hB : 0 < B := (hunit s).choose_spec.choose_spec.2.1
  have hjets := (hunit s).choose_spec.choose_spec.2.2
  let A' : ℝ := (1 + BL) ^ s * A
  let B' : ℝ := BL * (s : ℝ) + B
  have hA' : 0 < A' := mul_pos (pow_pos (by linarith : 0 < 1 + BL) _) hA
  have hB' : 0 < B' := add_pos_of_nonneg_of_pos
    (mul_nonneg hBL.le (Nat.cast_nonneg s)) hB
  refine ⟨A', B', hA', hB', ?_⟩
  intro z hz m v y hy i j hij
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let G : ℝ := CanonicalGeometry.parameterGrading S (s + loss) z
  have hE : 1 ≤ E := hfloor m
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hc : 0 ≤ (K.right m - K.left m)⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr (hinterval m)).le
  have hpow := n04Coordinates_inverse_affine_power_cost hc hE hBL.le
    ((le_abs_self _).trans (hlength m)) (show i ≤ s by omega)
  have hx := n07aCanonicalUnitInversePoint_maps (hinterval m) hy
  have hj := hjets z hz m v (n07aCanonicalUnitInversePoint K m y) hx i j hij
  have hcost : 0 ≤ (1 + BL) ^ s * E ^ (BL * (s : ℝ)) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hE0 _)
  change |mixedDerivative i j
    (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v ∘
      n07aCanonicalUnitInversePoint K m) y| ≤ _
  rw [n07a_mixedDerivative_unitInverse, abs_mul, abs_of_nonneg (pow_nonneg hc i)]
  calc
    _ ≤ ((1 + BL) ^ s * E ^ (BL * (s : ℝ))) *
        (A * E ^ B * (1 + G)) := mul_le_mul hpow hj (abs_nonneg _) hcost
    _ = A' * E ^ B' * (1 + G) := by
      dsimp only [A', B']
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ring

theorem n04Coordinates_sectorParameterOfState_grading
    (href : referenceStateConditions D S C) (s : ℕ)
    (z : AnnularState S × ℝ) (hs : stateSector S z.1) :
    CanonicalGeometry.parameterGrading S s (n07aSectorParameterOfState href z hs) =
      stateGrading S s (z.1 - C.referenceState) + |z.2| := by
  simp only [CanonicalGeometry.parameterGrading, pairGrading_apply, sectorGrading,
    Seminorm.comp_apply, Submodule.subtype_apply, n07aSectorParameterOfState,
    realGrading, coe_normSeminorm, Real.norm_eq_abs]

/-- Reference and actual current jets supply the exact four-field sector
estimate, including order zero, with the original fixed state loss. -/
theorem n04Coordinates_sectorCanonicalJetBounds_of_reference_current
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (hstate : referenceStateConditions D S C)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m) :
    ∃ loss : ℕ, SectorCanonicalJetBounds T S C K base loss ε := by
  have hrawBounds := n04Coordinates_canonicalAtom_absolute_envelope
    (D := D) (T := T) (S := S) (C := C) (L := L) (K := K)
    (base := base) (ε := ε) hD hT hfloor href hcur hinterval
  let loss : ℕ := hrawBounds.choose
  have hraw := hrawBounds.choose_spec
  refine ⟨loss, fun s => ?_⟩
  let A : ℝ := (hraw s).choose
  let B : ℝ := (hraw s).choose_spec.choose
  have hA : 0 < A := (hraw s).choose_spec.choose_spec.1
  have hB : 0 < B := (hraw s).choose_spec.choose_spec.2.1
  have hjets := (hraw s).choose_spec.choose_spec.2.2
  obtain ⟨Q, hQ, hpack⟩ := coefficientEnvelope_pack (4 * A) B
  refine ⟨Q, hQ, ?_⟩
  intro z hz hs m y hy i j hij
  let w := n07aSectorParameterOfState hstate z hs
  have hw : w ∈ sectorNeighborhood S base ε ε :=
    n07aSectorParameterOfState_mem hstate hz hs
  have hwLift : liftSectorParameter S C w = z :=
    lift_n07aSectorParameterOfState hstate z hs
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let G : ℝ := CanonicalGeometry.parameterGrading S (s + loss) w
  let V : ℝ := A * E ^ B * (1 + G)
  have hG : 0 ≤ G := apply_nonneg _ _
  have hV : 0 ≤ V := mul_nonneg
    (mul_nonneg hA.le (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) _))
    (add_nonneg zero_le_one hG)
  have hpotential : |mixedDerivative i j (K.potential z m) y| ≤ V := by
    simpa only [V, A, B, E, G, loss, n07aCanonicalAtomField, Function.comp_def, CanonicalGeometry.atom,
      hwLift, n07aCanonicalUnitPoint_inverse (hinterval m)] using
      hjets w hw m .potential y hy i j hij
  have hfour : |mixedDerivative i j (K.potential z m) y| +
      (if K.positive m = true then
        |mixedDerivative i j (K.dividedDifference z m).a y| +
        |mixedDerivative i j (K.dividedDifference z m).b y| +
        |mixedDerivative i j (K.dividedDifference z m).c y| else 0) ≤ 4 * V := by
    by_cases hpos : K.positive m = true
    · have ha : |mixedDerivative i j (K.dividedDifference z m).a y| ≤ V := by
        simpa only [V, A, B, E, G, loss, n07aCanonicalAtomField, Function.comp_def, CanonicalGeometry.atom,
          hwLift, if_pos hpos, n07aCanonicalUnitPoint_inverse (hinterval m)] using
          hjets w hw m .dividedA y hy i j hij
      have hb : |mixedDerivative i j (K.dividedDifference z m).b y| ≤ V := by
        simpa only [V, A, B, E, G, loss, n07aCanonicalAtomField, Function.comp_def, CanonicalGeometry.atom,
          hwLift, if_pos hpos, n07aCanonicalUnitPoint_inverse (hinterval m)] using
          hjets w hw m .dividedB y hy i j hij
      have hc : |mixedDerivative i j (K.dividedDifference z m).c y| ≤ V := by
        simpa only [V, A, B, E, G, loss, n07aCanonicalAtomField, Function.comp_def, CanonicalGeometry.atom,
          hwLift, if_pos hpos, n07aCanonicalUnitPoint_inverse (hinterval m)] using
          hjets w hw m .dividedC y hy i j hij
      rw [if_pos hpos]
      linarith
    · rw [if_neg hpos]
      linarith
  have hpacked : 4 * V ≤ Q * E ^ Q * (1 + G) := by
    calc
      4 * V = ((4 * A) * E ^ B) * (1 + G) := by dsimp only [V]; ring
      _ ≤ Q * E ^ Q * (1 + G) :=
        mul_le_mul_of_nonneg_right (hpack E (hfloor m)) (add_nonneg zero_le_one hG)
  have hgrading : G = stateGrading S (s + loss) (z.1 - C.referenceState) + |z.2| :=
    n04Coordinates_sectorParameterOfState_grading hstate (s + loss) z hs
  have h := hfour.trans hpacked
  simpa only [loss, hgrading, add_assoc] using h

end ContinuousFlexibility.Analysis
