import ContinuousFlexibility.Analysis.N06PrimitiveActualJetIdentities
import ContinuousFlexibility.Analysis.N06MaterialAbsorption

/-!
# Primitive geometric jets give the actual relative jets

This uses only the zeroth state-derivative clause of `CurrentJets`.
All radial interval factors are retained, and their fixed finite cost is
absorbed into one coefficient exponent by the two reference length atoms.
The original material hypothesis absorbs the scalar-column weight. The
result applies to every finite set of pieces, chosen after the constants.
No N06 inverse or relative operator estimate is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- A literal unit-strip identity is the only field-specific input to
this rescaling estimate; no new candidate coefficient is introduced. -/
theorem n06_primitive_canonicalDifference_jet_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : referenceStateConditions D S C)
    (hreference : ReferenceJets D T S C L K)
    (hcurrent : CurrentJets D T S C L K base ε)
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ d : ℕ, ∀ n : ℕ, ∃ A Q : ℝ, 0 < A ∧ 0 < Q ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m a (f : PolarPoint → ℝ),
      EqOn (f ∘ canonicalUnitPoint K m)
        (fun q => atom D T S C L K z m a q -
          atom D T S C L K (C.referenceState, 0) m a q) unitStrip →
      ∀ i j : ℕ, i + j ≤ n → ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative i j f p| ≤
          (Q * (stateGrading S (n + d) (z.1 - C.referenceState) + |z.2|)) *
            (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              T.E0 (T.sample (K.cell m)) ^ A) := by
  obtain ⟨P, hP, hlength⟩ := n06_referenceCanonicalLength_envelope hreference hlen
  obtain ⟨d, hd⟩ := n06_primitive_currentAtom_difference_jets href hcurrent
  refine ⟨d, fun n => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hd n
  refine ⟨B + P * n, B * P ^ n,
    add_pos_of_pos_of_nonneg hB (mul_nonneg hP.le (Nat.cast_nonneg n)),
    mul_pos hB (pow_pos hP n), ?_⟩
  intro z hz hs m a f heq i j hij p hp
  let q := n07aCanonicalUnitInversePoint K m p
  have hq : q ∈ unitStrip := n07aCanonicalUnitInversePoint_maps (hlen m) hp
  have hsample := spaces_trace_sample_mem hD hT (K.cell m)
  have hE : 0 < T.E0 (T.sample (K.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hH : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 _ hsample).2.1.le _
  have hrho : 0 ≤ stateGrading S (n + d) (z.1 - C.referenceState) + |z.2| :=
    add_nonneg (apply_nonneg (stateGrading S (n + d)) _) (abs_nonneg _)
  have hjet := hbound z hz hs m a q hq i j hij
  rw [n06_mixedJet_of_unit_identity m (hlen m) heq i j hp]
  exact n06_inverseLength_weighted_jet_bound (sub_pos.mpr (hlen m)) hE hH
    hB.le hP.le hrho (by omega : i ≤ n) (hlength m).1 (hlength m).2.2 hjet

private theorem n06_primitive_weighted_bound_enlarge
    {Q C rho w v : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hw : 0 ≤ w) (hv : |v| ≤ Q * rho * w) :
    |v| ≤ Q * (1 + C) * rho * w := by
  apply hv.trans
  apply mul_le_mul_of_nonneg_right _ hw
  apply mul_le_mul_of_nonneg_right _ hrho
  have hone : (1 : ℝ) ≤ 1 + C := le_add_of_nonneg_right hC
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hone hQ

private theorem n06_primitive_weighted_bound_absorb
    {Q C rho w v : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hw : w ≤ C) (hv : |v| ≤ Q * rho * w) :
    |v| ≤ Q * (1 + C) * rho := by
  calc
    |v| ≤ Q * rho * w := hv
    _ ≤ Q * rho * C := mul_le_mul_of_nonneg_left hw (mul_nonneg hQ hrho)
    _ ≤ Q * (1 + C) * rho := by
      have hnonneg := mul_nonneg hQ hrho
      nlinarith only [hnonneg]

/-- The exact jet input of the existing relative-operator assembly now
follows from the primitive construction-stage clauses. The neighborhood,
atlas, volume model and graph need not be changed. The estimate is uniform
over the finite piece set, which is selected later by the support argument. -/
theorem n06_exists_actualRelativeJetBounds_of_primitive
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hreference : ReferenceJets D T S C L K)
    (hcurrent : CurrentJets D T S C L K base ε) (b : ℕ) :
    ∃ order : ℕ, ∃ A Cjet : ℝ, 0 < A ∧ 0 < Cjet ∧
      ∀ I : Finset ℕ, ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        N06ActualRelativeJetBounds D T S C L K b A I
          (Cjet * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) z := by
  obtain ⟨d, hd⟩ := n06_primitive_canonicalDifference_jet_bound h01.1.1 hT
    h01.2.2.1 hreference hcurrent (fun m => (h04.1.referenceBounds m).2.1)
  obtain ⟨A, Q, hA, hQ, hbound⟩ := hd (b + 1)
  obtain ⟨Cabs, hCabs, habs⟩ := n06_material_loss_absorb hT (3 / 4 : ℝ) A 0 (by norm_num)
  have hCjet : 0 < Q * (1 + Cabs) := mul_pos hQ (by linarith only [hCabs])
  refine ⟨b + 1 + d, A, Q * (1 + Cabs), hA, hCjet, ?_⟩
  intro I z hz hs
  have hrho : 0 ≤ stateGrading S (b + 1 + d) (z.1 - C.referenceState) + |z.2| :=
    add_nonneg (apply_nonneg (stateGrading S (b + 1 + d)) _) (abs_nonneg _)
  have hweight (m : ℕ) :
      0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (K.cell m)) ^ A := by
    have hpos := hT.2.1 _ (spaces_trace_sample_mem h01.1.1 hT (K.cell m))
    exact mul_nonneg (Real.rpow_nonneg hpos.2.1.le _)
      (Real.rpow_nonneg hpos.2.2.1.le _)
  refine ⟨?_, ?_, ?_⟩
  · intro m hm a j haj p hp
    have he := n06_primitive_divided_unit_identities h01 h04 z hm
    refine ⟨?_, ?_, ?_⟩
    · exact n06_primitive_weighted_bound_enlarge hQ.le hCabs.le hrho (hweight m)
        (hbound z hz hs m .dividedA _ he.1 a j haj p hp)
    · exact n06_primitive_weighted_bound_enlarge hQ.le hCabs.le hrho (hweight m)
        (hbound z hz hs m .dividedB _ he.2.1 a j haj p hp)
    · exact n06_primitive_weighted_bound_enlarge hQ.le hCabs.le hrho (hweight m)
        (hbound z hz hs m .dividedC _ he.2.2 a j haj p hp)
  · intro m j hj p hp
    have h := n06_primitive_weighted_bound_enlarge hQ.le hCabs.le hrho (hweight m)
      (hbound z hz hs m .potential _ (n06_primitive_potential_unit_identity z m)
        0 j (by omega) p hp)
    simpa only [mul_assoc] using h
  · intro i m _ j hj p hp
    have hw : T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (K.cell m)) ^ A ≤ Cabs := by
      simpa only [Real.rpow_zero, mul_one] using
        habs _ (spaces_trace_sample_mem h01.1.1 hT (K.cell m))
    exact n06_primitive_weighted_bound_absorb hQ.le hCabs.le hrho hw
      (hbound z hz hs m (![.leftColumn, .nuColumn, .auxiliaryColumn] i) _
        (n06_primitive_column_unit_identity hS h01 h03 h04 z i m)
        0 j (by omega) p hp)

end ContinuousFlexibility.Statements
