import ContinuousFlexibility.Analysis.N04PulledFieldsSampleTransport
import ContinuousFlexibility.Analysis.N04PulledFieldsSampleCost
import ContinuousFlexibility.Analysis.N04RealizationMaterialTransfer
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Physical coefficient costs at the retained sample

The positive physical height factor is transferred before it is bounded
above. At parameter order zero the uniform reference coefficient is
added separately. This avoids transferring an unweighted physical
envelope by a one-sided endpoint comparison.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

/-- Every full physical height cost at an actual inverse point has the
same sampled height exponent. The coefficient precedes every auxiliary
column, state, piece, and canonical point. -/
theorem n04PulledFields_sampledCoefficient_heightCost
    (G : N04RealizationGauge) {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    {C P : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∃ B : ℝ, 0 < B ∧
      ∀ η : (G.W.S.height (3 / 4 : ℝ)).Space,
      ∀ z ∈ sectorNeighborhood (G.S η) base ε ε, ∀ m q, q ∈ unitStrip →
        C * G.W.U.E0 (G.pulledPoint η (G.lift η z) m q).1 ^ P *
            G.W.U.H (G.pulledPoint η (G.lift η z) m q).1 ^ (3 / 4 : ℝ) ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B *
            G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) := by
  obtain ⟨L, hL, hpoint⟩ := n04PulledFields_pulledPoint_sample_endpointX G hadm
  obtain ⟨CW, A, hCW, hA, htransfer⟩ :=
    n04Realization_material_H_E0_rpow_oneSided
      (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT) G.W.radial.1
      (by norm_num : 0 < (3 / 4 : ℝ)) hP hL
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (C * CW) A
  refine ⟨B, hB, fun η z hz m q hq => ?_⟩
  have hp := hpoint η z hz m q hq
  have hw := htransfer (G.pulledPoint η (G.lift η z) m q).1
    (G.W.U.sample ((G.V η).cell m)) hp.1
    (n04PulledFields_sample_mem_interval G η m) hp.2
  have hH : 0 ≤ G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg ((G.cost_nonneg η).2.1 m) _
  calc
    _ = C * (G.W.U.H (G.pulledPoint η (G.lift η z) m q).1 ^ (3 / 4 : ℝ) *
        G.W.U.E0 (G.pulledPoint η (G.lift η z) m q).1 ^ P) := by ring
    _ ≤ C * (CW * G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) *
        G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A) :=
      mul_le_mul_of_nonneg_left hw hC
    _ = ((C * CW) * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ A) *
        G.W.U.H (G.W.U.sample ((G.V η).cell m)) ^ (3 / 4 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hpack _ ((G.cost_nonneg η).2.2 m)) hH

/-- An unweighted uniform reference term is added only after the
current height-weighted term has reached the actual sample. -/
theorem n04PulledFields_referencePlusHeightCost
    {Cref C A L : ℝ} (hCref : 0 ≤ Cref) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ E H Q : ℝ, 1 ≤ E → 0 ≤ H → H ≤ L → 1 ≤ Q →
      Cref + C * E ^ A * H * Q ≤ B * E ^ B * Q := by
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (Cref + C * L) A
  refine ⟨B, hB, fun E H Q hE _ hHL hQ => ?_⟩
  have hpow : 1 ≤ E ^ A := Real.one_le_rpow hE hA
  have hreference : Cref ≤ Cref * E ^ A * Q := by
    have hprod : 1 ≤ E ^ A * Q := one_le_mul_of_one_le_of_one_le hpow hQ
    simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hprod hCref
  have hcurrent : C * E ^ A * H * Q ≤ C * E ^ A * L * Q :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHL
        (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hE) _)))
      (zero_le_one.trans hQ)
  calc
    _ ≤ Cref * E ^ A * Q + C * E ^ A * L * Q := add_le_add hreference hcurrent
    _ = (Cref + C * L) * E ^ A * Q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hpack E hE) (zero_le_one.trans hQ)

end ContinuousFlexibility.Analysis
