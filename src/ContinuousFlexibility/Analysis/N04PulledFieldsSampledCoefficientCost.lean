module

public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleTransport
public import ContinuousFlexibility.Analysis.N04PulledFieldsSampleCost
public import ContinuousFlexibility.Analysis.N04RealizationMaterialTransfer
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Physical coefficient costs at the retained sample

The positive physical height factor is transferred before it is bounded
above. At parameter order zero the uniform reference coefficient is
added separately. This avoids transferring an unweighted physical
envelope by a one-sided endpoint comparison.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

/-- Pack the one-sided material transfer before introducing the gauge's
dependent state space or its actual inverse-point maps. -/
theorem n04PulledFields_material_heightCost
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    {C P L : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∀ r s : ℝ,
      r ∈ Ioo D.a D.b → s ∈ Ioo D.a D.b → 1 ≤ T.E0 s →
      endpointX 1 (Statements.endpointDistance D s) ≤
        endpointX 1 (Statements.endpointDistance D r) + L →
      C * T.E0 r ^ P * T.H r ^ (3 / 4 : ℝ) ≤
        B * T.E0 s ^ B * T.H s ^ (3 / 4 : ℝ) := by
  obtain ⟨CW, A, _, _, htransfer⟩ :=
    n04Realization_material_H_E0_rpow_oneSided hT hRef
      (by norm_num : 0 < (3 / 4 : ℝ)) hP hL
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (C * CW) A
  refine ⟨B, hB, fun r s hr hs hE hdist => ?_⟩
  have hw := htransfer r s hr hs hdist
  have hH : 0 ≤ T.H s ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 s hs).2.1.le _
  calc
    _ = C * (T.H r ^ (3 / 4 : ℝ) * T.E0 r ^ P) := by ring
    _ ≤ C * (CW * T.H s ^ (3 / 4 : ℝ) * T.E0 s ^ A) :=
      mul_le_mul_of_nonneg_left hw hC
    _ = ((C * CW) * T.E0 s ^ A) * T.H s ^ (3 / 4 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hpack (T.E0 s) hE) hH

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
  let pointData := n04PulledFields_pulledPoint_sample_endpointX G
    (base := base) (ε := ε) hadm
  let costData := n04PulledFields_material_heightCost
    (isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT) G.W.radial.1
    hC hP pointData.choose_spec.1
  refine ⟨costData.choose, costData.choose_spec.1, fun η z hz m q hq => ?_⟩
  have hp := pointData.choose_spec.2 η z hz m q hq
  exact costData.choose_spec.2 (G.pulledPoint η (G.lift η z) m q).1
    (G.W.U.sample ((G.V η).cell m)) hp.1
    (n04PulledFields_sample_mem_interval G η m) ((G.cost_nonneg η).2.2 m) hp.2

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
