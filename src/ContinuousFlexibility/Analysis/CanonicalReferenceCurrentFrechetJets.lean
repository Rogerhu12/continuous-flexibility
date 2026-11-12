import ContinuousFlexibility.Analysis.CanonicalReferenceCurrentAbsoluteJets
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Actual unit-atom Frechet jets with the original fixed state loss

The current certificate already supplies smoothness on the actual unit
strip. The mixed envelope is chosen once at order N and used for every
Frechet order k at most N, retaining its sample, exponent and state order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

/-- A single loss precedes N, and the same A and B control all k at most N. -/
theorem n04Coordinates_unitAtom_absolute_iteratedFDeriv_envelope
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m)))
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ loss : ℕ, ∀ N : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m v p,
        p ∈ CanonicalGeometry.unitStrip → ∀ k : ℕ, k ≤ N →
          ‖iteratedFDeriv ℝ k
            (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v) p‖ ≤
            (2 : ℝ) ^ N * A * T.E0 (T.sample (K.cell m)) ^ B *
              (1 + CanonicalGeometry.parameterGrading S (N + loss) z) := by
  obtain ⟨loss, hbound⟩ :=
    n04Coordinates_unitAtom_absolute_envelope hD hT hfloor href hcur
  refine ⟨loss, fun N => ?_⟩
  obtain ⟨A, B, hA, hB, hb⟩ := hbound N
  refine ⟨A, B, hA, hB, ?_⟩
  intro z hz m v p hp k hk
  let M : ℝ := A * T.E0 (T.sample (K.cell m)) ^ B *
    (1 + CanonicalGeometry.parameterGrading S (N + loss) z)
  have hM : 0 ≤ M :=
    mul_nonneg (mul_nonneg hA.le
      (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) B))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  have hf : ContDiffOn ℝ ∞
      (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v)
      CanonicalGeometry.unitStrip := (hcur.1 z hz m v).1
  have hj := norm_iteratedFDeriv_le_of_mixedDerivative
    (show IsOpen CanonicalGeometry.unitStrip from isOpen_Ioo.prod isOpen_univ)
    hf k hp hM (fun i j hij => by
      simpa only [Real.norm_eq_abs] using hb z hz m v p hp i j (hij.le.trans hk))
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ N :=
    pow_le_pow_right₀ (by norm_num) hk
  exact hj.trans ((mul_le_mul_of_nonneg_right hpow hM).trans_eq (by
    dsimp only [M]
    ring))

end ContinuousFlexibility.Analysis
