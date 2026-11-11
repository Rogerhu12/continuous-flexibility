import ContinuousFlexibility.Analysis.N08ReferenceFlow
import ContinuousFlexibility.Analysis.N08StateProjection
import ContinuousFlexibility.Analysis.SolveResidualSpaces
import ContinuousFlexibility.Analysis.SolveTameSubspace

/-!
# The actual return residual in the even circle space

The odd candidate chart and its two inverse identities force the chosen
inverse chart to be odd.  The actual return residual is therefore even.
Restricting its codomain preserves the smooth tame tower supplied by N02.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base : ℕ} {ε : ℝ}

theorem n08_rightChartCandidate_odd (z : AnnularState S × ℝ) (m : ℕ) (θ : ℝ) :
    rightChartCandidate S C z m (-θ) = -rightChartCandidate S C z m θ := by
  simp only [rightChartCandidate, oddPart, neg_neg]
  ring

theorem n08_rightChartInverse_odd
    (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    C.rightChartInverse z m (-θ) = -C.rightChartInverse z m θ := by
  have hinj : Function.Injective (rightChartCandidate S C z m) :=
    Function.LeftInverse.injective
      (fun t => (hR.1 z hz hs m t).2.2.2.1)
  apply hinj
  rw [(hR.1 z hz hs m (-θ)).2.2.1, n08_rightChartCandidate_odd,
    (hR.1 z hz hs m θ).2.2.1]

theorem n08_returnResidualField_even
    (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    Function.Even (returnResidualField S C z m) := by
  intro θ
  simp only [returnResidualField, evenPart,
    n08_rightChartInverse_odd hR hz hs, neg_neg]
  ring

theorem n08_returnResidual_mem_even
    (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) : R.residual z ∈ evenCircleSubmodule S := by
  change ∀ m θ, (S.circle (3 / 4 : ℝ)).decode (R.residual z) m (-θ) =
    (S.circle (3 / 4 : ℝ)).decode (R.residual z) m θ
  intro m θ
  rw [hR.2.1 z hz hs m (-θ), hR.2.1 z hz hs m θ]
  exact n08_returnResidualField_even hR hz hs m θ

/-- The physical projection gives a representative on an open domain in
the full state space. Arbitrary control directions are retained through
their angular means. -/
def n08CircleResidual (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) : EvenCircle S := by
  classical
  exact if hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε then
    ⟨R.residual (n08_stateProjection hS z.1, z.2),
      n08_returnResidual_mem_even hR hz (n08_stateProjection_mem hS z.1)⟩
  else 0

theorem n08CircleResidual_projected_coe (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε) :
    (n08CircleResidual hS hR z).val = R.residual (n08_stateProjection hS z.1, z.2) := by
  unfold n08CircleResidual
  rw [dif_pos hz]

theorem n08CircleResidual_coe (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    (n08CircleResidual hS hR z).val = R.residual z := by
  have hp := n08_stateProjection_eq_self hS z.1 hs
  have hz' : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε := by
    simpa only [hp, Prod.eta] using hz
  rw [n08CircleResidual_projected_coe hS hR hz', hp, Prod.eta]

theorem n08CircleResidual_decode (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (n08CircleResidual hS hR z).val m θ =
      returnResidualField S C z m θ := by
  rw [n08CircleResidual_coe hS hR hz hs]
  exact hR.2.1 z hz hs m θ

/-- All actual directional jets remain in the closed even subspace;
the N02 tame estimates are retained with the inherited grading. -/
theorem n08CircleResidual_smoothTame
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    (hR : N02Properties D T S C R base ε) :
    SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (fun n => ((S.circle (3 / 4 : ℝ)).grading n).comp (evenCircleSubmodule S).subtype)
      (sectorNeighborhood S base ε ε)
      (fun z => n08CircleResidual hS hR (liftSectorParameter S C z)) := by
  have htame : SmoothTameOn (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ht⟩ := hR
    exact ht
  apply solve_smoothTameOn_codRestrict (evenCircleSubmodule S)
    (solve_isClosed_evenCircle hS) htame
  intro z hz
  exact n08CircleResidual_coe hS hR
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (href.liftSectorParameter_sector z)

end ContinuousFlexibility.Statements
