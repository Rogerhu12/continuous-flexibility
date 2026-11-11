import ContinuousFlexibility.Analysis.CircleJetClosedGraph
import ContinuousFlexibility.Analysis.SpacesCircleSpectral
import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Restricting the actual circle space to weighted control means

The zero jet of a physical circle model already contains the factor
`H_m ^ (-3/4)`.  Its normalized angular mean is a bounded L² functional;
applying it coordinate by coordinate therefore produces an actual ℓ²
control vector.  The exact decoding clause identifies its coordinates
with the manuscript's weighted angular means.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open ContinuousFlexibility.Statements

def n08ControlMeanConstant : ℝ := (1 / Real.pi) * Real.sqrt Real.pi

theorem n08ControlMeanConstant_pos : 0 < n08ControlMeanConstant :=
  mul_pos (div_pos zero_lt_one Real.pi_pos) (Real.sqrt_pos.mpr Real.pi_pos)

theorem n08ControlMeanConstant_nonneg : 0 ≤ n08ControlMeanConstant :=
  n08ControlMeanConstant_pos.le

private theorem n08_angularMean_eq_angleIntegral (f : ℝ → ℝ) :
    angularMean f = (1 / Real.pi) * ∫ θ, f θ ∂angleMeasure := by
  rw [angularMean, intervalIntegral.integral_of_le Real.pi_pos.le]

/-- Normalized averaging is a continuous functional on the actual angular L² space. -/
def n08AngleMean : AngleL2 →L[ℝ] ℝ :=
  (1 / Real.pi) • angleL2TestPairing (fun _ : ℝ => (1 : ℝ))
    (memLp_angleMeasure_of_continuous continuous_const)

theorem n08AngleMean_apply (u : AngleL2) :
    n08AngleMean u = angularMean (u : ℝ → ℝ) := by
  simp only [n08AngleMean, ContinuousLinearMap.smul_apply, smul_eq_mul,
    angleL2TestPairing_apply, mul_one, n08_angularMean_eq_angleIntegral]

theorem n08AngleMean_norm_le (u : AngleL2) :
    ‖n08AngleMean u‖ ≤ n08ControlMeanConstant * ‖u‖ := by
  simpa only [n08AngleMean_apply, Real.norm_eq_abs, Lp.norm_def,
    n08ControlMeanConstant] using abs_angularMean_le_angleL2 (Lp.memLp u)

/-- Angular averaging of the zero jet acts on the complete square-summable family. -/
def n08CircleJetMeans : CircleJetHilbert 0 →L[ℝ] ControlBanach :=
  lpSpectralDiagonal
    (fun _ : ℕ => n08AngleMean.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : CircleJetIndex 0 => AngleL2) (zeroCircleJetIndex 0)))
    n08ControlMeanConstant_nonneg (fun _ z => by
      rw [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      exact (n08AngleMean_norm_le _).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z (zeroCircleJetIndex 0))
          n08ControlMeanConstant_nonneg))

theorem n08CircleJetMeans_apply (u : CircleJetHilbert 0) (m : ℕ) :
    n08CircleJetMeans u m = angularMean (u m (zeroCircleJetIndex 0) : ℝ → ℝ) := by
  simp only [n08CircleJetMeans, lpSpectralDiagonal_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, n08AngleMean_apply]

theorem n08CircleJetMeans_norm_le (u : CircleJetHilbert 0) :
    ‖n08CircleJetMeans u‖ ≤ n08ControlMeanConstant * ‖u‖ := by
  unfold n08CircleJetMeans
  exact lpSpectralDiagonal_norm_le _ _ _ u

/-- The restriction is defined from actual model coordinates, with no
assumed summability or assumed continuous extension. -/
def n08ControlRestriction (S : PhysicalSpacesData) : CircleSpace S →L[ℝ] ControlBanach :=
  n08CircleJetMeans.comp
    (((S.circle (3 / 4 : ℝ)).level 0).subtypeL.comp
      (projectiveCoordinate (fun s => (S.circle (3 / 4 : ℝ)).level s)
        (S.circle (3 / 4 : ℝ)).bond 0))

theorem n08ControlRestriction_jet_apply (S : PhysicalSpacesData)
    (u : CircleSpace S) (m : ℕ) :
    n08ControlRestriction S u m =
      angularMean (((u.val 0).val m (zeroCircleJetIndex 0)) : ℝ → ℝ) := by
  simp only [n08ControlRestriction, ContinuousLinearMap.comp_apply,
    projectiveCoordinate_apply, Submodule.subtypeL_apply, n08CircleJetMeans_apply]

theorem n08ControlRestriction_norm_le (S : PhysicalSpacesData) (u : CircleSpace S) :
    ‖n08ControlRestriction S u‖ ≤
      n08ControlMeanConstant * (S.circle (3 / 4 : ℝ)).grading 0 u := by
  rw [n08ControlRestriction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    projectiveCoordinate_apply, Submodule.subtypeL_apply]
  refine (n08CircleJetMeans_norm_le ((u.val 0).val)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (norm_coordinate_le_graded (fun s => (S.circle (3 / 4 : ℝ)).level s)
      (S.circle (3 / 4 : ℝ)).bond (le_refl 0) u) n08ControlMeanConstant_nonneg

/-- The restriction has precisely the actual weighted mean coordinates. -/
theorem n08ControlRestriction_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (u : CircleSpace S) (m : ℕ) :
    n08ControlRestriction S u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m) := by
  have hmodel : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)) := hS.2.1 _
  have hae := hmodel.2.2.2.2.2.2.1 u 0 m
  rw [n08ControlRestriction_jet_apply]
  simp only [n08_angularMean_eq_angleIntegral]
  rw [integral_congr_ae hae, integral_const_mul]
  ring

theorem exists_n08ControlRestriction
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) :
    ∃ restriction : CircleSpace S →L[ℝ] ControlBanach, ∃ C : ℝ, 0 < C ∧
      (∀ u m, restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
        angularMean ((S.circle (3 / 4 : ℝ)).decode u m)) ∧
      ∀ u, ‖restriction u‖ ≤ C * (S.circle (3 / 4 : ℝ)).grading 0 u :=
  ⟨n08ControlRestriction S, n08ControlMeanConstant, n08ControlMeanConstant_pos,
    n08ControlRestriction_apply hS, n08ControlRestriction_norm_le S⟩

end ContinuousFlexibility.Analysis
