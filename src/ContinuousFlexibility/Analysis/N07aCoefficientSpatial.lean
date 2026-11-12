import ContinuousFlexibility.Analysis.N07aLeadingRegularity

/-!
# Interior regularity of all three actual coefficients

The same pointwise geometric inequalities used for the leading coefficient
also give regularity of the mixed and corrected angular coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07a_originalCoefficients_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) ∧
      ContDiffOn ℝ ∞ (originalCoefficients D S C z).b (annularOpen D) ∧
      ContDiffOn ℝ ∞ (originalCoefficients D S C z).c (annularOpen D) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hw := contDiff_stateProfile_of_n01 hS hT h01 z.1
  have hh := n07a_stateHeight_contDiffOn hS hT h01 z
  have hgeom := h01.1.1.choose_spec.1
  have hpoint (p : PolarPoint) (hp : p ∈ annularOpen D) :=
    h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hregular (p : PolarPoint) (hp : p ∈ annularOpen D) :
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
        ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
        ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p := by
    have hwp : 0 < stateProfile D S C z.1 p.1 := by
      exact mul_pos (hgeom.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
    have hQlower := (le_div_iff₀ hwp).mp (hpoint p hp).2.2.1
    have hQpos : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) := by
      linarith only [hwp, hQlower]
    have hΔpos : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpoint p hp).2.2.2.2.1
    have h := contDiffAt_heightLinearCoefficients hw.contDiffAt
      (hh.contDiffAt (hopen.mem_nhds hp)) (hgeom.1.trans hp.1.1).ne' hΔpos hQpos.ne'
    exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  exact ⟨fun p hp => (hregular p hp).1.contDiffWithinAt,
    fun p hp => (hregular p hp).2.1.contDiffWithinAt,
    fun p hp => (hregular p hp).2.2.contDiffWithinAt⟩

end ContinuousFlexibility.Analysis
