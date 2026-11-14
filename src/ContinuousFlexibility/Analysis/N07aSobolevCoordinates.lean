module

public import ContinuousFlexibility.Analysis.SpacesPhysicalEncode
public import ContinuousFlexibility.Analysis.SpacesPhysicalUniqueness

/-!
# Actual weighted coordinates of every frozen Sobolev model

The frozen model identifies its zero coordinate with the decoded height.
Uniqueness of the original weak derivatives then identifies every higher
coordinate with the actual weighted mixed derivative. This supplies the
coordinate identity used when lifting genuine parameter towers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- Every actual model level is exactly the weighted jet of its decoder. -/
theorem n07a_sobolev_level_eq_heightJet
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (u : A.Space) (s : ℕ) :
    (u.val s).val = spacesPhysicalHeightJet (hA.2.2.2.1 u) s := by
  let hf := hA.2.2.2.1 u
  have hu : (u.val s).val ∈ physicalJetGraph T s := by
    rw [← hA.1 s]
    exact (u.val s).property
  have hv := spacesPhysicalHeightJet_mem_graph hT hf s
  have hzero : (u.val s).val (zeroJetIndex s) =
      spacesPhysicalHeightJet hf s (zeroJetIndex s) := by
    rw [spacesPhysicalHeightJet_zero]
    exact Lp.ext ((hA.2.2.2.2.2.2.1 u s).trans
      (spaces_materialPullback_memLp hf).coeFn_toLp.symm)
  apply PiLp.ext
  intro j
  let dataU := hu.2 j
  let du : CylinderL2 := dataU.choose
  have hdu : HasWeakMixedDerivative ((u.val s).val (zeroJetIndex s)) du
      (j.val 0).val (j.val 1).val := dataU.choose_spec.1
  have hwu : (((u.val s).val j) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => T.M (T.radius p.1) ^ (j.val 2).val * du p) := dataU.choose_spec.2
  let dataV := hv.2 j
  let dv : CylinderL2 := dataV.choose
  have hdv : HasWeakMixedDerivative (spacesPhysicalHeightJet hf s (zeroJetIndex s)) dv
      (j.val 0).val (j.val 1).val := dataV.choose_spec.1
  have hwv : (spacesPhysicalHeightJet hf s j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      (fun p => T.M (T.radius p.1) ^ (j.val 2).val * dv p) := dataV.choose_spec.2
  rw [hzero] at hdu
  have hd : du = dv := hasWeakMixedDerivative_unique hdu hdv
  rw [hd] at hwu
  exact Lp.ext (hwu.trans hwv.symm)

/-- All coordinates are the actual weighted mixed derivatives, almost
everywhere for the material cylinder measure. -/
theorem n07a_sobolev_coordinate_ae
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (u : A.Space) (s : ℕ) (j : JetIndex s) :
    (((u.val s).val j) : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val (A.decode u) := by
  rw [n07a_sobolev_level_eq_heightJet hT hA]
  exact spacesPhysicalHeightJet_ae (hA.2.2.2.1 u) s j

end ContinuousFlexibility.Analysis
