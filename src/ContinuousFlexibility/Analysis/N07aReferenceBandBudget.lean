module

public import ContinuousFlexibility.Analysis.N07aVolumeBandBudget
public import ContinuousFlexibility.Analysis.N07aReferenceSecondNormal

/-!
# One actual N05 volume representative for every mode budget

Only the fixed base angular order is used.  The same weighted field
represents the prescribed reference inverse and controls each of its
local angular bands.  Higher output orders will be supplied by the exact
band weights, without choosing another reference inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

local instance n07aReferenceBandBudgetLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aReferenceBandBudgetLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _
local instance n07aReferenceBandBudgetUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceBandBudgetUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n07aReferenceBandBudgetGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aReferenceBandBudgetGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

theorem n07a_referenceInverse_baseVolume_budget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h05 : N05Properties D T S C K V b B) (hI : ∀ m, K.left m < K.right m) :
    ∃ A : ℝ, 0 < A ∧ ∀ F : V.level (3 / 4 : ℝ) 0 b,
      ∃ W : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) b,
        V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) b W =
          n07aReferenceInverseField (B := B) F ∧
        ‖W‖ + canonicalUnknownScalars S K (B.inverse F).val.1 ≤ A * ‖F‖ ∧
        ∀ m j, Real.sqrt (n07aAngularJetWeightSq b j) *
            ‖n07aAngularBand m (hI m) j (n07aReferenceInverseField (B := B) F m)‖ ≤
          n07aVolumeWeight T K (3 / 4 : ℝ) (0 - B.lossMaterial) m * ‖W.val m‖ := by
  let estimates := h05.2.2.2.2.2.2.2.2.2.2.2.2.1 0 b
  let A : ℝ := estimates.choose
  have hA : 0 < A := estimates.choose_spec.1
  have hb := estimates.choose_spec.2
  refine ⟨A, hA, fun F => ?_⟩
  let W : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) b := (hb F).choose
  have hcoh := h05.2.2.2.2.2.2.2.2.2.1 F
  have hW : V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) b W =
      n07aReferenceInverseField (B := B) F := by
    funext m
    exact (congrFun (hb F).choose_spec.1 m).trans
      (congrArg (fun U : CanonicalUnknown S K => U.1 m) hcoh).symm
  have hnorm : ‖W‖ + canonicalUnknownScalars S K (B.inverse F).val.1 ≤ A * ‖F‖ := by
    rw [hcoh]
    exact (hb F).choose_spec.2
  refine ⟨W, hW, hnorm, fun m j => ?_⟩
  have h := n07aVolume_band_piece_norm_le hD hT h05.2.1
    (3 / 4 : ℝ) (0 - B.lossMaterial) hI b j W m
  rwa [hW] at h

end ContinuousFlexibility.Analysis
