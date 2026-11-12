import ContinuousFlexibility.Analysis.N05CanonicalZeroOrderInverse

/-!
# The fixed canonical inverse belongs to the original physical relation

The weighted zero-order output is the actual first component of the same
global inverse. Together with its genuine physical source normalization
and selected scalars, this proves the literal frozen reference relation
on the prescribed base source layer.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem n05CanonicalGlobalInverse_base_relation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {ρ M0 M1 : ℝ} (hρ : 0 < ρ) (hρbound : ρ < (1 / 4 : ℝ))
    {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D ((3 / 4 : ℝ) - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D ((3 / 4 : ℝ) + ρ) M0 M1 G)
    (v : (n05CanonicalVolumeModel T S K).level (3 / 4 : ℝ) 0 2) :
    ReferenceCanonicalRelation D T S C K (n05CanonicalVolumeModel T S K)
      ((3 / 4 : ℝ) - ρ) M0 M1 4
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) 0 2 v))
      ((n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) 0 2 v) := by
  have hminus : 0 < (3 / 4 : ℝ) - ρ := by linarith only [hρbound]
  have hplus : 0 < (3 / 4 : ℝ) + ρ := by linarith only [hρ]
  have hgap : (3 / 4 : ℝ) - ρ < (3 / 4 : ℝ) := sub_lt_self _ hρ
  have hV := n05CanonicalVolumeModel_actual hD.1 hT S K
  obtain ⟨_, _, hweighted⟩ := n05CanonicalGlobalInverse_zero_level_bound
    (β := (3 / 4 : ℝ)) (ρ := ρ) (γ := (3 / 4 : ℝ)) (δ := 0)
    hD hT hS h hcoordinates hminus hplus
    (show |(3 / 4 : ℝ) - (3 / 4 : ℝ)| ≤ (0 : ℝ) by simp) hρ hGminus hGplus 0 2
  obtain ⟨W, hW, _⟩ := hweighted v
  obtain ⟨hrep, hgraph⟩ := n05CanonicalGlobalInverse_represents
    hD hT hS h hcoordinates hV hminus hgap hGminus 0 2 v
  refine ⟨?_,
    (G (n05CanonicalNormalizedSource D S C K
      ((n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) 0 2 v))).1,
    n05CanonicalSourceLift S C K
      ((n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) 0 2 v), hrep, hgraph⟩
  refine ⟨W, ?_⟩
  funext m
  calc
    _ = (n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) (0 - 4) 0 W m := by
      rw [n05CanonicalVolumeModel_forget, n05CanonicalVolumeModel_forget]
      norm_num
    _ = _ := congrFun hW m

end ContinuousFlexibility.Statements
