import ContinuousFlexibility.Analysis.N05CanonicalInverseData
import ContinuousFlexibility.Analysis.N05CanonicalReferenceRelation
import ContinuousFlexibility.Analysis.N05CanonicalAllOrderInverse
import ContinuousFlexibility.Analysis.N05CanonicalAllOrderNormal
import ContinuousFlexibility.Analysis.N05CanonicalVolumeTransport

/-!
# The complete canonical reference inverse estimates

The physical reference supplies one inverse at three exponents. Its two
outer estimates give the same canonical inverse at every angular order
and every real material order, with loss four. The actual first normal
derivative obeys the corresponding bound with one additional source
angular derivative. The physical relation and the continuous base map
are those of this same inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem n05_existsReferenceInverseBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) :
    ∃ I : N05ReferenceInverseData S K V, N05ReferenceInverseBounds D T S C K V I := by
  have hmodel : V = n05CanonicalVolumeModel T S K :=
    n05_volumeModel_unique hV (n05CanonicalVolumeModel_actual hD.1 hT S K)
  subst V
  obtain ⟨ρ, M0, M1, hρ, hρbound, G, hfamily⟩ := hD.2.2.2.2
  have hm := hfamily (referenceBeta - ρ) (Or.inl rfl)
  have hp := hfamily (referenceBeta + ρ) (Or.inr (Or.inr rfl))
  dsimp only [referenceBeta] at hm hp
  have hminus : 0 < (3 / 4 : ℝ) - ρ := by linarith only [hρbound]
  have hplus : 0 < (3 / 4 : ℝ) + ρ := by linarith only [hρ]
  let I : N05ReferenceInverseData S K (n05CanonicalVolumeModel T S K) :=
    n05CanonicalReferenceInverseData hD hT hS h hcoordinates hV hρ hρbound hm.1
  have hbase (F : (n05CanonicalVolumeModel T S K).level (3 / 4 : ℝ) 0 2) :
      I.baseInverse F = n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget (3 / 4 : ℝ) 0 2 F) :=
    n05CanonicalReferenceInverseData_base_apply hD hT hS h hcoordinates hV hρ hρbound hm.1 F
  refine ⟨I, hminus, sub_lt_self _ hρ, by norm_num [I, n05CanonicalReferenceInverseData],
    hm.1, hbase, ?_, ?_, ?_⟩
  · intro F
    rw [hbase F]
    exact n05CanonicalGlobalInverse_base_relation
      hD hT hS h hcoordinates hρ hρbound hm.1 hp.1 F
  · refine ⟨ρ / 2, half_pos hρ, by linarith only [hρbound], ?_⟩
    intro γ hγ t s
    have hwindow : |γ - (3 / 4 : ℝ)| ≤ ρ / 2 := by
      rcases hγ with rfl | rfl | rfl <;>
        apply abs_le.mpr <;> constructor <;> linarith only [hρ]
    exact n05CanonicalGlobalInverse_all_level_bound hD hT hS h hcoordinates
      hminus hplus hwindow (by linarith only [hρ]) hm.1 hp.1 t s
  · intro t s
    obtain ⟨B, hB, hnormal⟩ := n05CanonicalGlobalInverse_all_normal_level_bound
      (β := (3 / 4 : ℝ)) (ρ := ρ) (γ := (3 / 4 : ℝ)) (δ := 0)
      hD hT hS h hcoordinates hminus hplus
      (show |(3 / 4 : ℝ) - (3 / 4 : ℝ)| ≤ (0 : ℝ) by simp) hρ
      hm.1 hp.1 hm.2.2.2.2 hp.2.2.2.2 t s
    refine ⟨B, hB, fun F => ?_⟩
    obtain ⟨W, _, hweak, hnorm⟩ := hnormal F
    exact ⟨W, hweak, hnorm⟩

end ContinuousFlexibility.Statements
