import ContinuousFlexibility.Statements.Nonlinear

/-!
# Uniqueness of the actual canonical volume model

The frozen specification fixes both the complete weak-jet submodule and
its weighted zero-column map at every level. Consequently any two models
satisfying it are equal as data. Bounds, continuous maps and physical graph
relations therefore transfer by this literal equality, with their norms
and their represented canonical sequences unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem n05_volumeModel_unique {T : MaterialData} {S : PhysicalSpacesData}
    {K : CanonicalData S} {V W : VolumeModelData S K}
    (hV : IsVolumeModel T S K V) (hW : IsVolumeModel T S K W) : V = W := by
  rcases V with ⟨lv, fv⟩
  rcases W with ⟨lw, fw⟩
  have hl : lv = lw := by
    funext γ t s
    apply SetLike.coe_injective
    exact (hV.1 γ t s).trans (hW.1 γ t s).symm
  cases hl
  have hf : fv = fw := by
    funext γ t s
    apply LinearMap.ext
    intro v
    funext m
    exact (hV.2.2.2 γ t s v m).trans (hW.2.2.2 γ t s v m).symm
  cases hf
  rfl

end ContinuousFlexibility.Statements
