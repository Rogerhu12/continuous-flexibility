import ContinuousFlexibility.Analysis.N05CanonicalModel

/-!
# N05: the actual closed canonical volume scale

Source: readable manuscript §8, lines 34--74.
Task: `docs/tasks/N05-VolumeModel.md`.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem N05VolumeModel {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (S : PhysicalSpacesData) (K : CanonicalData S) :
    ∃ V : VolumeModelData S K, IsVolumeModel T S K V :=
  exists_n05CanonicalVolumeModel hD hT S K

/-- info: 'ContinuousFlexibility.Blueprint.N05VolumeModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms N05VolumeModel

end ContinuousFlexibility.Blueprint
