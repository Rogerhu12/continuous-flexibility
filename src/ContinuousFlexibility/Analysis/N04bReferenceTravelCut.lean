import ContinuousFlexibility.Analysis.N01RadialFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The actual reference cut at half optical travel

The fixed reference metadata must use the inverse image of half the
reference optical travel. The physical arithmetic midpoint need not have
that travel value. Strict positivity of the actual optical speed inside
each negative component gives a unique interior reference cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

theorem n04b_referenceOpticalSpeed_continuousOn
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    ContinuousOn (opticalSpeed D.w) (Icc (C.left m) (C.right m)) := by
  apply continuousOn_opticalSpeed_of_profile hD.2.2.1.1
    (hD.1.trans (hC.1 m).1)
  intro r hr
  exact hD.2.2.2.2.1 r
    ⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩

theorem n04b_referenceOpticalSpeed_pos
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    0 < opticalSpeed D.w r := by
  have hrD : r ∈ radialCore D :=
    ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
  exact Real.sqrt_pos.mpr
    (div_pos (neg_pos.mpr (hC.2.2.2.1 m r hr))
      (mul_pos (hD.1.trans hrD.1) (hD.2.2.2.2.1 r hrD)))

theorem n04b_referenceTravel_continuousOn
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    ContinuousOn (opticalTravel D.w (C.left m)) (Icc (C.left m) (C.right m)) := by
  have hc := n04b_referenceOpticalSpeed_continuousOn hD hC m
  have hi : IntervalIntegrable (opticalSpeed D.w) volume (C.left m) (C.right m) :=
    hc.intervalIntegrable_of_Icc (hC.1 m).2.1.le
  simpa only [opticalTravel, uIcc_of_le (hC.1 m).2.1.le] using
    (intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : C.left m ∈ Set.uIcc (C.left m) (C.right m)))

theorem n04b_referenceTravel_hasDerivAt
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    HasDerivAt (opticalTravel D.w (C.left m)) (opticalSpeed D.w r) r := by
  have hc := n04b_referenceOpticalSpeed_continuousOn hD hC m
  have ho := hc.mono Ioo_subset_Icc_self
  have hi : IntervalIntegrable (opticalSpeed D.w) volume (C.left m) r :=
    (hc.mono (Icc_subset_Icc le_rfl hr.2.le)).intervalIntegrable_of_Icc hr.1.le
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ho r hr)
    ((ho r hr).continuousAt (isOpen_Ioo.mem_nhds hr))

theorem n04b_referenceTravel_strictMonoOn
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    StrictMonoOn (opticalTravel D.w (C.left m)) (Icc (C.left m) (C.right m)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (n04b_referenceTravel_continuousOn hD hC m)
  intro r hr
  have hr' : r ∈ Ioo (C.left m) (C.right m) := by
    simpa only [interior_Icc] using hr
  rw [(n04b_referenceTravel_hasDerivAt hD hC m hr').deriv]
  exact n04b_referenceOpticalSpeed_pos hD hC m hr'

theorem n04b_referenceTravel_right
    (hC : controlGeometryConditions D S C) (m : ℕ) :
    opticalTravel D.w (C.left m) (C.right m) = C.travel m := by
  exact (hC.2.2.2.2.2.2.2.1 m).symm

theorem n04b_referenceTravel_pos
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    0 < C.travel m := by
  have hab := (hC.1 m).2.1
  have h := n04b_referenceTravel_strictMonoOn hD hC m
    (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  rw [n04b_referenceTravel_right hC m] at h
  simpa only [opticalTravel, intervalIntegral.integral_same] using h

/-- The reference cut is fixed by its actual travel value, uniquely. -/
theorem n04b_exists_unique_referenceTravel_cut
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    ∃! r : ℝ, r ∈ Ioo (C.left m) (C.right m) ∧
      opticalTravel D.w (C.left m) r = C.travel m / 2 := by
  have hT := n04b_referenceTravel_pos hD hC m
  have hleft : opticalTravel D.w (C.left m) (C.left m) = 0 := by
    exact intervalIntegral.integral_same
  have hright := n04b_referenceTravel_right hC m
  have hmiddle : C.travel m / 2 ∈
      Icc (opticalTravel D.w (C.left m) (C.left m))
        (opticalTravel D.w (C.left m) (C.right m)) := by
    rw [hleft, hright]
    constructor <;> linarith
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (hC.1 m).2.1.le
    (n04b_referenceTravel_continuousOn hD hC m) hmiddle
  have hri : r ∈ Ioo (C.left m) (C.right m) := by
    constructor
    · by_contra hn
      have heq : r = C.left m := le_antisymm (le_of_not_gt hn) hr.1
      rw [heq, hleft] at he
      linarith
    · by_contra hn
      have heq : r = C.right m := le_antisymm hr.2 (le_of_not_gt hn)
      rw [heq, hright] at he
      linarith
  refine ⟨r, ⟨hri, he⟩, ?_⟩
  intro s hs
  exact (n04b_referenceTravel_strictMonoOn hD hC m).injOn
    ⟨hs.1.1.le, hs.1.2.le⟩ hr (hs.2.trans he.symm)

/-- One fixed reference cut for each actual negative component. -/
def n04bReferenceTravelCut
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) : ℝ :=
  (n04b_exists_unique_referenceTravel_cut hD hC m).exists.choose

theorem n04bReferenceTravelCut_spec
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C) (m : ℕ) :
    n04bReferenceTravelCut hD hC m ∈ Ioo (C.left m) (C.right m) ∧
      opticalTravel D.w (C.left m) (n04bReferenceTravelCut hD hC m) = C.travel m / 2 :=
  (n04b_exists_unique_referenceTravel_cut hD hC m).exists.choose_spec

end ContinuousFlexibility.Analysis
