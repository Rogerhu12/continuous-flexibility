module

public import ContinuousFlexibility.Analysis.NormedSmoothDirections
public import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomDirections
public import ContinuousFlexibility.Analysis.N01cStateAngleSelections
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Fixed spatial terms vanish in every positive state word

Subtracting the angle or a fixed radial origin leaves the joint words
used for positive parameter jets unchanged. No bound on an unwrapped
angle value is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint}

theorem n04PositiveGeometry_fixedSpatial_stateWord_zero
    (hU : IsOpen U) (hV : IsOpen V) {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g V)
    (J : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => g z.2))
    {n : ℕ} (w : StateAngleWord n) (hw : 0 < w.stateArity)
    {x : E} (hx : x ∈ U) {q : PolarPoint} (hq : q ∈ V)
    (v : Fin n → E × PolarPoint)
    (hv : ∀ i, w.isState i = true → (v i).2 = 0) : J.D n (x, q) v = 0 := by
  classical
  have hex : ∃ i, w.isState i = true := by
    by_contra h
    have hsum : (∑ i : Fin n, if w.isState i then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi
      · exact False.elim (h ⟨i, hi⟩)
      · rfl
    rw [← w.stateArity_eq_sum] at hsum
    omega
  obtain ⟨i, hi⟩ := hex
  let P : (E × PolarPoint) →L[ℝ] PolarPoint := ContinuousLinearMap.snd ℝ E PolarPoint
  let K₀ := smoothDirectionsOfContDiffOn hV hg
  have hmap : MapsTo (fun z => (0 : PolarPoint) + P z) (U ×ˢ V) V := by
    intro z hz
    simpa only [P, ContinuousLinearMap.coe_snd', zero_add] using hz.2
  let K : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => g z.2) :=
    (K₀.compAffine P 0 (hU.prod hV) hmap).congrOn
      (fun z _ => by simp only [P, ContinuousLinearMap.coe_snd', zero_add])
  have he := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] ℝ => A v)
    (J.unique K n (x, q) ⟨hx, hq⟩)
  have he' : J.D n (x, q) v = K₀.D n q (fun j => (v j).2) := by
    simpa only [K, SmoothDirections.congrOn, SmoothDirections.compAffine_apply,
      P, ContinuousLinearMap.coe_snd', zero_add] using he
  exact he'.trans ((K₀.D n q).map_coord_zero i (hv i hi))

theorem n04PositiveGeometry_sub_fixedSpatial_stateWord
    (hU : IsOpen U) (hV : IsOpen V) {f : E × PolarPoint → ℝ} {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g V) (J : SmoothDirections (U ×ˢ V) f)
    (K : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => f z - g z.2))
    (JG : SmoothDirections (U ×ˢ V) (fun z : E × PolarPoint => -g z.2))
    {n : ℕ} (w : StateAngleWord n) (hw : 0 < w.stateArity)
    {x : E} (hx : x ∈ U) {q : PolarPoint} (hq : q ∈ V)
    (v : Fin n → E × PolarPoint)
    (hv : ∀ i, w.isState i = true → (v i).2 = 0) :
    K.D n (x, q) v = J.D n (x, q) v := by
  have hzero := n04PositiveGeometry_fixedSpatial_stateWord_zero hU hV hg.neg
    JG w hw hx hq v hv
  let Q := (smoothDirectionsAdd J JG).congrOn
    (fun z _ => (sub_eq_add_neg (f z) (g z.2)).symm)
  have he := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] ℝ => A v)
    (K.unique Q n (x, q) ⟨hx, hq⟩)
  simpa only [Q, SmoothDirections.congrOn, smoothDirectionsAdd,
    ContinuousMultilinearMap.add_apply, hzero, add_zero] using he

end ContinuousFlexibility.Analysis
