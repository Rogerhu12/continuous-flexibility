module

public import ContinuousFlexibility.Analysis.N04bCollarInverse

/-!
# Gluing the physical inverse to its genuine root-collar inverse

The positive radial factor shows that a positive target point has a
positive source coordinate in the collar. Global injectivity of the
actual physical chart then identifies its physical inverse with the
collar inverse. A piecewise stored inverse is therefore genuinely smooth
on a full neighborhood of the root, while retaining every interior germ.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- Use the physical inverse inside the canonical half-strip, and the
genuine collar inverse at and beyond its root boundary. -/
def n04bGluedRootInverse (G H : PolarPoint → PolarPoint) (q : PolarPoint) : PolarPoint :=
  if 0 < q.1 then H q else G q

theorem n04bGluedRootInverse_physical_germ
    (G H : PolarPoint → PolarPoint) {q : PolarPoint} (hq : 0 < q.1) :
    n04bGluedRootInverse G H =ᶠ[𝓝 q] H := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hq] with p hp
  exact if_pos hp

theorem n04b_collarInverse_first_pos
    {F G : PolarPoint → PolarPoint} {g : PolarPoint → ℝ}
    {S T : Set PolarPoint}
    (hMaps : MapsTo G T S) (hRight : RightInvOn G F T)
    (hFactor : ∀ p ∈ S, (F p).1 = p.1 * g p)
    (hFactorPos : ∀ p ∈ S, 0 < g p)
    {q : PolarPoint} (hq : q ∈ T) (hq0 : 0 < q.1) :
    0 < (G q).1 := by
  have hprod : 0 < (G q).1 * g (G q) := by
    rw [← hFactor _ (hMaps hq)]
    simpa only [hRight hq] using hq0
  by_contra hn
  exact (not_lt_of_ge
    (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (hFactorPos _ (hMaps hq)).le)) hprod

/-- Compatibility of the two inverses follows from actual chart
identities and injectivity; it is not an extra inverse-germ hypothesis. -/
theorem n04b_physicalInverse_eq_collarInverse
    {F Fphys G H : PolarPoint → PolarPoint} {g : PolarPoint → ℝ}
    {S T Ω : Set PolarPoint}
    (hMaps : MapsTo G T S) (hRight : RightInvOn G F T)
    (hFactor : ∀ p ∈ S, (F p).1 = p.1 * g p)
    (hFactorPos : ∀ p ∈ S, 0 < g p)
    (hPhysical : S ∩ {p : PolarPoint | 0 < p.1} ⊆ Ω)
    (hAgree : EqOn Fphys F (S ∩ {p : PolarPoint | 0 < p.1}))
    (hPhysInj : InjOn Fphys Ω)
    (hHMaps : MapsTo H (T ∩ {q : PolarPoint | 0 < q.1}) Ω)
    (hHRight : RightInvOn H Fphys (T ∩ {q : PolarPoint | 0 < q.1}))
    {q : PolarPoint} (hq : q ∈ T) (hq0 : 0 < q.1) :
    H q = G q := by
  have hGpos := n04b_collarInverse_first_pos hMaps hRight hFactor hFactorPos hq hq0
  have hGphys : G q ∈ Ω := hPhysical ⟨hMaps hq, hGpos⟩
  apply hPhysInj (hHMaps ⟨hq, hq0⟩) hGphys
  exact (hHRight ⟨hq, hq0⟩).trans ((hAgree ⟨hMaps hq, hGpos⟩).trans (hRight hq)).symm

/-- The piecewise actual inverse has both inverse identities on the
collar, is smooth there, and has genuine full-neighborhood inverse germs.
Its physical-interior values are retained by definition. -/
theorem n04b_gluedRootInverse_spec
    {F Fphys G H : PolarPoint → PolarPoint} {g : PolarPoint → ℝ}
    {S T Ω : Set PolarPoint}
    (hS : IsOpen S) (hT : IsOpen T)
    (hF : ContDiffOn ℝ ∞ F S) (hJ : ∀ p ∈ S, planeJacobian F p ≠ 0)
    (hInj : InjOn F S)
    (hMaps : MapsTo G T S) (hRight : RightInvOn G F T)
    (hFactor : ∀ p ∈ S, (F p).1 = p.1 * g p)
    (hFactorPos : ∀ p ∈ S, 0 < g p)
    (hPhysical : S ∩ {p : PolarPoint | 0 < p.1} ⊆ Ω)
    (hAgree : EqOn Fphys F (S ∩ {p : PolarPoint | 0 < p.1}))
    (hPhysInj : InjOn Fphys Ω)
    (hHMaps : MapsTo H (T ∩ {q : PolarPoint | 0 < q.1}) Ω)
    (hHRight : RightInvOn H Fphys (T ∩ {q : PolarPoint | 0 < q.1})) :
    let J := n04bGluedRootInverse G H
    EqOn J G T ∧ MapsTo J T S ∧ LeftInvOn J F (S ∩ F ⁻¹' T) ∧
      RightInvOn J F T ∧ ContDiffOn ℝ ∞ J T ∧
      ∀ p ∈ S, F p ∈ T → CanonicalBoundaryInverseGerm F J p := by
  let J := n04bGluedRootInverse G H
  have heq : EqOn J G T := by
    intro q hq
    by_cases hq0 : 0 < q.1
    · change (if 0 < q.1 then H q else G q) = G q
      rw [if_pos hq0]
      exact n04b_physicalInverse_eq_collarInverse hMaps hRight hFactor hFactorPos
        hPhysical hAgree hPhysInj hHMaps hHRight hq hq0
    · exact if_neg hq0
  have hMapsJ : MapsTo J T S := by
    intro q hq
    rw [heq hq]
    exact hMaps hq
  have hRightJ : RightInvOn J F T := by
    intro q hq
    rw [heq hq]
    exact hRight hq
  refine ⟨heq, hMapsJ, ?_, hRightJ,
    contDiffOn_planar_rightInverse_of_injOn hS hT hF hJ hInj hMapsJ hRightJ, ?_⟩
  · intro p hp
    apply hInj (hMapsJ hp.2) hp.1
    exact hRightJ hp.2
  · intro p hp hFp
    exact n04b_boundaryInverseGerm_of_rightInverse hS hT
      (hF.contDiffAt (hS.mem_nhds hp)) (hJ p hp) hInj hMapsJ hRightJ hp hFp

end ContinuousFlexibility.Analysis
