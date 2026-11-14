module

public import ContinuousFlexibility.Analysis.N04RealizationLeadStart
public import ContinuousFlexibility.Analysis.N04RealizationRootAbsorbedJoint
public import ContinuousFlexibility.Analysis.N06RootPhysicalSmallness
public import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition
public import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# Actual root fields on a common profile collar

On a fixed spatial set where every state profile equals the reference
profile, the original N01 coefficient inequalities bound the normalized
root denominators. The absorbed packet has an actual joint tower, so the
physical drift and speed ratio have one too. This applies on a whole root
collar, not only to traces at its zero axis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

abbrev negativeRootParameterRadius : ℝ := min W.ε (1 / 2 : ℝ)

abbrev negativeRootParameterDomain : Set (StateDirections W.S × ℝ) :=
  sectorNeighborhood W.S W.base W.negativeRootParameterRadius W.negativeRootParameterRadius

theorem negativeRootParameterRadius_pos : 0 < W.negativeRootParameterRadius :=
  lt_min W.ε_pos (by norm_num)

/-- The normalized denominator inequalities hold at every physical point
where the actual profile equals the reference value. -/
theorem rootNormalized_denominators_of_profile
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C W.base W.ε)
    (hs : stateSector W.S z.1) {p : PolarPoint} (hp : p ∈ annularOpen W.D)
    (hprofile : stateProfile W.D W.S W.C z.1 p.1 = W.D.w p.1) :
    (7 / 8 : ℝ) ≤ n06RootNormalizedQ (n06ActualRootNormalizedCoordinates W.D W.S z p) ∧
      (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant
        (n06ActualRootNormalizedCoordinates W.D W.S z p) := by
  have hN := W.through03.1.1
  have hr : 0 < p.1 := hN.1.1.choose_spec.1.1.trans hp.1.1
  have hw : W.D.w p.1 ≠ 0 := (hN.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne'
  have hraw := n06_rootFinite_denominators_eq W.hT W.hS hN z hr.ne' hprofile
  have hnorm := n06_normalizeRoot_denominators
    (v := n06ActualNuJetCoordinates W.D W.S z p) hw
  have hQ : n06RootNormalizedQ (n06ActualRootNormalizedCoordinates W.D W.S z p) =
      heightQ (profileEnergy (stateProfile W.D W.S W.C z.1) p)
        (heightRadial (stateHeight W.D W.S W.C z) p)
        (angularPartial (heightAngular (stateHeight W.D W.S W.C z)) p) /
          stateProfile W.D W.S W.C z.1 p.1 :=
    hnorm.1.trans (congrArg₂ (fun a b : ℝ => a / b) hraw.1 hprofile.symm)
  have hD : n06RootNormalizedDiscriminant
      (n06ActualRootNormalizedCoordinates W.D W.S z p) =
      polarDiscriminant (stateProfile W.D W.S W.C z.1)
        (stateHeight W.D W.S W.C z) p := hnorm.2.trans hraw.2
  have hb := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  exact ⟨hb.2.2.1.trans_eq hQ.symm, hb.2.2.2.2.1.trans_eq hD.symm⟩

/-- At scalar parameter zero the physical drift and speed ratio are
exactly their reference values, for every profile on this locus. -/
theorem rootPhysicalFields_zero_parameter_of_profile
    (x : AnnularState W.S) {p : PolarPoint} (hp : p ∈ annularOpen W.D)
    (hprofile : stateProfile W.D W.S W.C x p.1 = W.D.w p.1) :
    n06PhysicalRootFields W.D W.S W.C (x, 0) p = (0, 1) := by
  have hr : 0 < p.1 := W.through03.1.1.1.1.choose_spec.1.1.trans hp.1.1
  have hw : W.D.w p.1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1).ne'
  exact (n06_physicalRootFields_eq_finite W.hT W.hS W.through03.1.1
      (x, 0) hr.ne' hprofile).trans
    ((n06_normalizeRoot_fields
      (v := n06ActualNuJetCoordinates W.D W.S (x, 0) p) hw).symm.trans
      (congrFun (n06_rootNormalizedFields_zero_parameter W.D W.S x) p))

/-- Restrict the actual absorbed packet to the sector by its fixed affine
parameter inclusion. This is independent of the profile-locus identity. -/
def rootAbsorbedCoordinates_sectorJointTower
    (Ω : Set PolarPoint) (hΩ : IsOpen Ω) (hΩann : Ω ⊆ annularOpen W.D) :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ Ω)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n06ActualRootAbsorbedCoordinates W.D W.S (liftSectorParameter W.S W.C x.1) x.2) := by
  let U := W.negativeRootParameterDomain ×ˢ Ω
  have hU : IsOpen U :=
    (sectorNeighborhood_isOpen W.S W.base W.negativeRootParameterRadius
      W.negativeRootParameterRadius).prod hΩ
  have hε : W.negativeRootParameterRadius ≤ 1 :=
    (min_le_right W.ε (1 / 2 : ℝ)).trans (by norm_num)
  let JP : SmoothDirections
      (stateNeighborhood W.S W.C W.base W.negativeRootParameterRadius ×ˢ annularOpen W.D)
      (fun x : (AnnularState W.S × ℝ) × PolarPoint =>
        n06ActualRootAbsorbedCoordinates W.D W.S x.1 x.2) :=
    n04Realization_rootAbsorbedCoordinates_joint
    (D := W.D) (T := W.T) (C := W.C) (base := W.base) (ε := W.negativeRootParameterRadius)
    W.through03.1.1.1.1 W.hT W.hS hε
  let c : (AnnularState W.S × ℝ) × PolarPoint := ((W.C.referenceState, 0), 0)
  let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ]
      (AnnularState W.S × ℝ) × PolarPoint :=
    ((sectorParameterInclusion W.S).comp
      (ContinuousLinearMap.fst ℝ (StateDirections W.S × ℝ) PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
  have hpoint (x : (StateDirections W.S × ℝ) × PolarPoint) :
      c + L x = (liftSectorParameter W.S W.C x.1, x.2) := by
    simp only [c, L, liftSectorParameter_eq_affine, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add]
  have hmap : MapsTo (fun x => c + L x) U
      (stateNeighborhood W.S W.C W.base W.negativeRootParameterRadius ×ˢ
        annularOpen W.D) := by
    intro x hx
    change c + L x ∈ _
    rw [hpoint x]
    exact ⟨liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl, hΩann hx.2⟩
  apply (JP.compAffine L c hU hmap).congrOn
  intro x hx
  exact congrArg (fun q : (AnnularState W.S × ℝ) × PolarPoint =>
    n06ActualRootAbsorbedCoordinates W.D W.S q.1 q.2) (hpoint x)

/-- The actual physical drift and speed ratio on any fixed open profile
locus. The common root collar below supplies all three spatial inputs. -/
def rootProfileLocus_physicalFieldsJointTower
    (Ω : Set PolarPoint) (hΩ : IsOpen Ω) (hΩann : Ω ⊆ annularOpen W.D)
    (hprofile : ∀ x : AnnularState W.S, ∀ p ∈ Ω,
      stateProfile W.D W.S W.C x p.1 = W.D.w p.1) :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ Ω)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n06PhysicalRootFields W.D W.S W.C (liftSectorParameter W.S W.C x.1) x.2) := by
  let U := W.negativeRootParameterDomain ×ˢ Ω
  let K := W.rootAbsorbedCoordinates_sectorJointTower Ω hΩ hΩann
  let V : Set N06RootNormalizedCoordinates :=
    {q | 0 < n06RootNormalizedQ q ∧ 0 < n06RootNormalizedDiscriminant q}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  have hkernel : ContDiffOn ℝ ∞ n06RootNormalizedFields V := fun q hq =>
    (n06RootNormalizedFields_contDiffAt hq.1.ne' hq.2).contDiffWithinAt
  have hKmap : MapsTo
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n06ActualRootAbsorbedCoordinates W.D W.S (liftSectorParameter W.S W.C x.1) x.2)
      U V := by
    intro x hx
    have hz : liftSectorParameter W.S W.C x.1 ∈ stateNeighborhood W.S W.C W.base W.ε :=
      stateNeighborhood_mono W.S W.C le_rfl (min_le_left _ _)
        (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
    have hd := W.rootNormalized_denominators_of_profile hz
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) (hΩann hx.2)
      (hprofile _ x.2 hx.2)
    have he := n06_absorbRoot_denominators
      (n06ActualRootNormalizedCoordinates W.D W.S (liftSectorParameter W.S W.C x.1) x.2)
    exact ⟨(lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hd.1).trans_eq he.1.symm,
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hd.2).trans_eq he.2.symm⟩
  apply (K.comp_contDiff hV hkernel hKmap).congrOn
  intro x hx
  have hp := hΩann hx.2
  have hr : 0 < x.2.1 := W.through03.1.1.1.1.choose_spec.1.1.trans hp.1.1
  have hw : W.D.w x.2.1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 x.2.1 hp.1).ne'
  exact (n06_absorbRoot_fields
      (n06ActualRootNormalizedCoordinates W.D W.S (liftSectorParameter W.S W.C x.1) x.2)).trans
    ((n06_normalizeRoot_fields
      (v := n06ActualNuJetCoordinates W.D W.S (liftSectorParameter W.S W.C x.1) x.2) hw).trans
      (n06_physicalRootFields_eq_finite W.hT W.hS W.through03.1.1
        (liftSectorParameter W.S W.C x.1) hr.ne' (hprofile _ x.2 hx.2)).symm)

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.rootProfileLocus_physicalFieldsJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.rootProfileLocus_physicalFieldsJointTower
