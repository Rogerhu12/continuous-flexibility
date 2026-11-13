import ContinuousFlexibility.Analysis.N04NegativeGeometryRootCollarData
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# Genuine joint towers for the actual coefficients on a root collar

The collar is the common one already supplied by N01. Affine pullback
of the physical drift and speed ratio, followed by multiplication by the
fixed reference root factor, yields the literal two coefficients used
by the regular root flow. Their reference difference and every mixed
spatial derivative have towers on this same parameter neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {W : N04RealizationStart} {m : ℕ} {side : Bool}
  (B : NegativeRootCollar W m side)

abbrev drift (z : AnnularState W.S × ℝ) (p : PolarPoint) : ℝ :=
  orientedCharacteristicDrift (stateProfile W.D W.S W.C z.1)
    (stateHeight W.D W.S W.C z) B.root B.orientation p

abbrev speed (z : AnnularState W.S × ℝ) (p : PolarPoint) : ℝ :=
  factoredCharacteristicSpeed W.D.w B.factor (stateProfile W.D W.S W.C z.1)
    (stateHeight W.D W.S W.C z) B.root B.orientation p

abbrev referenceSpeed (p : PolarPoint) : ℝ :=
  referenceRootSpeedFactor W.D.w B.factor B.root B.orientation p.1

abbrev coefficientDifference (z : AnnularState W.S × ℝ) (p : PolarPoint) : PolarPoint :=
  (B.drift z p, B.speed z p - B.referenceSpeed p)

/-- The spatial affine pullback is proved with its source family opaque,
so specialization does not unfold the selected physical fields. -/
def jointRootShift
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {Ω V : Set PolarPoint} {f : X × PolarPoint → PolarPoint}
    (hU : IsOpen U) (hV : IsOpen V) (r σ : ℝ)
    (hm : MapsTo (rootProfileShift r σ) V Ω)
    (J : SmoothDirections (U ×ˢ Ω) f) :
    SmoothDirections (U ×ˢ V) (fun x => f (x.1, rootProfileShift r σ x.2)) := by
  let Q : PolarPoint →L[ℝ] PolarPoint :=
    (σ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : (X × PolarPoint) →L[ℝ] X × PolarPoint :=
    (ContinuousLinearMap.fst ℝ X PolarPoint).prod
      (Q.comp (ContinuousLinearMap.snd ℝ X PolarPoint))
  let c : X × PolarPoint := (0, (r, 0))
  have he (x : X × PolarPoint) : c + P x = (x.1, rootProfileShift r σ x.2) := by
    simp only [c, P, Q, rootProfileShift, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul, Prod.mk_add_mk, zero_add]
  have hmap : MapsTo (fun x => c + P x) (U ×ˢ V) (U ×ˢ Ω) := by
    intro x hx
    change c + P x ∈ _
    rw [he x]
    exact ⟨hx.1, hm hx.2⟩
  apply (J.compAffine P c (hU.prod hV) hmap).congrOn
  intro x hx
  exact congrArg f (he x)

/-- Both coordinates are actual physical coefficients at the shifted
point, with the entire open collar retained. -/
def physicalFieldsJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n06PhysicalRootFields W.D W.S W.C (liftSectorParameter W.S W.C x.1)
          (rootProfileShift B.root B.orientation x.2)) :=
  jointRootShift
    (sectorNeighborhood_isOpen W.S W.base W.negativeRootParameterRadius
      W.negativeRootParameterRadius) B.strip_isOpen B.root B.orientation
    (fun _ hp => B.shift_mem_physicalStrip hp)
    (W.rootProfileLocus_physicalFieldsJointTower B.physicalStrip
      B.physicalStrip_isOpen (fun _ hp => (B.physicalStrip_properties hp).1)
      (fun z _ hp => (B.physicalStrip_properties hp).2 z))

def referenceSpeedJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint => B.referenceSpeed x.2) := by
  let π : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] PolarPoint :=
    ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint
  have hU : IsOpen (W.negativeRootParameterDomain ×ˢ B.strip) :=
    (sectorNeighborhood_isOpen W.S W.base W.negativeRootParameterRadius
      W.negativeRootParameterRadius).prod B.strip_isOpen
  let J := smoothDirectionsOfContDiffOn B.strip_isOpen B.referenceFactor_contDiff
  apply (J.compAffine π 0 hU (fun x hx => by
    simpa only [zero_add, π, ContinuousLinearMap.coe_snd'] using hx.2)).congrOn
  intro x hx
  simp only [zero_add, π, ContinuousLinearMap.coe_snd']

def driftJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        B.drift (liftSectorParameter W.S W.C x.1) x.2) := by
  apply (solveSmoothDirectionsPostcomp B.physicalFieldsJointTower
    (B.orientation • ContinuousLinearMap.fst ℝ ℝ ℝ)).congrOn
  intro x hx
  rfl

def speedJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        B.speed (liftSectorParameter W.S W.C x.1) x.2) := by
  let J := solveSmoothDirectionsPostcomp B.physicalFieldsJointTower
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  apply (smoothDirections_realMul B.referenceSpeedJointTower J).congrOn
  intro x hx
  have hp := B.point x.2.1 hx.2.1
  have hw : W.D.w (rootProfileShift B.root B.orientation x.2).1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hp.1).ne'
  exact (n06_factoredRootFields_eq_physical W.D W.S W.C
    (liftSectorParameter W.S W.C x.1) B.factor B.root B.orientation x.2 hw).2.symm

/-- The reference speed is subtracted before taking any derivative. -/
def speedDifferenceJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        B.speed (liftSectorParameter W.S W.C x.1) x.2 - B.referenceSpeed x.2) :=
  solveSmoothDirectionsPostcomp
    (smoothDirectionsProd B.speedJointTower B.referenceSpeedJointTower)
    (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)

def coefficientDifferenceJointTower :
    SmoothDirections (W.negativeRootParameterDomain ×ˢ B.strip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        B.coefficientDifference (liftSectorParameter W.S W.C x.1) x.2) :=
  smoothDirectionsProd B.driftJointTower B.speedDifferenceJointTower

/-- Exact cancellation holds for every height state at scalar parameter
zero, throughout the two-sided root collar. -/
theorem coefficients_zero_parameter (z : AnnularState W.S)
    {p : PolarPoint} (hp : p ∈ B.strip) :
    B.drift (z, 0) p = 0 ∧ B.speed (z, 0) p = B.referenceSpeed p := by
  have hB := B.point p.1 hp.1
  have hpAnn : rootProfileShift B.root B.orientation p ∈ annularOpen W.D :=
    ⟨hB.1, mem_univ _⟩
  have he := W.rootPhysicalFields_zero_parameter_of_profile z hpAnn (hB.2.2 z)
  have hw : W.D.w (rootProfileShift B.root B.orientation p).1 ≠ 0 :=
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hB.1).ne'
  have hf := n06_factoredRootFields_eq_physical W.D W.S W.C
    (z, 0) B.factor B.root B.orientation p hw
  simpa only [he, mul_zero, mul_one] using hf

theorem coefficientDifference_zero_parameter (z : AnnularState W.S)
    {p : PolarPoint} (hp : p ∈ B.strip) :
    B.coefficientDifference (z, 0) p = 0 := by
  have h := B.coefficients_zero_parameter z hp
  simp only [coefficientDifference, h.1, h.2, sub_self, Prod.zero_eq_mk]

def coefficientDifferenceMixedRegularity (A : PolarPoint →L[ℝ] ℝ) :
    MixedJetRegularity W.negativeRootParameterDomain B.strip
      (fun z p => A (B.coefficientDifference (liftSectorParameter W.S W.C z) p)) :=
  n04Realization_jointMixedRegularity
    (solveSmoothDirectionsPostcomp B.coefficientDifferenceJointTower A)
    (sectorNeighborhood_isOpen W.S W.base W.negativeRootParameterRadius
      W.negativeRootParameterRadius) B.strip_isOpen
    ((sectorNeighborhood_convex W.S W.base W.negativeRootParameterRadius
      W.negativeRootParameterRadius).prod ((convex_Ioo _ _).prod convex_univ))

/-- Finite affine restrictions are ordinary smooth maps of the actual
coefficient differences, including their spatial variables. -/
theorem coefficientDifference_contDiffOn_finiteAffine
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (x₀ : (StateDirections W.S × ℝ) × PolarPoint)
    (L : X →L[ℝ] (StateDirections W.S × ℝ) × PolarPoint) :
    ContDiffOn ℝ ∞
      (fun y => B.coefficientDifference
        (liftSectorParameter W.S W.C (x₀ + L y).1) (x₀ + L y).2)
      ((fun y => x₀ + L y) ⁻¹' (W.negativeRootParameterDomain ×ˢ B.strip)) :=
  smoothDirections_contDiffOn_finiteAffine B.coefficientDifferenceJointTower x₀ L

end ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar.coefficientDifferenceJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeRootCollar.coefficientDifferenceJointTower
