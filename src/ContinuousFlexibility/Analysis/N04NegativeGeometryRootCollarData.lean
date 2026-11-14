module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryRootProfileJoint
public import ContinuousFlexibility.Analysis.N01ActualRootGeometry
public import ContinuousFlexibility.Analysis.RootShiftMixedJets

/-!
# A common actual collar at every negative turning root

The divided reference derivative and its collar are chosen from the
proved N01 common root-strip theorem, before the state. The data below
retain its literal profile identity and positive factored-speed bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

structure NegativeRootCollar (W : N04RealizationStart) (m : ℕ) (side : Bool) where
  factor : ℝ → ℝ
  radius : ℝ
  factor_contDiff : ContDiff ℝ ∞ factor
  factor_zero_pos : 0 < factor 0
  radius_pos : 0 < radius
  divides : ∀ t : ℝ,
    -deriv W.D.w (n01ComponentRoot W.C m side + n01ComponentRootOrientation side * t) =
      t * factor t
  point : ∀ t ∈ Ioo (-radius) radius,
    n01ComponentRoot W.C m side + n01ComponentRootOrientation side * t ∈ Ioo W.D.a W.D.b ∧
      0 < factor t ∧
      ∀ x : AnnularState W.S,
        stateProfile W.D W.S W.C x
            (n01ComponentRoot W.C m side + n01ComponentRootOrientation side * t) =
          W.D.w (n01ComponentRoot W.C m side + n01ComponentRootOrientation side * t)
  speed_bounds : ∀ z ∈ stateNeighborhood W.S W.C W.base W.ε, stateSector W.S z.1 →
    ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ),
      0 < factoredCharacteristicSpeed W.D.w factor (stateProfile W.D W.S W.C z.1)
        (stateHeight W.D W.S W.C z) (n01ComponentRoot W.C m side)
        (n01ComponentRootOrientation side) p ∧
      referenceRootSpeedFactor W.D.w factor (n01ComponentRoot W.C m side)
          (n01ComponentRootOrientation side) 0 / 4 ≤
        factoredCharacteristicSpeed W.D.w factor (stateProfile W.D W.S W.C z.1)
          (stateHeight W.D W.S W.C z) (n01ComponentRoot W.C m side)
          (n01ComponentRootOrientation side) p ∧
      factoredCharacteristicSpeed W.D.w factor (stateProfile W.D W.S W.C z.1)
          (stateHeight W.D W.S W.C z) (n01ComponentRoot W.C m side)
          (n01ComponentRootOrientation side) p ≤
        4 * referenceRootSpeedFactor W.D.w factor (n01ComponentRoot W.C m side)
          (n01ComponentRootOrientation side) 0

variable (W : N04RealizationStart)

theorem exists_negativeRootCollar (m : ℕ) (side : Bool) :
    Nonempty (NegativeRootCollar W m side) := by
  have hroot := n01_component_root_data W.through03.1.1 m side
  obtain ⟨g, δ, hg, hg0, hδ, hdivide, hpoint, hfields⟩ :=
    n01_exists_common_characteristic_root_strip W.hS W.hT W.through03.1.1
      hroot.1 hroot.2.1 hroot.2.2
  exact ⟨{
    factor := g
    radius := δ
    factor_contDiff := hg
    factor_zero_pos := hg0
    radius_pos := hδ
    divides := hdivide
    point := hpoint
    speed_bounds := fun z hz hs p hp =>
      ⟨((hfields z hz hs).2.2 p hp).1,
        ((hfields z hz hs).2.2 p hp).2.1,
        ((hfields z hz hs).2.2 p hp).2.2.1⟩ }⟩

def negativeRootCollar (m : ℕ) (side : Bool) : NegativeRootCollar W m side :=
  Classical.choice (W.exists_negativeRootCollar m side)

namespace NegativeRootCollar

variable {W : N04RealizationStart} {m : ℕ} {side : Bool}
  (B : NegativeRootCollar W m side)

abbrev root (_B : NegativeRootCollar W m side) : ℝ := n01ComponentRoot W.C m side

abbrev orientation (_B : NegativeRootCollar W m side) : ℝ := n01ComponentRootOrientation side

abbrev strip : Set PolarPoint := Ioo (-B.radius) B.radius ×ˢ univ

abbrev physicalStrip : Set PolarPoint :=
  Ioo (B.root - B.radius) (B.root + B.radius) ×ˢ univ

theorem strip_isOpen : IsOpen B.strip := isOpen_Ioo.prod isOpen_univ

theorem physicalStrip_isOpen : IsOpen B.physicalStrip := isOpen_Ioo.prod isOpen_univ

/-- The entire physical collar is a common profile locus, including its
two sides. No current state occurs in the choice of this collar. -/
theorem physicalStrip_properties {p : PolarPoint} (hp : p ∈ B.physicalStrip) :
    p ∈ annularOpen W.D ∧
      ∀ x : AnnularState W.S, stateProfile W.D W.S W.C x p.1 = W.D.w p.1 := by
  rcases n01ComponentRootOrientation_eq side with hσ | hσ
  · have ht : p.1 - B.root ∈ Ioo (-B.radius) B.radius := by
      constructor <;> linarith [hp.1.1, hp.1.2]
    have hB := B.point (p.1 - B.root) ht
    have he : n01ComponentRoot W.C m side +
        n01ComponentRootOrientation side * (p.1 - B.root) = p.1 := by
      rw [hσ]
      dsimp only [root]
      ring
    rw [he] at hB
    exact ⟨⟨hB.1, mem_univ _⟩, hB.2.2⟩
  · have ht : B.root - p.1 ∈ Ioo (-B.radius) B.radius := by
      constructor <;> linarith [hp.1.1, hp.1.2]
    have hB := B.point (B.root - p.1) ht
    have he : n01ComponentRoot W.C m side +
        n01ComponentRootOrientation side * (B.root - p.1) = p.1 := by
      rw [hσ]
      dsimp only [root]
      ring
    rw [he] at hB
    exact ⟨⟨hB.1, mem_univ _⟩, hB.2.2⟩

theorem shift_mem_physicalStrip {p : PolarPoint} (hp : p ∈ B.strip) :
    rootProfileShift B.root B.orientation p ∈ B.physicalStrip :=
  ⟨rootProfileShift_mem_symmetric_interval (n01ComponentRootOrientation_eq side) hp.1,
    mem_univ _⟩

theorem referenceFactor_contDiff :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      referenceRootSpeedFactor W.D.w B.factor B.root B.orientation p.1) B.strip := by
  intro p hp
  have hB := B.point p.1 hp.1
  have hr : 0 < B.root + B.orientation * p.1 :=
    W.through03.1.1.1.1.choose_spec.1.1.trans hB.1.1
  have hw : 0 < W.D.w (B.root + B.orientation * p.1) :=
    W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hB.1
  exact ((contDiffAt_referenceRootSpeedFactor
    W.through03.1.1.1.1.choose_spec.1.2.2.1.1 B.factor_contDiff
    hr hw hB.2.1).comp p contDiffAt_fst).contDiffWithinAt

theorem referenceFactor_pos {p : PolarPoint} (hp : p ∈ B.strip) :
    0 < referenceRootSpeedFactor W.D.w B.factor B.root B.orientation p.1 := by
  have hB := B.point p.1 hp.1
  exact referenceRootSpeedFactor_pos
    (W.through03.1.1.1.1.choose_spec.1.1.trans hB.1.1)
    (W.through03.1.1.1.1.choose_spec.1.2.2.2.2.1 _ hB.1) hB.2.1

end NegativeRootCollar

end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.exists_negativeRootCollar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.exists_negativeRootCollar
