import ContinuousFlexibility.Analysis.N04bCharacteristicFlowJets
import ContinuousFlexibility.Analysis.N01FlowAngularVariation

/-!
# Actual angular jets of the original characteristic speed

The N01 separation writes the speed as two smooth angular fields with a
continuous radial multiplier. This proves angular smoothness and joint
continuity of every angular jet on the entire physical annulus, including
the turning radii. No radial smoothness of the square root is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

/-- The compact radial interval may cross a turning radius. -/
theorem N01Properties.minusCharacteristicSpeed_angularRegular_on_subinterval
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ Ioo D.a D.b) (n : ℕ) :
    AngularRegular n (fun r θ =>
      closedStripExtend hab (minusCharacteristicSpeed (originalCoefficients D S C z))
        (r, θ)) := by
  have hA : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (stateCharacteristicDrift D S C z) p :=
    fun p hp => (hN01.characteristic_factors_contDiffAt hS hT hz hsector
      ⟨hI hp.1, hp.2⟩).1
  have hB : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (characteristicAngularFactor D S C z) p :=
    fun p hp => (hN01.characteristic_factors_contDiffAt hS hT hz hsector
      ⟨hI hp.1, hp.2⟩).2
  have hk : ContinuousOn (characteristicRadialRoot D S C z) (Icc a b) :=
    fun r hr => (hN01.characteristicRadialRoot_continuousAt hS hT
      (z := z) (hI hr)).continuousWithinAt
  have hρ : Continuous (fun r : ℝ => (projIcc a b hab r : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hke : Continuous (fun r : ℝ =>
      characteristicRadialRoot D S C z (projIcc a b hab r)) :=
    hk.comp_continuous hρ (fun r => (projIcc a b hab r).property)
  have hAr := angularRegular_closedStripExtend_of_contDiffAt hab
    (stateCharacteristicDrift D S C z) hA n
  have hBr := angularRegular_closedStripExtend_of_contDiffAt hab
    (characteristicAngularFactor D S C z) hB n
  have hkr := angularRegular_time n _ hke
  apply (hAr.sub (hkr.mul hBr)).congr
  intro r θ
  exact hN01.minusCharacteristicSpeed_eq_separated hS hT hz hsector
    ⟨hI (projIcc a b hab r).property, mem_univ _⟩

private theorem n04b_originalSpeed_local_clamp
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ∃ a b : ℝ, ∃ hab : a ≤ b, r ∈ Ioo a b ∧
      ∀ n : ℕ, AngularRegular n (fun s θ =>
        closedStripExtend hab (minusCharacteristicSpeed (originalCoefficients D S C z))
          (s, θ)) := by
  let a := (D.a + r) / 2
  let b := (r + D.b) / 2
  have ha : D.a < a ∧ a < r := by
    dsimp only [a]
    constructor <;> linarith [hr.1]
  have hb : r < b ∧ b < D.b := by
    dsimp only [b]
    constructor <;> linarith [hr.2]
  have hab : a ≤ b := (ha.2.trans hb.1).le
  refine ⟨a, b, hab, ⟨ha.2, hb.1⟩, fun n => ?_⟩
  exact hN01.minusCharacteristicSpeed_angularRegular_on_subinterval hS hT hz hsector hab
    (fun s hs => ⟨ha.1.trans_le hs.1, hs.2.trans_lt hb.2⟩) n

theorem N01Properties.minusCharacteristicSpeed_angular_contDiff
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContDiff ℝ ∞ (fun θ => minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ)) := by
  obtain ⟨a, b, hab, hrab, hreg⟩ := n04b_originalSpeed_local_clamp hN01 hS hT hz hsector hr
  have hs := contDiff_of_angularRegular_all hreg r
  have he : (fun θ => closedStripExtend hab
      (minusCharacteristicSpeed (originalCoefficients D S C z)) (r, θ)) =
      (fun θ => minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ)) := by
    funext θ
    exact closedStripExtend_eq hab _ ⟨hrab.1.le, hrab.2.le⟩
  rw [he] at hs
  exact hs

theorem N01Properties.minusCharacteristicSpeed_angularJet_continuousAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) (n : ℕ) :
    ContinuousAt (fun q : PolarPoint => iteratedDeriv n
      (fun θ => minusCharacteristicSpeed (originalCoefficients D S C z) (q.1, θ)) q.2) p := by
  obtain ⟨a, b, hab, hrab, hreg⟩ := n04b_originalSpeed_local_clamp hN01 hS hT hz hsector hp.1
  exact n04b_angularJet_continuousAt_of_clamp hab (hreg n) hrab

end ContinuousFlexibility.Statements
