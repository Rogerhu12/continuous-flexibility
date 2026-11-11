import ContinuousFlexibility.Analysis.N01FlowAngularVariation
import ContinuousFlexibility.Analysis.ScalarFlowSmoothness

/-!
# Smooth angular dependence of the actual N01 flow

The actual characteristic angular derivative is a sum of smooth angular
fields with a continuous radial multiplier.  Every angular jet is jointly
continuous after the radial coordinate is clamped to the closed component.
The scalar variational bootstrap therefore proves smoothness of the actual
endpoint return, with no extra regularity premise.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

section ActualCoefficients

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

theorem N01Properties.characteristicAngularDerivative_angularRegular
    (m : ℕ) (hab : C.left m ≤ C.right m) (n : ℕ) :
    Analysis.AngularRegular n (fun r θ =>
      Analysis.closedStripExtend hab (characteristicAngularDerivative D S C z) (r, θ)) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hcore {p : PolarPoint} (hp : p.1 ∈ Icc (C.left m) (C.right m)) :
      p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans_le hp.1, hp.2.trans_lt (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hAθ : ∀ p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (angularPartial (stateCharacteristicDrift D S C z)) p := by
    intro p hp
    have hA := (N01Properties.characteristic_factors_contDiffAt hN01 hS hT hz hsector
      (hcore (p := p) hp.1)).1
    exact contDiffAt_angularPartial hA (m := ∞) (by simp)
  have hBθ : ∀ p ∈ Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (angularPartial (characteristicAngularFactor D S C z)) p := by
    intro p hp
    have hB := (N01Properties.characteristic_factors_contDiffAt hN01 hS hT hz hsector
      (hcore (p := p) hp.1)).2
    exact contDiffAt_angularPartial hB (m := ∞) (by simp)
  have hk : ContinuousOn (characteristicRadialRoot D S C z) (Icc (C.left m) (C.right m)) :=
    fun r hr => (N01Properties.characteristicRadialRoot_continuousAt hN01 hS hT
      (z := z) (hcore (p := (r, 0)) hr).1).continuousWithinAt
  have hρ : Continuous (fun r : ℝ => (projIcc (C.left m) (C.right m) hab r : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hke : Continuous (fun r : ℝ =>
      characteristicRadialRoot D S C z (projIcc (C.left m) (C.right m) hab r)) :=
    hk.comp_continuous hρ (fun r => (projIcc (C.left m) (C.right m) hab r).property)
  have hAr := Analysis.angularRegular_closedStripExtend_of_contDiffAt hab
    (angularPartial (stateCharacteristicDrift D S C z)) hAθ n
  have hBr := Analysis.angularRegular_closedStripExtend_of_contDiffAt hab
    (angularPartial (characteristicAngularFactor D S C z)) hBθ n
  have hkr := Analysis.angularRegular_time n _ hke
  exact (hAr.sub (hkr.mul hBr)).congr fun r θ => rfl

end ActualCoefficients

/-- Actual angular smoothness holds at every radius in the closed
component, in particular at the return radius used in N02. -/
theorem N01Properties.minusFlow_angular_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    ContDiff ℝ ∞ (C.minusFlow z m r) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  exact Analysis.scalar_flow_angular_contDiff_of_angularRegular
    (v := fun s x => minusCharacteristicSpeed (originalCoefficients D S C z) (s, x))
    (d := fun s x => characteristicAngularDerivative D S C z (s, x))
    (hcontrol.1 m).2.1
    (fun n => N01Properties.characteristicAngularDerivative_angularRegular
      hN01 hS hT hz hsector m (hcontrol.1 m).2.1.le n)
    (fun s hs x => N01Properties.minusCharacteristicSpeed_hasDerivAt_angular
      hN01 hS hT hz hsector
      ⟨(hcontrol.1 m).1.trans_le hs.1, hs.2.trans_lt (hcontrol.1 m).2.2⟩ x)
    (N01Properties.minusFlow_continuousOn hN01 hz m)
    (fun x => (hflow z hz m x).1)
    (fun x s hs => (hflow z hz m x).2.2.1 s hs) hr

/-- All actual angular jets are jointly continuous on the closed
component; this is the input for radial smoothness bootstrapping. -/
theorem N01Properties.minusFlow_angular_iteratedDeriv_continuousOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    (n : ℕ) :
    ContinuousOn (fun p : PolarPoint => iteratedDeriv n (C.minusFlow z m p.1) p.2)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  exact Analysis.scalar_flow_angular_iteratedDeriv_continuousOn
    (v := fun s x => minusCharacteristicSpeed (originalCoefficients D S C z) (s, x))
    (d := fun s x => characteristicAngularDerivative D S C z (s, x))
    (hcontrol.1 m).2.1
    (fun n => N01Properties.characteristicAngularDerivative_angularRegular
      hN01 hS hT hz hsector m (hcontrol.1 m).2.1.le n)
    (fun s hs x => N01Properties.minusCharacteristicSpeed_hasDerivAt_angular
      hN01 hS hT hz hsector
      ⟨(hcontrol.1 m).1.trans_le hs.1, hs.2.trans_lt (hcontrol.1 m).2.2⟩ x)
    (N01Properties.minusFlow_continuousOn hN01 hz m)
    (fun x => (hflow z hz m x).1)
    (fun x s hs => (hflow z hz m x).2.2.1 s hs) n

end ContinuousFlexibility.Statements
