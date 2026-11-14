module

public import ContinuousFlexibility.Analysis.N04bNegativePieceSymmetry

/-!
# Full geometric properties of the constructed negative functions

The literal pasted functions inherit both open and closed inverse
identities from the actual travel inverse. Their regularity and full
boundary germs are the proved output of the root construction. Angular
symmetries are transferred through the actual interior germs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

namespace N04bNegativePieceProperties

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  {z : AnnularState S × ℝ} {m : ℕ} {side : Bool}
  {F J : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
  (H : N04bNegativePieceProperties S C L z m side F h J)

include H

theorem component_chart_germ {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    F =ᶠ[𝓝 p] n04bRootPhysicalChart
      (n04bActualTravelChart S C L z m) (C.travel m) side :=
  H.chart_physical_germ p (n04b_rootAffine_component_pos C m side hp)

theorem component_height_germ {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    h =ᶠ[𝓝 p] n04bRootPhysicalHeight (L.coefficients z)
      (n04bCharacteristicHalfGap (L.coefficients z))
      (n04bActualTravelChart S C L z m) (C.travel m) side :=
  H.height_physical_germ p (n04b_rootAffine_component_pos C m side hp)

theorem open_chart_eq :
    EqOn F (n04bRootPhysicalChart
      (n04bActualTravelChart S C L z m) (C.travel m) side)
      (n04bActualNegativeDomain S C L z m side) :=
  fun _ hp => H.closed_chart_eq (subset_closure hp)

theorem open_inverse_eq :
    EqOn J (n04bRootPhysicalInverse
      (n04bActualTravelInverse S C L z m) (C.travel m) side)
      (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) :=
  fun q hq => (H.inverse_physical_germ q hq.1.1).self_of_nhds

variable
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hfield : N04bFieldRegularity D S C L base ε)
  (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)

include hN hS hT hfield hz hs

theorem open_chart_data :
    MapsTo F (n04bActualNegativeDomain S C L z m side)
        (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) ∧
      MapsTo J (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ))
        (n04bActualNegativeDomain S C L z m side) ∧
      (∀ p ∈ n04bActualNegativeDomain S C L z m side, J (F p) = p) ∧
      (∀ q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ),
        F (J q) = q) := by
  have hBij := n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m
  have hX := n04b_actualTravelInverse_spec hN hS hT hfield hz hs m
  obtain ⟨hf, hj, hjf, hfj⟩ := n04b_rootPhysical_chart_data
    (n04b_actualTravel_positive hN hS hT hfield hz hs m) hBij.mapsTo hX.1
    (fun _ hp => hX.2.1 hp) (fun _ hq => hX.2.2.1 hq) side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [H.open_chart_eq hp]
    exact hf hp
  · intro q hq
    rw [H.open_inverse_eq hq]
    exact hj hq
  · intro p hp
    rw [H.open_chart_eq hp, H.open_inverse_eq (hf hp)]
    exact hjf p hp
  · intro q hq
    rw [H.open_inverse_eq hq, H.open_chart_eq (hj hq)]
    exact hfj q hq

theorem closed_chart_data :
    MapsTo F (closure (n04bActualNegativeDomain S C L z m side))
        (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) ∧
      MapsTo J (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ))
        (closure (n04bActualNegativeDomain S C L z m side)) ∧
      (∀ p ∈ closure (n04bActualNegativeDomain S C L z m side), J (F p) = p) ∧
      (∀ q ∈ Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ),
        F (J q) = q) := by
  have hp : ∀ r ∈ Icc (C.left m) (C.right m), ∀ θ,
      (n04bActualTravelChart S C L z m (r, θ + Real.pi)).2 =
        (n04bActualTravelChart S C L z m (r, θ)).2 + Real.pi := by
    intro r hr θ
    exact congrArg Prod.snd
      (n04b_actualTravelChart_period_add hN hS hT hfield hz hs m hr θ)
  obtain ⟨hf, hj, hjf, hfj⟩ := n04b_rootPhysical_closure_chart_data
    (n04b_actualTravel_positive hN hS hT hfield hz hs m) Real.pi_ne_zero
    (n04b_actualTravelChart_continuous hN hS hT hfield hz hs m)
    (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m)
    (n04b_actualTravelChart_closed_bijOn hN hS hT hfield hz hs m) hp side
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [H.closed_chart_eq hp]
    exact hf hp
  · intro q hq
    rw [H.closed_inverse_eq hq]
    exact hj hq
  · intro p hp
    rw [H.closed_chart_eq hp, H.closed_inverse_eq (hf hp)]
    exact hjf p hp
  · intro q hq
    have hj' : n04bRootPhysicalInverse
        (n04bActualClosedTravelInverse S C L z m) (C.travel m) side q ∈
          closure (n04bActualNegativeDomain S C L z m side) := hj hq
    rw [H.closed_inverse_eq hq, H.closed_chart_eq hj']
    exact hfj q hq

theorem period {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    F (p + (0, Real.pi)) = F p + (0, Real.pi) ∧
      h (p + (0, Real.pi)) = h p := by
  have hp' : p + (0, Real.pi) ∈
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    simpa only [mem_prod, Prod.fst_add, add_zero, mem_univ, and_true] using hp
  constructor
  · rw [(H.component_chart_germ hp').self_of_nhds,
      (H.component_chart_germ hp).self_of_nhds]
    exact n04b_actualRootChart_period hN hS hT hfield hz hs m side
      ⟨hp.1.1.le, hp.1.2.le⟩
  · rw [(H.component_height_germ hp').self_of_nhds,
      (H.component_height_germ hp).self_of_nhds]
    exact n04b_actualRootHeight_period hN hS hT hfield hz hs m side hp

theorem charts :
    MapsTo F (n04bActualNegativeDomain S C L z m side)
        (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) ∧
      MapsTo J (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ))
        (n04bActualNegativeDomain S C L z m side) ∧
      (∀ p ∈ n04bActualNegativeDomain S C L z m side, J (F p) = p) ∧
      (∀ q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ),
        F (J q) = q) ∧
      ContDiffOn ℝ ∞ F (n04bActualNegativeDomain S C L z m side) ∧
      ContDiffOn ℝ ∞ J
        (Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ h (n04bActualNegativeDomain S C L z m side) ∧
      (∀ p ∈ n04bActualNegativeDomain S C L z m side,
        0 < h p ∧ planeJacobian F p ≠ 0 ∧
          F (p + (0, Real.pi)) = F p + (0, Real.pi) ∧
          h (p + (0, Real.pi)) = h p) := by
  obtain ⟨hf, hj, hjf, hfj⟩ := H.open_chart_data hN hS hT hfield hz hs
  refine ⟨hf, hj, hjf, hfj, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (H.closed_regular p (subset_closure hp)).1.contDiffWithinAt
  · intro q hq
    exact (H.inverse_regular q ⟨⟨hq.1.1.le, hq.1.2.le⟩, mem_univ _⟩).contDiffWithinAt
  · intro p hp
    exact (H.closed_regular p (subset_closure hp)).2.1.contDiffWithinAt
  · intro p hp
    have hr := H.closed_regular p (subset_closure hp)
    exact ⟨hr.2.2.2, hr.2.2.1, H.period hN hS hT hfield hz hs
      (n04b_actualNegativeDomain_subset_component C L z m side hp)⟩

theorem boundary :
    MapsTo F (closure (n04bActualNegativeDomain S C L z m side))
        (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) ∧
      MapsTo J (Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ))
        (closure (n04bActualNegativeDomain S C L z m side)) ∧
      (∀ p ∈ closure (n04bActualNegativeDomain S C L z m side), J (F p) = p) ∧
      (∀ q ∈ Icc (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ),
        F (J q) = q) ∧
      (∀ p ∈ closure (n04bActualNegativeDomain S C L z m side),
        ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ h p ∧ planeJacobian F p ≠ 0 ∧ 0 < h p) ∧
      (∀ p ∈ frontier (n04bActualNegativeDomain S C L z m side),
        CanonicalBoundaryInverseGerm F J p) := by
  obtain ⟨hf, hj, hjf, hfj⟩ := H.closed_chart_data hN hS hT hfield hz hs
  exact ⟨hf, hj, hjf, hfj, H.closed_regular,
    fun p hp => H.boundary_inverse p (frontier_subset_closure hp)⟩

theorem reflection {p : PolarPoint}
    (hp : p ∈ n04bActualNegativeDomain S C L z m side) :
    F (p.1, -p.2) = ((F p).1, -(F p).2) ∧
      h (p.1, -p.2) = h p ∧
      planeJacobian F (p.1, -p.2) = planeJacobian F p := by
  have hpFull := n04b_actualNegativeDomain_subset_component C L z m side hp
  have hpReflect : (p.1, -p.2) ∈
      Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := ⟨hpFull.1, mem_univ _⟩
  have hg := H.component_chart_germ hpFull
  have hgr := H.component_chart_germ hpReflect
  refine ⟨?_, ?_, ?_⟩
  · rw [hgr.self_of_nhds, hg.self_of_nhds]
    exact n04b_actualRootChart_reflection m side p
  · rw [(H.component_height_germ hpReflect).self_of_nhds,
      (H.component_height_germ hpFull).self_of_nhds]
    exact n04b_actualRootHeight_reflection hN hz hs m side p
  · have hSmooth := n04b_actualTravelChart_smooth hN hS hT hfield hz hs m
    have hMaps := (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo
    have hf := n04b_contDiffAt_rootPhysicalChart
      (hSmooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpFull))
      (n04b_travelOrientation_pos_of_fullStrip side (hMaps hpFull).1)
    have hfr := n04b_contDiffAt_rootPhysicalChart
      (hSmooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpReflect))
      (n04b_travelOrientation_pos_of_fullStrip side (hMaps hpReflect).1)
    have he (q : PolarPoint)
        (hgerm : F =ᶠ[𝓝 q] n04bRootPhysicalChart
          (n04bActualTravelChart S C L z m) (C.travel m) side) :
        planeJacobian F q =
          planeJacobian (n04bRootPhysicalChart
            (n04bActualTravelChart S C L z m) (C.travel m) side) q := by
      unfold planeJacobian
      rw [hgerm.fderiv_eq]
    rw [he _ hgr, he _ hg]
    exact n04b_planeJacobian_reflection
      (fun x η => n04b_actualRootChart_reflection m side (x, η))
      (hf.differentiableAt (by simp)) (hfr.differentiableAt (by simp))

theorem inverseReflection {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (C.travel m)) ×ˢ (univ : Set ℝ)) :
    J (q.1, -q.2) = ((J q).1, -(J q).2) := by
  rw [(H.inverse_physical_germ (q.1, -q.2) hq.1.1).self_of_nhds,
    (H.inverse_physical_germ q hq.1.1).self_of_nhds]
  exact n04b_actualRootInverse_reflection hN hS hT hfield hz hs m side hq

end N04bNegativePieceProperties

end ContinuousFlexibility.Analysis
