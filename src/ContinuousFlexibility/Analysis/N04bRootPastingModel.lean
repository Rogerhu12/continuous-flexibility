module

public import ContinuousFlexibility.Analysis.N04bMatchedRootCollars
public import ContinuousFlexibility.Analysis.N04bRootCollarDomain

/-!
# Actual local data for literal root pasting

A matched smooth root collar is shrunk using its genuine uniform radial
bound. Its physical positive side then lies in the actual moving half.
This constructs the local inputs of the pasting theorem from Through03.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

structure N04bRootPastingModel (r₀ : ℝ) (side : Bool)
    (Ω : Set PolarPoint) (Fphysical : PolarPoint → PolarPoint)
    (hphysical : PolarPoint → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  rootChart : PolarPoint → PolarPoint
  rootHeight : PolarPoint → ℝ
  radialFactor : PolarPoint → ℝ
  chart_smooth : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ),
    ContDiffAt ℝ ∞ rootChart p
  height_smooth : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ),
    ContDiffAt ℝ ∞ rootHeight p
  jacobian_pos : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ),
    0 < planeJacobian rootChart p
  angle_pos : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ),
    0 < angularPartial (fun q => (rootChart q).2) p
  factor_pos : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ), 0 < radialFactor p
  height_pos : ∀ p ∈ Ioo (-radius) radius ×ˢ (univ : Set ℝ), 0 < rootHeight p
  factor : ∀ p, (rootChart p).1 = p.1 * radialFactor p
  period : ∀ r θ, rootChart (r, θ + Real.pi) = rootChart (r, θ) + (0, Real.pi)
  axis : ∀ θ, (rootChart (0, θ)).1 = 0
  physical : MapsTo (n04bRootAffine r₀ side).symm
    ((Ioo (-radius) radius ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1}) Ω
  chart_match : EqOn (fun q => Fphysical ((n04bRootAffine r₀ side).symm q)) rootChart
    ((Ioo (-radius) radius ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1})
  height_match : EqOn (fun q => hphysical ((n04bRootAffine r₀ side).symm q)) rootHeight
    ((Ioo (-radius) radius ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1})

/-- A single construction handles either physical orientation. -/
theorem n04b_rootPastingModel_of_matched_collar
    {d c₀ : PolarPoint → ℝ} {hL : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    {ρ σ : ℝ} {G : ℝ × ℝ × ℝ → ℝ}
    (H : N04bRootCoordinateProperties d c₀ hL Φ ρ σ G)
    {Ω : Set PolarPoint} {F : PolarPoint → PolarPoint}
    {A : SymmetricCoefficients} {v aroot : PolarPoint → ℝ}
    {T r₀ δ : ℝ} (hT : 0 < T) (side : Bool) (hδ : 0 < δ)
    (hF : MapsTo F Ω (Ioo (0 : ℝ) T ×ˢ univ))
    (hReg : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (extendedRootEvenOddChart G) p ∧
        0 < extendedRootOddCoefficient G p ∧
        0 < planeJacobian (extendedRootEvenOddChart G) p ∧
        0 < angularPartial (extendedRootEven G) p ∧
        ContDiffAt ℝ ∞ (rootSmoothHeight aroot G) p ∧
        0 < rootSmoothHeight aroot G p)
    (hPhysical : MapsTo (n04bRootAffine r₀ side).symm (Ioo (0 : ℝ) δ ×ˢ univ) Ω)
    (hChart : EqOn
      (fun q => n04bRootPhysicalChart F T side ((n04bRootAffine r₀ side).symm q))
      (extendedRootEvenOddChart G)
      ((Ioo (-δ) δ ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1}))
    (hHeight : EqOn
      (fun q => n04bRootPhysicalHeight A v F T side ((n04bRootAffine r₀ side).symm q))
      (rootSmoothHeight aroot G)
      ((Ioo (-δ) δ ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1})) :
    Nonempty (N04bRootPastingModel r₀ side (n04bTravelHalfDomain Ω F T side)
      (n04bRootPhysicalChart F T side) (n04bRootPhysicalHeight A v F T side)) := by
  obtain ⟨η, hη, hBound⟩ := H.exists_uniform_first_lt (n04bRootCutRadius_pos hT)
  let ε := min δ η
  have hε : 0 < ε := lt_min_iff.mpr ⟨hδ, hη⟩
  have hSub : Ioo (-ε) ε ×ˢ (univ : Set ℝ) ⊆ Ioo (-δ) δ ×ˢ univ := by
    intro p hp
    have heδ : ε ≤ δ := min_le_left _ _
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩
  have hSubPos :
      ((Ioo (-ε) ε ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1}) ⊆
        ((Ioo (-δ) δ ×ˢ univ) ∩ {p : PolarPoint | 0 < p.1}) :=
    fun _ hp => ⟨hSub hp.1, hp.2⟩
  refine ⟨{
    radius := ε
    radius_pos := hε
    rootChart := extendedRootEvenOddChart G
    rootHeight := rootSmoothHeight aroot G
    radialFactor := extendedRootRadialFactor G
    chart_smooth := fun p hp => (hReg p (hSub hp)).1
    height_smooth := fun p hp => (hReg p (hSub hp)).2.2.2.2.1
    jacobian_pos := fun p hp => (hReg p (hSub hp)).2.2.1
    angle_pos := fun p hp => (hReg p (hSub hp)).2.2.2.1
    factor_pos := fun p hp => Real.rpow_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 3 / 2) (hReg p (hSub hp)).2.1) _
    height_pos := fun p hp => (hReg p (hSub hp)).2.2.2.2.2
    factor := fun _ => rfl
    period := H.extended_chart_period
    axis := fun θ => congrArg Prod.fst (H.extended_chart_zero θ)
    physical := ?_
    chart_match := fun _ hp => hChart (hSubPos hp)
    height_match := fun _ hp => hHeight (hSubPos hp)
  }⟩
  intro p hp
  have hPhysicalPoint := hPhysical ⟨⟨hp.2, (hSub hp.1).1.2⟩, mem_univ _⟩
  apply n04b_mem_travelHalf_of_rootCoordinate_mem hT side hF hPhysicalPoint
  have hChartPoint :
      n04bRootPhysicalChart F T side ((n04bRootAffine r₀ side).symm p) =
        extendedRootEvenOddChart G p := hChart (hSubPos hp)
  have hRadius :
      (n04bRootPhysicalChart F T side ((n04bRootAffine r₀ side).symm p)).1 =
        (extendedRootEvenOddChart G p).1 := congrArg Prod.fst hChartPoint
  rw [hRadius]
  refine ⟨n04b_extended_root_first_pos hp.2 (hReg p (hSub hp.1)).2.1, ?_⟩
  apply hBound p.1 p.2
  exact (abs_lt.mpr hp.1.1).trans_le (min_le_right _ _)

theorem n04b_exists_actual_rootPastingModel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) :
    Nonempty (N04bRootPastingModel (if side then C.right m else C.left m) side
      (n04bTravelHalfDomain (Ioo (C.left m) (C.right m) ×ˢ univ)
        (n04bActualTravelChart S C L z m) (C.travel m) side)
      (n04bRootPhysicalChart (n04bActualTravelChart S C L z m) (C.travel m) side)
      (n04bRootPhysicalHeight (L.coefficients z)
        (n04bCharacteristicHalfGap (L.coefficients z))
        (n04bActualTravelChart S C L z m) (C.travel m) side)) := by
  have hTravel := n04b_actualTravel_positive hN hS hT hfield hz hs m
  have hMaps := (n04b_actualTravelChart_bijOn hN hS hT hfield hz hs m).mapsTo
  cases side with
  | false =>
    obtain ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hδ, hδρ, hcollar, hmatch⟩ :=
      n04b_exists_left_matched_root_collar hT hS hN hfield hz hs m
    apply n04b_rootPastingModel_of_matched_collar H hTravel false hδ hMaps
    · intro p hp
      obtain ⟨_, hf, hχ, hJ, ha, _, hh, hhpos, _⟩ :=
        hcollar p.1 p.2 (abs_lt.mpr hp.1)
      exact ⟨hf, hχ, hJ, ha, hh, hhpos⟩
    · intro p hp
      have hpoint : (C.left m + p.1, p.2) ∈
          Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
        ⟨⟨by linarith only [hp.1.1],
          by linarith only [hp.1.2, hδρ, hspan]⟩, mem_univ _⟩
      simpa [n04bRootAffine_symm_apply, rootProfileShift] using hpoint
    · intro p hp
      simpa [n04bRootAffine_symm_apply, rootProfileShift] using
        (hmatch p.1 ⟨hp.2, hp.1.1.2⟩ p.2).1.symm
    · intro p hp
      simpa [n04bRootAffine_symm_apply, rootProfileShift] using
        (hmatch p.1 ⟨hp.2, hp.1.1.2⟩ p.2).2.symm
  | true =>
    obtain ⟨ρ, δ, d, c₀, G, hρ, hspan, H, hδ, hδρ, hcollar, hmatch⟩ :=
      n04b_exists_right_matched_root_collar hT hS hN hfield hz hs m
    apply n04b_rootPastingModel_of_matched_collar H hTravel true hδ hMaps
    · intro p hp
      obtain ⟨_, hf, hχ, hJ, ha, _, hh, hhpos, _⟩ :=
        hcollar p.1 p.2 (abs_lt.mpr hp.1)
      exact ⟨hf, hχ, hJ, ha, hh, hhpos⟩
    · intro p hp
      have hpoint : (C.right m - p.1, p.2) ∈
          Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) :=
        ⟨⟨by linarith only [hp.1.2, hδρ, hspan],
          by linarith only [hp.1.1]⟩, mem_univ _⟩
      simpa [n04bRootAffine_symm_apply, rootProfileShift, sub_eq_add_neg] using hpoint
    · intro p hp
      simpa [n04bRootAffine_symm_apply, rootProfileShift, sub_eq_add_neg] using
        (hmatch p.1 ⟨hp.2, hp.1.1.2⟩ p.2).1.symm
    · intro p hp
      simpa [n04bRootAffine_symm_apply, rootProfileShift, sub_eq_add_neg] using
        (hmatch p.1 ⟨hp.2, hp.1.1.2⟩ p.2).2.symm

end ContinuousFlexibility.Analysis
