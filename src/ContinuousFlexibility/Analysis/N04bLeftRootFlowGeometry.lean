import ContinuousFlexibility.Analysis.N04bSymmetricRootField
import ContinuousFlexibility.Analysis.N04bRootOrientation
import ContinuousFlexibility.Analysis.N04bRootFlowIdentification

/-!
# The actual corrected flow on a left root collar

The factorization is constructed from the N01 height and the uniform N03
coefficient germ. The stored L.minusFlow supplies only its initial value,
closed radial continuity and its actual interior differential equation.
The smooth periodic Picard flow then proves the angular geometry of the
stored family, including the actual chosen inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Construct one genuine left collar on which the stored corrected flow
solves the smooth-factor root equation. The root orientation is derived
from the primitive profile rather than assumed. -/
theorem n04b_exists_left_root_symmetric_flow_equations_with_halfGap
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m + ρ < C.right m ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      (∀ θ, L.minusFlow z m (C.left m + 0) θ = θ) ∧
      (∀ θ, ContinuousOn (fun x => L.minusFlow z m (C.left m + x) θ)
        (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (fun y => L.minusFlow z m (C.left m + y) θ)
          (rootPhysicalSpeed d c₀ (-1) (x, L.minusFlow z m (C.left m + x) θ)) x) ∧
      (∀ x ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
        Real.sqrt x * c₀ (x, θ) =
          n04bCharacteristicHalfGap (L.coefficients z) (C.left m + x, θ)) := by
  have hcontrol : controlGeometryConditions D S C := h03.1.1.2.2.2.1
  have hbounds := hcontrol.1 m
  have hroot := hcontrol.2.1 m
  have hr : C.left m ∈ Ioo D.a D.b :=
    ⟨hbounds.1, hbounds.2.1.trans hbounds.2.2⟩
  have hsign : (1 : ℝ) * deriv (deriv D.w) (C.left m) < 0 := by
    simpa only [one_mul] using (n04b_component_root_orientations h03.1.1 m).1
  obtain ⟨η, d, c₀, hη, hd, hc, hdp, hcp, hdodd, hceven, hcpos, hphysical⟩ :=
    n04b_exists_symmetric_corrected_root_factors hT hS h03 hL hz hs hr hroot.1 hsign
  let ρ : ℝ := min η ((C.right m - C.left m) / 2)
  have hρ : 0 < ρ := lt_min_iff.mpr ⟨hη, half_pos (sub_pos.mpr hbounds.2.1)⟩
  have hρη : ρ ≤ η := min_le_left _ _
  have hsmall : C.left m + ρ < C.right m := by
    have hhalf : ρ ≤ (C.right m - C.left m) / 2 := min_le_right _ _
    linarith [hbounds.2.1]
  have hflow := h03.2.2.2.2.2.1 z hz hs m
  refine ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos, ?_, ?_, ?_, ?_⟩
  · intro θ
    simpa only [add_zero] using (hflow θ).1
  · intro θ
    apply (hflow θ).2.1.comp (continuous_const.add continuous_id).continuousOn
    intro x hx
    change C.left m + x ∈ Icc (C.left m) (C.right m)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro θ x hx
    have hxC : C.left m + x ∈ Ioo (C.left m) (C.right m) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hactual :
        HasDerivAt (fun y => L.minusFlow z m (C.left m + y) θ)
          (minusCharacteristicSpeed (L.coefficients z)
            (C.left m + x, L.minusFlow z m (C.left m + x) θ)) x := by
      simpa only [Function.comp_def, mul_one] using
        ((hflow θ).2.2.1 (C.left m + x) hxC).comp x
          ((hasDerivAt_id x).const_add (C.left m))
    apply hactual.congr_deriv
    have hp : (x, L.minusFlow z m (C.left m + x) θ) ∈
        Icc (0 : ℝ) η ×ˢ (univ : Set ℝ) :=
      ⟨⟨hx.1.le, hx.2.le.trans hρη⟩, mem_univ _⟩
    have heq := (hphysical _ hp).2.1
    simp only [rootProfileShift, one_mul] at heq
    rw [heq]
    dsimp only [rootPhysicalSpeed]
    ring
  · intro x hx θ
    have hp : (x, θ) ∈ Icc (0 : ℝ) η ×ˢ (univ : Set ℝ) :=
      ⟨⟨hx.1, hx.2.trans hρη⟩, mem_univ _⟩
    have hm := (hphysical (x, θ) hp).2.1
    have hp' := (hphysical (x, θ) hp).2.2
    simp only [rootProfileShift, one_mul] at hm hp'
    dsimp only [minusCharacteristicSpeed, plusCharacteristicSpeed,
      n04bCharacteristicHalfGap] at hm hp' ⊢
    linarith only [hm, hp']

/-- Projection retaining the established actual root-flow interface. -/
theorem n04b_exists_left_root_symmetric_flow_equations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m + ρ < C.right m ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ r θ, d (r, -θ) = -d (r, θ)) ∧
      (∀ r θ, c₀ (r, -θ) = c₀ (r, θ)) ∧
      (∀ p, 0 < c₀ p) ∧
      (∀ θ, L.minusFlow z m (C.left m + 0) θ = θ) ∧
      (∀ θ, ContinuousOn (fun x => L.minusFlow z m (C.left m + x) θ)
        (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (fun y => L.minusFlow z m (C.left m + y) θ)
          (rootPhysicalSpeed d c₀ (-1) (x, L.minusFlow z m (C.left m + x) θ)) x) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
      hi, hcont, hflow, _⟩ :=
    n04b_exists_left_root_symmetric_flow_equations_with_halfGap hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hdodd, hceven, hcpos,
    hi, hcont, hflow⟩

/-- The same actual root equation, projected to the data needed for
ordinary angular regularity and interior continuation. -/
theorem n04b_exists_left_root_flow_equations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ (ρ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < ρ ∧ C.left m + ρ < C.right m ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ c₀ ∧
      (∀ r, Function.Periodic (fun θ => d (r, θ)) Real.pi) ∧
      (∀ r, Function.Periodic (fun θ => c₀ (r, θ)) Real.pi) ∧
      (∀ θ, L.minusFlow z m (C.left m + 0) θ = θ) ∧
      (∀ θ, ContinuousOn (fun x => L.minusFlow z m (C.left m + x) θ)
        (Icc (0 : ℝ) ρ)) ∧
      (∀ θ x, x ∈ Ioo (0 : ℝ) ρ →
        HasDerivAt (fun y => L.minusFlow z m (C.left m + y) θ)
          (rootPhysicalSpeed d c₀ (-1) (x, L.minusFlow z m (C.left m + x) θ)) x) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, _, _, _, hi, hcont, hflow⟩ :=
    n04b_exists_left_root_symmetric_flow_equations hT hS h03 hL hz hs m
  exact ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hi, hcont, hflow⟩

/-- The stored corrected flow, at every radial point of one closed left
collar, is a genuine smooth increasing circle lift with smooth increasing
inverse. It is also jointly smooth at all positive radial points. -/
theorem n04b_exists_left_root_flow_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ C.left m + ρ < C.right m ∧
      (∀ r ∈ Icc (C.left m) (C.left m + ρ),
        let f : ℝ → ℝ := L.minusFlow z m r
        let g : ℝ → ℝ := Function.invFun f
        ContDiff ℝ ∞ f ∧ (∀ θ, 0 < deriv f θ) ∧
          (∀ θ, f (θ + Real.pi) = f θ + Real.pi) ∧ Function.Bijective f ∧
          ContDiff ℝ ∞ g ∧ (∀ θ, 0 < deriv g θ) ∧
          (∀ θ, f (g θ) = θ ∧ g (f θ) = θ) ∧
          (∀ θ, g (θ + Real.pi) = g θ + Real.pi)) ∧
      ContDiffOn ℝ ∞ (fun p : PolarPoint => L.minusFlow z m p.1 p.2)
        (Ioo (C.left m) (C.left m + ρ) ×ˢ univ) := by
  obtain ⟨ρ, d, c₀, hρ, hsmall, hd, hc, hdp, hcp, hi, hcont, hflow⟩ :=
    n04b_exists_left_root_flow_equations hT hS h03 hL hz hs m
  let Φ : ℝ → ℝ → ℝ := fun θ x => L.minusFlow z m (C.left m + x) θ
  refine ⟨ρ, hρ, hsmall, ?_, ?_⟩
  · intro r hr
    have hx : r - C.left m ∈ Icc (0 : ℝ) ρ := by
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hh := n04b_rootStoredFlow_angular_geometry (Φ := Φ)
      hρ Real.pi_ne_zero hd hc hdp hcp hi hcont hflow hx
    have he : C.left m + (r - C.left m) = r := by ring
    simpa only [Φ, he] using hh
  · have hlocal : ContDiffOn ℝ ∞ (fun p : PolarPoint => Φ p.2 p.1)
        (Ioo (0 : ℝ) ρ ×ˢ univ) :=
      n04b_rootStoredFlow_contDiffOn hρ Real.pi_ne_zero hd hc hdp hcp hi hcont hflow
    have hshift : ContDiff ℝ ∞
        (fun p : PolarPoint => (p.1 - C.left m, p.2)) :=
      (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    have hmaps : MapsTo (fun p : PolarPoint => (p.1 - C.left m, p.2))
        (Ioo (C.left m) (C.left m + ρ) ×ˢ (univ : Set ℝ))
        (Ioo (0 : ℝ) ρ ×ˢ univ) := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩
    apply (hlocal.comp hshift.contDiffOn hmaps).congr
    intro p _
    have he : C.left m + (p.1 - C.left m) = p.1 := by ring
    simp only [Function.comp_def, Φ, he]

end ContinuousFlexibility.Analysis
