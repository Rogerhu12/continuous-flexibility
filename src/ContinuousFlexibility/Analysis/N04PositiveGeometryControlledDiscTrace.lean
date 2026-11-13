import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledDiscKernel
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeightFormula
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsSpatialInputs

/-!
# Genuine joint towers of the physical discriminant power traces

The N01 profile germ identifies the physical discriminant before any
ordinary radial derivative is taken. Angular derivatives of the whole
radial trace then give the same finite spatial partition formula. Each
term is a smooth function of the actual absorbed packet, so the result
is a genuine joint state and angle tower on the common neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

private theorem discKernel_trace_formula
    (u : PolarPoint → N06RootNormalizedCoordinates) (hu : ContDiff ℝ ∞ u)
    (f : PolarPoint → ℝ) (r γ : ℝ)
    (hgerm : ∀ θ, f =ᶠ[𝓝 (r, θ)] fun p => n06RootNormalizedDiscriminant (u p))
    (hpos : ∀ θ, 0 < n06RootNormalizedDiscriminant (u (r, θ)))
    (a d : ℕ) (θ : ℝ) :
    iteratedDeriv d (radialBoundaryJet (fun p => f p ^ γ) r a) θ =
      ∑ c : OrderedFinpartition (a + d), n04PositiveGeometry_rootDiscKernel γ c.length
        (n04PositiveGeometry_rootSpatialPacket c u (r, θ)
          (fun j => cylinderBasisVector (cylinderMixedWord a d j))) := by
  let V : Set N06RootNormalizedCoordinates := {v | 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous
  let Ω := u ⁻¹' V
  have hΩ : IsOpen Ω := hV.preimage hu.continuous
  have hc : ContDiffOn ℝ ∞ (fun p => n04PositiveGeometry_rootDiscPower γ (u p)) Ω := by
    intro p hp
    exact ((n04PositiveGeometry_rootDiscPower_contDiffAt γ hp).comp p
      hu.contDiffAt).contDiffWithinAt
  have hr (η : ℝ) : (r, η) ∈ Ω := hpos η
  have htrace : radialBoundaryJet (fun p => f p ^ γ) r a =
      radialBoundaryJet (fun p => n04PositiveGeometry_rootDiscPower γ (u p)) r a := by
    funext η
    have hslice : (fun x => f (x, η) ^ γ) =ᶠ[𝓝 r]
        (fun x => n04PositiveGeometry_rootDiscPower γ (u (x, η))) := by
      filter_upwards [(hgerm η).comp_tendsto
        ((continuous_id.prodMk continuous_const).tendsto r)] with x hx
      exact congrArg (fun y : ℝ => y ^ γ) hx
    exact hslice.iteratedDeriv_eq a
  rw [htrace, iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hΩ hc r hr,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hc a d (hr θ)]
  exact n04PositiveGeometry_rootDiscKernel_formula γ u hu (a + d) (r, θ)
    (fun j => cylinderBasisVector (cylinderMixedWord a d j)) (hpos θ)

local instance n04ControlledDiscTraceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

/-- The unpowered physical discriminant has the actual two-variable
normalized germ at every true turning root. -/
theorem n04PositiveGeometry_rootDiscriminant_germ_eq_absorbed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0) (θ : ℝ) :
    (fun p => polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p)
      =ᶠ[𝓝 (r, θ)] n06RootNormalizedDiscriminant ∘ n06ActualRootAbsorbedCoordinates D S z := by
  have hprofile := hN.2.2.2.2.2.2.2.2.2.2.1 z hz r hr hroot
  have hprofile' := hprofile.comp_tendsto (continuous_fst.tendsto (r, θ))
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  filter_upwards [hprofile', hU.mem_nhds ⟨hr, mem_univ θ⟩] with p hp hpm
  have hr0 : p.1 ≠ 0 := (hN.1.1.choose_spec.1.1.trans hpm.1.1).ne'
  have hw : D.w p.1 ≠ 0 := (hN.1.1.choose_spec.1.2.2.2.2.1 _ hpm.1).ne'
  exact n04PositiveGeometry_rootDiscriminant_eq_absorbed hT hS hN z p hr0 hw hp

/-- Exact mixed traces of the original physical discriminant power,
using the same finite packet as the other root coefficient kernels. -/
theorem n04PositiveGeometry_physicalRootDiscPowerTrace_kernel_formula
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (γ : ℝ) (a d : ℕ) (θ : ℝ) :
    iteratedDeriv d (radialBoundaryJet
      (fun p => polarDiscriminant (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z)) p ^ γ) r a) θ =
      ∑ c : OrderedFinpartition (a + d), n04PositiveGeometry_rootDiscKernel γ c.length
        (n04PositiveGeometry_rootSpatialInput (D := D) (C := C)
          c (cylinderMixedWord a d) r (z, θ)) := by
  let u := n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z)
  have hgerm (η : ℝ) :
      (fun p => polarDiscriminant (stateProfile D S C (liftSectorParameter S C z).1)
        (stateHeight D S C (liftSectorParameter S C z)) p)
        =ᶠ[𝓝 (r, η)] fun p => n06RootNormalizedDiscriminant (u p) :=
    n04PositiveGeometry_rootDiscriminant_germ_eq_absorbed hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) hr hroot η
  have hpos (η : ℝ) : 0 < n06RootNormalizedDiscriminant (u (r, η)) := by
    have hb := n06_actualRootNormalized_denominators_lower hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) hr hroot η
    have he := n06_actualRootAbsorbed_denominators D S (liftSectorParameter S C z) (r, η)
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2).trans_eq he.2.symm
  have he := discKernel_trace_formula u
    (n06_actualRootAbsorbedCoordinates_contDiff hN.1.1 hT hS
      (liftSectorParameter S C z)) _ r γ hgerm hpos a d θ
  apply he.trans
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (n04PositiveGeometry_rootDiscKernel γ c.length)
    (n04PositiveGeometry_rootSpatialInput_eq_packet hN.1.1 hT hS
      c (cylinderMixedWord a d) r (z, θ)).symm

theorem n04PositiveGeometry_rootSpatialInput_mapsTo_discKernel
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2) :
    MapsTo (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r)
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootDiscKernelDomain c.length) := by
  intro z hz
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (n04PositiveGeometry_rootSpatialInput_denominators hT hS hN hr hroot c w hz).2

/-- Each term has an actual joint tower before any parameter or extra
angular order is selected. -/
def n04PositiveGeometry_rootDiscKernelTerm_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (γ : ℝ) {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => n04PositiveGeometry_rootDiscKernel γ c.length
        (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z)) := by
  let JT := n04PositiveGeometry_rootSpatialInput_joint
    (C := C) (base := base) hN.1.1 hT hS hε hr c w
  exact JT.comp_contDiff (n04PositiveGeometry_rootDiscKernelDomain_open c.length)
    (n04PositiveGeometry_rootDiscKernel_contDiff γ c.length)
    (n04PositiveGeometry_rootSpatialInput_mapsTo_discKernel hT hS hN hr hroot c w)

/-- The literal physical mixed trace is jointly smooth in the original
sector parameter and angle, by the exact finite kernel identity. -/
def n04PositiveGeometry_physicalRootDiscPowerTrace_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (γ : ℝ) (a d : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => iteratedDeriv d (radialBoundaryJet
        (fun p => polarDiscriminant
          (stateProfile D S C (liftSectorParameter S C z.1).1)
          (stateHeight D S C (liftSectorParameter S C z.1)) p ^ γ) r a) z.2) := by
  apply (smoothDirections_finiteSum
    ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
    (fun c : OrderedFinpartition (a + d) =>
      n04PositiveGeometry_rootDiscKernelTerm_joint hT hS hN hε hr hroot γ
        c (cylinderMixedWord a d))).congr
  intro z hz
  exact (n04PositiveGeometry_physicalRootDiscPowerTrace_kernel_formula
    hT hS hN hr hroot z.1 hz.1 γ a d z.2).symm

end ContinuousFlexibility.Analysis
