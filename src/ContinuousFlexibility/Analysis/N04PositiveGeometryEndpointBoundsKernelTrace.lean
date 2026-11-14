module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsKernelPower
public import ContinuousFlexibility.Analysis.N04RealizationPhysicalRootJetDirections

/-!
# Identifying the finite kernel sum with the actual physical root trace

The original N01 profile germ identifies every radial trace, and the
identity holds as a function of the angle. Additional angular
derivatives therefore give the exact mixed spatial kernel formula.
The chosen root-coordinate extension never appears in this step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

private theorem normalizedKernel_trace_formula
    (u : PolarPoint → N06RootNormalizedCoordinates) (hu : ContDiff ℝ ∞ u)
    (f : PolarPoint → PolarPoint) (r : ℝ)
    (hgerm : ∀ θ, f =ᶠ[𝓝 (r, θ)] fun p => n06RootNormalizedFields (u p))
    (hpos : ∀ θ, 0 < n06RootNormalizedQ (u (r, θ)) ∧
      0 < n06RootNormalizedDiscriminant (u (r, θ)))
    (π : PolarPoint →L[ℝ] ℝ) (a d : ℕ) (θ : ℝ) :
    iteratedDeriv d (radialBoundaryJet (π ∘ f) r a) θ =
      ∑ c : OrderedFinpartition (a + d), π
        (n04PositiveGeometry_rootRadialKernel c.length
          (n04PositiveGeometry_rootSpatialPacket c u (r, θ)
            (fun j => cylinderBasisVector (cylinderMixedWord a d j)))) := by
  let V : Set N06RootNormalizedCoordinates :=
    {v | 0 < n06RootNormalizedQ v ∧ 0 < n06RootNormalizedDiscriminant v}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const n06RootNormalizedQ_contDiff.continuous).inter
      (isOpen_lt continuous_const n06RootNormalizedDiscriminant_contDiff.continuous)
  let Ω := u ⁻¹' V
  have hΩ : IsOpen Ω := hV.preimage hu.continuous
  have hc : ContDiffOn ℝ ∞ (fun p => n06RootNormalizedFields (u p)) Ω := by
    intro p hp
    exact ((n06RootNormalizedFields_contDiffAt hp.1.ne' hp.2).comp p
      hu.contDiffAt).contDiffWithinAt
  have hcπ : ContDiffOn ℝ ∞ (fun p => π (n06RootNormalizedFields (u p))) Ω := by
    intro p hp
    exact (π.contDiff.contDiffAt.comp p (hc.contDiffAt (hΩ.mem_nhds hp))).contDiffWithinAt
  have hr (η : ℝ) : (r, η) ∈ Ω := hpos η
  have htrace : radialBoundaryJet (π ∘ f) r a =
      radialBoundaryJet (fun p => π (n06RootNormalizedFields (u p))) r a := by
    funext η
    have hslice : (fun x => π (f (x, η))) =ᶠ[𝓝 r]
        (fun x => π (n06RootNormalizedFields (u (x, η)))) := by
      filter_upwards [(hgerm η).comp_tendsto
        ((continuous_id.prodMk continuous_const).tendsto r)] with x hx
      exact congrArg π hx
    exact hslice.iteratedDeriv_eq a
  rw [htrace, iteratedDeriv_radialBoundaryJet_eq_mixedDerivative hΩ hcπ r hr,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hcπ a d (hr θ)]
  let dirs := fun j => cylinderBasisVector (cylinderMixedWord a d j)
  have hprojection := congrArg
    (fun A : PolarPoint [×a + d]→L[ℝ] ℝ => A dirs)
    (π.iteratedFDeriv_comp_left (hc.contDiffAt (hΩ.mem_nhds (hr θ)))
      (i := a + d) (by simp))
  change iteratedFDeriv ℝ (a + d) (fun p => π (n06RootNormalizedFields (u p)))
      (r, θ) dirs = π (iteratedFDeriv ℝ (a + d)
        (fun p => n06RootNormalizedFields (u p)) (r, θ) dirs) at hprojection
  apply hprojection.trans
  rw [n04PositiveGeometry_rootSpatialKernel_formula u hu (a + d) (r, θ) dirs
    (hpos θ).1 (hpos θ).2, map_sum]

local instance n04PositiveKernelTraceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}

theorem n04PositiveGeometry_physicalRootTrace_kernel_formula
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (π : PolarPoint →L[ℝ] ℝ) (a d : ℕ) (θ : ℝ) :
    iteratedDeriv d (radialBoundaryJet
      (fun p => π (n06PhysicalRootFields D S C (liftSectorParameter S C z) p)) r a) θ =
      ∑ c : OrderedFinpartition (a + d), π
        (n04PositiveGeometry_rootRadialKernel c.length
          (n04PositiveGeometry_rootSpatialInput (D := D) (C := C)
            c (cylinderMixedWord a d) r (z, θ))) := by
  let u := n06ActualRootAbsorbedCoordinates D S (liftSectorParameter S C z)
  have hgerm (η : ℝ) : n06PhysicalRootFields D S C (liftSectorParameter S C z)
      =ᶠ[𝓝 (r, η)] fun p => n06RootNormalizedFields (u p) := by
    filter_upwards [n06_physicalRootFields_germ_eq_normalized hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl) hr hroot η] with p hp
    exact hp.trans (n06_absorbRoot_fields
      (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z) p)).symm
  have hpos (η : ℝ) : 0 < n06RootNormalizedQ (u (r, η)) ∧
      0 < n06RootNormalizedDiscriminant (u (r, η)) := by
    have hb := n06_actualRootNormalized_denominators_lower hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z) hr hroot η
    have he := n06_absorbRoot_denominators
      (n06ActualRootNormalizedCoordinates D S (liftSectorParameter S C z) (r, η))
    exact ⟨(lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.1).trans_eq he.1.symm,
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2).trans_eq he.2.symm⟩
  have he := normalizedKernel_trace_formula u
    (n06_actualRootAbsorbedCoordinates_contDiff hN.1.1 hT hS
      (liftSectorParameter S C z)) _ r hgerm hpos π a d θ
  apply he.trans
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun q => π (n04PositiveGeometry_rootRadialKernel c.length q))
    (n04PositiveGeometry_rootSpatialInput_eq_packet hN.1.1 hT hS
      c (cylinderMixedWord a d) r (z, θ)).symm

/-- Genuine joint tower for each literal kernel term used in the
physical trace formula. -/
def n04PositiveGeometry_rootKernelTerm_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    {n : ℕ} (c : OrderedFinpartition n) (w : Fin n → Fin 2)
    (π : PolarPoint →L[ℝ] ℝ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z => π (n04PositiveGeometry_rootRadialKernel c.length
        (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r z))) := by
  let JT := n04PositiveGeometry_rootSpatialInput_joint
    (C := C) (base := base) hN.1.1 hT hS hε hr c w
  let Q := JT.comp_contDiff (n04PositiveGeometry_rootRadialKernelDomain_open c.length)
    (n04PositiveGeometry_rootRadialKernel_contDiff c.length)
    (n04PositiveGeometry_rootSpatialInput_mapsTo hT hS hN hr hroot c w)
  exact (smoothDirections_postcompCLM Q π).congr (fun _ _ => rfl)

end ContinuousFlexibility.Analysis
