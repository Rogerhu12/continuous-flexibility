import ContinuousFlexibility.Analysis.N01cComponentOpticalGeometry
import ContinuousFlexibility.Analysis.N01cFiniteAffineSpeedFactors
import ContinuousFlexibility.Analysis.N01cCosineRootPath

/-!
# The actual compact component speed

The globally smooth signed-sine formula agrees with the actual ordinary
speed after the cosine change of variable on the physical half-period.
The supplied trajectories therefore satisfy the transformed classical
equation on that interval. No extension of their time equation is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

def componentCosineSpeed (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (m : ℕ)
    (p : (AnnularState S × ℝ) × PolarPoint) : ℝ :=
  cosineRegularizedSpeed (C.left m) (C.right m)
    (fun q => normalizedSpeedFactor D S C 0 q.1 q.2)
    (fun q => normalizedSpeedFactor D S C 1 q.1 q.2)
    (fun q => twoRootDivided (componentOpticalSquare D S C m q.1)
      (C.left m) (C.right m) q.2) p

theorem componentCosineSpeed_eq_transformed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) (θ : ℝ) :
    componentCosineSpeed D S C m (z, (t, θ)) =
      ((C.right m - C.left m) / 2 * Real.sin t) *
        minusCharacteristicSpeed (originalCoefficients D S C z)
          (rootCosinePath (C.left m) (C.right m) t, θ) := by
  have hC := hA.2.2.1
  have hr := rootCosinePath_mem_Ioo (hC.1 m).2.1 ht
  have hcore : (rootCosinePath (C.left m) (C.right m) t, θ) ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  rw [minusCharacteristicSpeed_normalized_factors hS hT hA hB hz hcore]
  have he := cosineRegularizedSpeed_eq_transformed (θ := θ) (hC.1 m).2.1
    (fun q : (AnnularState S × ℝ) × PolarPoint => normalizedSpeedFactor D S C 0 q.1 q.2)
    (fun q : (AnnularState S × ℝ) × PolarPoint => normalizedSpeedFactor D S C 1 q.1 q.2)
    (fun q : (AnnularState S × ℝ) × ℝ => componentOpticalSquare D S C m q.1 q.2)
    (componentOpticalSquare_boundary_zero hA m z (Or.inl rfl))
    (componentOpticalSquare_boundary_zero hA m z (Or.inr rfl)) ht
  simpa only [componentCosineSpeed, componentOpticalSquare_eq_actual hA m z hr] using he

theorem hasDerivAt_componentCosineFlow
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (θ : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (fun u => C.minusFlow z m (rootCosinePath (C.left m) (C.right m) u) θ)
      (componentCosineSpeed D S C m
        (z, (t, C.minusFlow z m (rootCosinePath (C.left m) (C.right m) t) θ))) t := by
  have hr := rootCosinePath_mem_Ioo (hA.2.2.1.1 m).2.1 ht
  have hd := ((hB.1 z hz m θ).2.2.1 _ hr).comp t
    (hasDerivAt_rootCosinePath (C.left m) (C.right m) t)
  rw [componentCosineSpeed_eq_transformed hS hT hA hB hz m ht]
  simpa only [Function.comp_def, mul_comm] using hd

theorem contDiffOn_componentCosineSpeed_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z) (C.left m) (C.right m) r)
    (m : ℕ) {n : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (AnnularState S × ℝ)) :
    ContDiffOn ℝ ∞ (fun p : (Fin n → ℝ) × PolarPoint =>
      componentCosineSpeed D S C m (x + L p.1, p.2))
      (((fun q => x + L q) ⁻¹' stateNeighborhood S C base ε) ×ˢ
        (univ : Set PolarPoint)) := by
  let U := (fun q => x + L q) ⁻¹' stateNeighborhood S C base ε
  have hU : IsOpen U := (isOpen_stateNeighborhood S C base ε).preimage
    (continuous_const.add L.continuous)
  have hC := hA.2.2.1
  have hclosed : Icc (C.left m) (C.right m) ⊆ Ioo D.a D.b :=
    fun r hr => ⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩
  have hQ := (contDiffOn_componentOpticalSquare_finiteAffine hS hT hA m x L).mono
    (show U ×ˢ Ioo D.a D.b ⊆ (univ : Set (Fin n → ℝ)) ×ˢ Ioo D.a D.b from
      fun p hp => ⟨mem_univ _, hp.2⟩)
  have hV := contDiffOn_twoRootDivided_parameter hU isOpen_Ioo
    (convex_Ioo D.a D.b) hQ
    (hclosed ⟨le_rfl, (hC.1 m).2.1.le⟩)
    (hclosed ⟨(hC.1 m).2.1.le, le_rfl⟩)
  exact contDiffOn_cosineRegularizedSpeed (hC.1 m).2.1.le hclosed
    (contDiffOn_normalizedSpeedFactor_finiteAffine hS hT hA hB x L 0)
    (contDiffOn_normalizedSpeedFactor_finiteAffine hS hT hA hB x L 1) hV
    (fun q hq r hr => hpos (x + L q) hq m r hr)

/-- The zero-dimensional affine restriction gives the full spatial slice.
All coordinate transport is performed before specializing the state type. -/
private theorem n01c_componentCosine_contDiff_zero_slice
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {U : Set X} {F : X × PolarPoint → ℝ} {x : X} (hx : x ∈ U)
    (hf : ∀ L : (Fin 0 → ℝ) →L[ℝ] X,
      ContDiffOn ℝ ∞ (fun p : (Fin 0 → ℝ) × PolarPoint => F (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint))) :
    ContDiff ℝ ∞ (fun p : PolarPoint => F (x, p)) := by
  let L : (Fin 0 → ℝ) →L[ℝ] X := 0
  have hp : ContDiffOn ℝ ∞ (fun p : PolarPoint => F (x + L 0, p)) univ :=
    (hf L).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun p _ => ⟨by simpa only [L, ContinuousLinearMap.zero_apply, add_zero] using hx,
        mem_univ p⟩)
  simpa only [L, ContinuousLinearMap.zero_apply, add_zero] using contDiffOn_univ.mp hp

set_option backward.isDefEq.respectTransparency true in
theorem contDiff_componentCosineSpeed
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z) (C.left m) (C.right m) r)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)) := by
  exact n01c_componentCosine_contDiff_zero_slice
    (F := componentCosineSpeed D S C m) hz
    (contDiffOn_componentCosineSpeed_finiteAffine (n := 0) hS hT hA hB hpos m z)

end ContinuousFlexibility.Statements
