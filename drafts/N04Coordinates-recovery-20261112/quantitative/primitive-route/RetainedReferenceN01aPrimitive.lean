import ContinuousFlexibility.Analysis.RetainedReferenceComponentHosts
import ContinuousFlexibility.Analysis.RetainedReferenceNormalizedOpticalLower
import ContinuousFlexibility.Analysis.MaterialSampleRadialPolynomial
import ContinuousFlexibility.Analysis.N01aControlGeometryAssembly
import ContinuousFlexibility.Analysis.N01aOpticalProfile

/-!
# N01a controls retaining the actual primitive geometry

This construction keeps the same retained reference and actual physical
spaces. The existing optical-control factory supplies genuine whole-
component hosts. The natural retained enumeration proves their bounded
index displacement; the actual sampled material estimate controls every
control derivative at that same host. Only the already proved E0
normalization is used. No existing Through03 witness is transferred to
a newly chosen reference or control geometry.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

private theorem n01a_controlGeometry_retaining_hosts
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsRadialReference D) (hS : IsPhysicalSpaces D T S)
    (hphi : HeightMember D T referenceBeta
      (fun p : PolarPoint => D.phi p.1 * cosineMode 2 p.2))
    (e : ℕ ≃ N01aNegativeComponent D) (host : ℕ → ℕ) (χ : ℕ → ℝ → ℝ)
    (hχ : ∀ m, ContDiff ℝ ∞ (χ m) ∧ HasCompactSupport (χ m) ∧
      tsupport (χ m) ⊆ (e m).interval)
    (hderiv : ∀ m, HasDerivAt
      (fun t : ℝ => ∫ r in (e m).left..(e m).right,
        Real.sqrt (-deriv (fun s => D.w s * Real.exp (t * χ m s)) r /
          (r * (D.w r * Real.exp (t * χ m r))))) 1 0)
    (hindex : ∃ B : ℝ, 0 < B ∧ ∀ m,
      |(D.cellIndex (host m) : ℝ) - D.cellIndex m| ≤ B)
    (hjets : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
      |iteratedDeriv s (χ m) r| ≤ B * T.E0 (T.sample (host m)) ^ B) :
    ∃ C : NonlinearGeometryData S,
      Blueprint.N01PartA D T S C ∧ C.cell = host ∧
        C.left = (fun m => (e m).left) ∧ C.right = (fun m => (e m).right) := by
  obtain ⟨x, hx⟩ := exists_referenceState_of_heightMember hS hD.2.2.2.1 hphi
  let C : NonlinearGeometryData S :=
    { n01aGeometryOfControls S e χ x with cell := host }
  refine ⟨C, ?_, rfl, rfl, rfl⟩
  refine ⟨hD, ?_, ?_, hindex, ?_⟩
  · simpa only [referenceStateConditions, C, n01aGeometryOfControls] using hx
  · change controlGeometryConditions D S (n01aGeometryOfControls S e χ x)
    exact n01aGeometryOfControls_controlGeometry hD.1.choose_spec.1 hD.2.2.1
      e χ x hχ hderiv
  · intro s
    obtain ⟨B, hB, hb⟩ := hjets s
    exact ⟨B, hB, fun m r _ => hb m r⟩

/-- The same retained reference has actual N01a controls, genuine hosts,
the true-border support, and the uniform primitive optical lower bound.
All four facts are constructed together; host inclusion is not an input. -/
theorem retainedReference_exists_n01a_primitive_geometry
    {S₀ : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K q length) (hS₀ : IsSelectedTail S₀)
    (hstart : 100 ≤ S₀.chain.index)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    (hD : IsRadialReference Γ.reference)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces Γ.reference T S)
    (hphi : HeightMember Γ.reference T referenceBeta
      (fun p : PolarPoint => Γ.reference.phi p.1 * cosineMode 2 p.2)) :
    ∃ C : NonlinearGeometryData S,
      IsMaterialData Γ.reference (enlargedMaterialData T) ∧
      IsPhysicalSpaces Γ.reference (enlargedMaterialData T) S ∧
      Blueprint.N01PartA Γ.reference (enlargedMaterialData T) S C ∧
      (∀ m, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m)) ∧
      tsupport Γ.reference.chi ⊆ Ioo Γ.reference.a Γ.reference.b ∧
      ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
        B⁻¹ * (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample (C.cell m)) ^ (-B) *
            min (r - C.left m) (C.right m - r) ≤
          -deriv Γ.reference.w r / (r * Γ.reference.w r) := by
  let T' := enlargedMaterialData T
  obtain ⟨hT', hnorm, Bopt, hBopt, hoptical⟩ :=
    retainedReference_normalized_optical_lower P hS₀ hstart hband hq hΓ hw hcoordinates hT
  have hS' : IsPhysicalSpaces Γ.reference T' S := isPhysicalSpaces_enlargedMaterialData hS
  have hphi' : HeightMember Γ.reference T' referenceBeta
      (fun p : PolarPoint => Γ.reference.phi p.1 * cosineMode 2 p.2) := hphi
  obtain ⟨e, he⟩ :=
    retainedReference_enumeration_host_index P hS₀ hband hq hΓ hw hcoordinates hT'
  obtain ⟨host, χ, hhost, hχ, hderiv, hraw⟩ :=
    exists_n01a_opticalControls_of_radialReference hD
      (l := fun m : ℕ => (e m).left) (h := fun m : ℕ => (e m).right)
      (fun m => (e m).property)
  have hindex := he host hhost
  have hjets : ∀ n : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
      |iteratedDeriv n (χ m) r| ≤ B * T'.E0 (T'.sample (host m)) ^ B := by
    intro n
    obtain ⟨A, hA, hjet⟩ := hraw n
    obtain ⟨C₀, Q, hC₀, hQ, hpoly⟩ :=
      materialSample_radialE_power_bound (T := T') hT' hD.1 (R := A) hA.le
    obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (A * C₀) Q
    refine ⟨B, hB, ?_⟩
    intro m r
    calc
      |iteratedDeriv n (χ m) r| ≤ A * radialE (Γ.reference.cellIndex (host m)) ^ A :=
        hjet m r
      _ ≤ A * (C₀ * T'.E0 (T'.sample (host m)) ^ Q) :=
        mul_le_mul_of_nonneg_left (hpoly (host m)) hA.le
      _ = (A * C₀) * T'.E0 (T'.sample (host m)) ^ Q := by ring
      _ ≤ B * T'.E0 (T'.sample (host m)) ^ B :=
        hpack _ (hnorm _ (materialSample_mem_interval hD.1 hT' (host m)))
  obtain ⟨C, hpart, hcell, hleft, hright⟩ :=
    n01a_controlGeometry_retaining_hosts hD hS' hphi' e host χ hχ hderiv hindex hjets
  have hhostC (m : ℕ) : Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells (C.cell m) := by
    simpa only [hcell, hleft, hright, N01aNegativeComponent.interval] using hhost m
  have hcomponent (m : ℕ) : NegativeRadialComponent Γ.reference (C.left m) (C.right m) := by
    rw [hleft, hright]
    exact (e m).property
  refine ⟨C, hT', hS', hpart, hhostC, ?_, Bopt, hBopt, ?_⟩
  · intro r hr
    exact (hD.2.2.2.1.2.2.1 hr).1
  · intro m r hr
    exact hoptical (C.left m) (C.right m) (C.cell m) (hcomponent m) (hhostC m) r hr

end ContinuousFlexibility.Radial
