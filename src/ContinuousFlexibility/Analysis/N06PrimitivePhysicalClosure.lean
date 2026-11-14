module

public import ContinuousFlexibility.Analysis.N06NamedPhysicalRelation
public import ContinuousFlexibility.Analysis.N06PhysicalHeightAffinePairing
public import ContinuousFlexibility.Analysis.N06PhysicalTestCoordinates
public import ContinuousFlexibility.Analysis.N06CurrentPhysicalTests
public import ContinuousFlexibility.Analysis.N06PrimitiveFiniteSupport
public import ContinuousFlexibility.Analysis.N06PrimitiveGraphFourierCore

/-!
# Actual physical closedness and the original graph core

The primitive reference jet estimates give local finiteness of the actual
current support pieces. All transformed test L2 bounds come from the
original N04 geometry. The same physical residual is therefore closed on
its original graph and source spaces, without a controlled-coordinate
window. Together with the actual primitive-gauge Fourier core this passes
finite graph identities to every original graph element.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open CanonicalGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n06_primitive_full_pairing_affine_equation
    (A B a mu omega s k c : ℝ) :
    (Real.pi⁻¹ * A + a * s + mu * k + omega * c = Real.pi⁻¹ * B) ↔
      A - B + (a * (Real.pi * s) + mu * (Real.pi * k) +
        omega * (Real.pi * c)) = 0 := by
  have he : Real.pi *
      ((Real.pi⁻¹ * A + a * s + mu * k + omega * c) - Real.pi⁻¹ * B) =
      A - B + (a * (Real.pi * s) + mu * (Real.pi * k) +
        omega * (Real.pi * c)) := by
    calc
      _ = (Real.pi * Real.pi⁻¹) * A - (Real.pi * Real.pi⁻¹) * B +
          (a * (Real.pi * s) + mu * (Real.pi * k) +
            omega * (Real.pi * c)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ Real.pi_ne_zero, one_mul, one_mul]
  rw [← he]
  simp only [mul_eq_zero, Real.pi_ne_zero, false_or, sub_eq_zero]

private theorem n06_primitive_full_pairing_finite_affine_equation
    (I : Finset ℕ) (A B : ℕ → ℝ) (a mu omega s k c : ℝ) :
    (Real.pi⁻¹ * (∑ m ∈ I, A m) + a * s + mu * k + omega * c =
      Real.pi⁻¹ * ∑ m ∈ I, B m) ↔
      (∑ m ∈ I, (A m - B m)) +
        (a * (Real.pi * s) + mu * (Real.pi * k) + omega * (Real.pi * c)) = 0 := by
  rw [Finset.sum_sub_distrib]
  exact n06_primitive_full_pairing_affine_equation _ _ _ _ _ _ _ _

/-- The named physical weak relation is closed on the same original
graph and source spaces. Its test support and all required current L2
transforms follow from the original geometric hypotheses. The domain
`B` is arbitrary; no reference inverse or graph equation is used. -/
theorem n06_namedPhysicalWeakRelation_isClosed_of_primitive
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K V b} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hThrough : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hV : IsVolumeModel T S K V)
    (hjets : ReferenceJets D T S C L K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
      N06NamedPhysicalWeakRelation D C L B z p.1 p.2} := by
  classical
  have h01 : N01Properties D T S C base loss ε := hThrough.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := hThrough.2.2.2.2.1
  have hab : D.a ≤ D.b := by
    obtain ⟨x, hxL, hxR⟩ := exists_between (h04.1.referenceBounds 0).1
    have hx := (h04.1.referenceBounds 0).2.2 ⟨hxL, hxR⟩
    exact (hx.1.trans hx.2).le
  let P : (PolarPoint → ℝ) → (B.Space × V.level (3 / 4 : ℝ) 0 b) → Prop :=
    fun φ p =>
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalHeight K z (fun m => (p.1.val.1.1 m : PolarPoint → ℝ))
          p.1.val.1.2.1 (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
        p.1.val.1.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          nuColumnField D S C z (r, θ) * φ (r, θ))) +
        p.1.val.1.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
          (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z
          (fun m => (V.forget (3 / 4 : ℝ) 0 b p.2 m : PolarPoint → ℝ)) (r, θ) *
            φ (r, θ))
  change IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
    ∀ φ, RadialTest D φ → P φ p}
  have hclosed (φ : PolarPoint → ℝ) (hφ : RadialTest D φ) :
      IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b | P φ p} := by
    obtain ⟨J, hJ, hJD, hφsupport, hLsupport, htests⟩ :=
      n06_current_physical_tests hT hS hThrough hz hs hφ
    have hfinite : (n06PhysicalSupportPieces K z J).Finite :=
      n06_physicalSupportPieces_finite_of_primitive h01.1.1 hT h01.2.2.2.1
        h04 hjets hz hs hJ hJD
    let g : PolarPoint → ℝ := divergenceOperator (L.coefficients z) φ
    let heightTest : ℕ → PolarPoint → ℝ := fun m =>
      canonicalSource S K z m (n06_radialTestAverage g)
    let sourceTest : ℕ → PolarPoint → ℝ := fun m =>
      canonicalHeight S K z m (n06_radialTestAverage φ)
    have hh (m : ℕ) : MemLp (heightTest m) 2 (canonicalMeasure S K m) :=
      n06_canonicalSource_average_memLp m (htests m).1 (htests m).2.1
    have hf (m : ℕ) : MemLp (sourceTest m) 2 (canonicalMeasure S K m) :=
      n06_canonicalHeight_average_memLp m (htests m).2.2.1 (htests m).2.2.2
    let s : ℝ := Real.pi * ∫ r in D.a..D.b,
      radialAngularMean (fun θ => S.chiLeft r * g (r, θ))
    let k : ℝ := Real.pi * ∫ r in D.a..D.b,
      radialAngularMean (fun θ => nuColumnField D S C z (r, θ) * φ (r, θ))
    let c : ℝ := Real.pi * ∫ r in D.a..D.b,
      radialAngularMean (fun θ => (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))
    have heq : {p : B.Space × V.level (3 / 4 : ℝ) 0 b | P φ p} =
        {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
          (∑ m ∈ hfinite.toFinset,
            ((∫ q, p.1.val.1.1 m q * heightTest m q ∂canonicalMeasure S K m) -
              ∫ q, V.forget (3 / 4 : ℝ) 0 b p.2 m q * sourceTest m q
                ∂canonicalMeasure S K m)) +
          (p.1.val.1.2.1 * s + p.1.val.1.2.2.1 * k + p.1.val.1.2.2.2 * c) = 0} := by
      ext p
      change P φ p ↔ _
      have hheight := n06_physicalHeight_affine_pairing hS h04 hz hs
        p.1.val.1.1 p.1.val.1.2.1 hfinite (g := g)
        (fun m => (htests m).1) (fun m => (htests m).2.1) hLsupport
      have hrep : ∀ m,
          (V.forget (3 / 4 : ℝ) 0 b p.2 m : PolarPoint → ℝ)
            =ᵐ[canonicalMeasure S K m] canonicalSource S K z m
              (n06PhysicalSource K z
                (fun m => (V.forget (3 / 4 : ℝ) 0 b p.2 m : PolarPoint → ℝ))) :=
        (n06_physical_representation h04 hz hs p.1.val.1
          (V.forget (3 / 4 : ℝ) 0 b p.2)).1.2
      have hsource := n06_fullCanonical_source_pairing hab h04 hz hs hfinite
        (V.forget (3 / 4 : ℝ) 0 b p.2) hrep
        (n06PhysicalSource_periodic h04 hz hs _)
        (fun m => (htests m).2.2.1) (fun m => (htests m).2.2.2) hφsupport
      dsimp only [P]
      refine (Iff.of_eq (congrArg₂
        (fun x y : ℝ =>
          x + p.1.val.1.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
            nuColumnField D S C z (r, θ) * φ (r, θ))) +
            p.1.val.1.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
              (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) = y)
        hheight hsource)).trans ?_
      exact n06_primitive_full_pairing_finite_affine_equation hfinite.toFinset
        (fun m => ∫ q, p.1.val.1.1 m q * heightTest m q ∂canonicalMeasure S K m)
        (fun m => ∫ q, V.forget (3 / 4 : ℝ) 0 b p.2 m q * sourceTest m q
          ∂canonicalMeasure S K m) _ _ _ _ _ _
    rw [heq]
    exact n06GraphSourceTest_isClosed hV B hfinite.toFinset
      heightTest sourceTest hh hf s k c
  have heq : {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
      ∀ φ, RadialTest D φ → P φ p} =
      ⋂ φ, ⋂ (_ : RadialTest D φ), {p : B.Space × V.level (3 / 4 : ℝ) 0 b | P φ p} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun φ => isClosed_iInter fun hφ => hclosed φ hφ

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

/-- The named weak equation is closed along the continuous operator on
the original graph, and the genuine finite-height core is dense there. -/
theorem n06_namedPhysicalWeakRelation_of_primitiveFiniteGraphCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)
    (hjets : ReferenceJets D T S C L K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (P : B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hcore : ∀ u ∈ n06CanonicalGraphFiniteAngularCore B,
      N06NamedPhysicalWeakRelation D C L B z u (P u)) :
    ∀ u : B.Space, N06NamedPhysicalWeakRelation D C L B z u (P u) := by
  have hclosed := (n06_namedPhysicalWeakRelation_isClosed_of_primitive
    (B := B) hT hS h.1 h.2.2.1 hjets hz hs).preimage
      (continuous_id.prodMk P.continuous)
  have hsubset : n06CanonicalGraphFiniteAngularCore B ⊆
      {u : B.Space | N06NamedPhysicalWeakRelation D C L B z u (P u)} := hcore
  have hclosure := closure_minimal hsubset hclosed
  exact fun u => hclosure (n06CanonicalGraphFiniteAngularCore_dense_of_primitive h hradial hgauge u)

/-- The original physical relation, including its normalization row,
follows for every graph element from the finite-height weak equations. -/
theorem n06_perturbedCanonicalRelation_of_primitiveFiniteGraphCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)
    (hjets : ReferenceJets D T S C L K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (P : B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hcore : ∀ u ∈ n06CanonicalGraphFiniteAngularCore B,
      N06NamedPhysicalWeakRelation D C L B z u (P u)) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (P u)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hab : D.a ≤ D.b := h01.1.1.choose_spec.1.2.1.le
  intro u
  exact n06_namedPhysicalWeakRelation_implies hab h04 h.2 href hsector hz hs u (P u)
    (n06_namedPhysicalWeakRelation_of_primitiveFiniteGraphCore hT hS h hradial hgauge hjets hz hs P hcore u)


end ContinuousFlexibility.Statements
