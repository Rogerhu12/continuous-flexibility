import ContinuousFlexibility.Analysis.N07aCanonicalScalarColumns
import ContinuousFlexibility.Analysis.N07aNuSupport
import ContinuousFlexibility.Analysis.N07aAngularPieceCover
import ContinuousFlexibility.Analysis.N07aScalarColumnSymmetry

/-!
# A fixed finite set of actual pieces for the scalar columns

The cutoff column is supported where its radial derivative is supported.
The ν column is supported on the fixed border support, and the auxiliary
source has its prescribed compact radial support. The genuine physical
piece geometry turns their union into one finite set of piece indices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_radialCutoff_divergence_zero_outside
    (A : SymmetricCoefficients) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {J : Set ℝ} (hJ : IsClosed J) (hzero : ∀ r, r ∉ J → deriv χ r = 0)
    {p : PolarPoint} (hp : p.1 ∉ J) :
    divergenceOperator A (fun q => χ q.1) p = 0 := by
  have he : ∀ᶠ q : PolarPoint in 𝓝 p, deriv χ q.1 = 0 := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (hJ.isOpen_compl.mem_nhds hp)] with q hq
    exact hzero q.1 hq
  have hr (q : PolarPoint) : radialPartial (fun p => χ p.1) q = deriv χ q.1 :=
    Radial.radialPartial_radialHeightField (hχ.differentiable (by simp) q.1)
  have ht (q : PolarPoint) : angularPartial (fun p => χ p.1) q = 0 :=
    Radial.angularPartial_radialHeightField (hχ.differentiable (by simp) q.1)
  have hrad : (fun q => A.a q * radialPartial (fun p => χ p.1) q +
      A.b q * angularPartial (fun p => χ p.1) q) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [he] with q hq
    simp only [hr, ht, hq, mul_zero, add_zero]
  have hang : (fun q => A.b q * radialPartial (fun p => χ p.1) q +
      A.c q * angularPartial (fun p => χ p.1) q) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
    filter_upwards [he] with q hq
    simp only [hr, ht, hq, mul_zero, add_zero]
  have hdr := congrArg (fun B : PolarPoint →L[ℝ] ℝ => B (1, 0))
    (hrad.fderiv_eq (𝕜 := ℝ))
  have hdt := congrArg (fun B : PolarPoint →L[ℝ] ℝ => B (0, 1))
    (hang.fderiv_eq (𝕜 := ℝ))
  simpa only [divergenceOperator, radialPartial, angularPartial, fderiv_const_apply,
    zero_apply, add_zero] using congrArg₂ (fun x y : ℝ => x + y) hdr hdt

def n07aPhysicalScalarColumn (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (i : Fin 3) : PolarPoint → ℝ :=
  ![divergenceOperator (L.coefficients z) (fun p => S.chiLeft p.1),
    nuColumnField D S C z, (S.height (3 / 4 : ℝ)).decode S.psi] i

theorem n07aScalarColumn_eq_canonicalSource
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 3) :
    n07aScalarColumn D S C L K z m i =
      canonicalSource S K z m (n07aPhysicalScalarColumn D S C L z i) := by
  fin_cases i <;> rfl

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_physicalScalarColumn_even
    (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) (r θ : ℝ) :
    n07aPhysicalScalarColumn D S C L z i (r, -θ) =
      n07aPhysicalScalarColumn D S C L z i (r, θ) := by
  fin_cases i
  · have hsym := h03.2.2.2.1 z hz hs
    exact n07a_divergenceOperator_even (L.coefficients z)
      (fun r θ => (hsym r θ).1) (fun r θ => (hsym r θ).2.1)
      (fun r θ => (hsym r θ).2.2) (fun _ _ => rfl) r θ
  · exact n07a_nuColumnField_even hS z r θ
  · exact ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.1 r θ

theorem n07a_canonicalScalarColumn_even
    (hS : IsPhysicalSpaces D T S)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (z : AnnularState S × ℝ) (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (i : Fin 3) :
    ∀ p ∈ canonicalOpen S K m,
      n07aScalarColumn D S C L K z m i (p.1, -p.2) = n07aScalarColumn D S C L K z m i p := by
  intro p hp
  have hx := (h04.2.2.2.2.2.2.2.1 z hz hs m).2.1 hp
  have hInv := h04.2.2.2.2.2.2.2.2.2.2.1 z hz hs m p hp
  have hreflect := h04.2.2.2.2.2.2.2.2.2.1 z hz hs m _ hx
  rw [n07aScalarColumn_eq_canonicalSource]
  simp only [canonicalSource, hInv, hreflect.2.1, hreflect.2.2,
    n07a_physicalScalarColumn_even hS h03 z hz hs i]

theorem n07a_physicalScalarColumns_uniform_support
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo D.a D.b ∧
      ∀ z i r, r ∉ J → ∀ θ, n07aPhysicalScalarColumn D S C L z i (r, θ) = 0 := by
  obtain ⟨J₀, hJ₀, hJ₀core, _, hcut⟩ := hS.2.2.1.2.2
  obtain ⟨J₂, hJ₂, hJ₂core, haux⟩ := hS.2.2.2.2.2.2.2.2.1
  have hborder : RadialTrueBorder D := h01.1.2.2.2.1
  refine ⟨J₀ ∪ tsupport D.chi ∪ J₂, (hJ₀.union hborder.2.1).union hJ₂,
    union_subset (union_subset hJ₀core (fun r hr => (hborder.2.2.1 hr).1)) hJ₂core, ?_⟩
  intro z i r hr θ
  have hr₀ : r ∉ J₀ := fun h => hr (Or.inl (Or.inl h))
  have hr₁ : r ∉ tsupport D.chi := fun h => hr (Or.inl (Or.inr h))
  have hr₂ : r ∉ J₂ := fun h => hr (Or.inr h)
  fin_cases i
  · exact n07a_radialCutoff_divergence_zero_outside (L.coefficients z) hS.2.2.1.1
      hJ₀.isClosed hcut hr₀
  · exact n07a_nuColumnField_eq_zero_outside hS hT h01 z hr₁
  · exact haux r hr₂ θ

theorem n07a_canonicalScalarColumns_finite_support
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K) :
    ∃ I : Finset ℕ, ∀ z, z ∈ stateNeighborhood S C base ε → stateSector S z.1 →
      ∀ m, m ∉ I → ∀ i p, p ∈ canonicalOpen S K m →
        n07aScalarColumn D S C L K z m i p = 0 := by
  classical
  obtain ⟨J, hJ, hJcore, hzero⟩ := n07a_physicalScalarColumns_uniform_support
    (L := L) hS hT h01
  let A : Set ℕ := {m | (J ∩ Ioo (K.physicalLeft m) (K.physicalRight m)).Nonempty}
  have hA : A.Finite := n07a_physicalPieces_finite_inter_compact hD hT h04 href hJ hJcore
  refine ⟨hA.toFinset, fun z hz hs m hm i p hp => ?_⟩
  have hx := (h04.2.2.2.2.2.2.2.1 z hz hs m).2.1 hp
  have hnot : (K.inverseChart z m p).1 ∉ J := by
    intro hj
    apply hm
    exact hA.mem_toFinset.mpr ⟨(K.inverseChart z m p).1, hj, hx.1⟩
  rw [n07aScalarColumn_eq_canonicalSource]
  change K.height z m (K.inverseChart z m p) *
    n07aPhysicalScalarColumn D S C L z i (K.inverseChart z m p) /
      |planeJacobian (K.chart z m) (K.inverseChart z m p)| = 0
  rw [hzero z i _ hnot, mul_zero, zero_div]

end ContinuousFlexibility.Analysis
