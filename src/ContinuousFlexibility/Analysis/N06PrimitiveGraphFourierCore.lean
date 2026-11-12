import ContinuousFlexibility.Analysis.N06PrimitiveFourierTransport
import ContinuousFlexibility.Analysis.N06CanonicalGraphFourierCore

/-!
# The original graph has a finite angular core in the primitive gauge

The primitive auxiliary column is radial. Projection retaining the mean
therefore leaves this same physical column fixed. Both height and source
can be cut directly in their original spaces, without constructing a
second volume representative of that column.

The original reference graph supplies the projected physical equation.
Its given inverse identifies the approximants and proves convergence in
the original graph norm. No material-label window, new graph, or N06
inverse is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open CanonicalGeometry ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Restoring a radial auxiliary field after projection gives the same
physical projection of the full source. Only its compatible part needs L2. -/
private theorem n06_primitive_compatibilityProjection_ae
    {D : ReferenceData} {f ψ : PolarPoint → ℝ} {omega : ℝ}
    (hg : MemLp (fun p => f p - omega * ψ p) 2 (radialPhysicalMeasure D))
    (hψ : ∀ p : PolarPoint, ψ p = ψ (p.1, 0))
    {I : Finset ℕ} (h0 : 0 ∈ I) :
    referenceBasisProjection I f =ᵐ[radialPhysicalMeasure D]
      (fun p => referenceBasisProjection I (fun q => f q - omega * ψ q) p +
        omega * ψ p) := by
  have he : (fun p : PolarPoint => (f p - omega * ψ p) - (-omega * ψ (p.1, 0))) = f := by
    funext p
    rw [hψ p]
    ring
  have hp := n06_referenceBasisProjection_sub_radial_ae hg
    (fun r => -omega * ψ (r, 0)) h0
  rw [he] at hp
  filter_upwards [hp] with p hp
  rw [hp, hψ p]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

/-- The genuine reference relation is invariant under simultaneous
finite angular projection of its height and its original source. -/
theorem n06_primitive_referenceCanonicalRelation_fourierProjection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)
    (hV : IsVolumeModel T S K V)
    {γ M₀ M₁ ell : ℝ} (hγ : 0 < γ)
    (U : CanonicalUnknown S K) (F : V.level (3 / 4 : ℝ) 0 b)
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ ell U
      (V.forget (3 / 4 : ℝ) 0 b F))
    (hreflect : ∀ m, (fun p : PolarPoint => U.1 m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U.1 m : PolarPoint → ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    ReferenceCanonicalRelation D T S C K V γ M₀ M₁ ell
      (n06CanonicalUnknownFourierCut N U)
      (V.forget (3 / 4 : ℝ) 0 b (n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N F)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  obtain ⟨hvolume, η, f, hrep, hgraph⟩ := hrel
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hb hγ hgraph.1
  obtain ⟨a, ha⟩ := hgraph.1
  have hηp : Function.Periodic η (0, Real.pi) := ha.2.2.1
  have hgp : Function.Periodic
      (fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p)
      (0, Real.pi) := hgraph.2.1.2.2.1
  have hfp : Function.Periodic f (0, Real.pi) := by
    intro p
    have he := hgp p
    change f (p + (0, Real.pi)) - U.2.2.2 *
        (S.height (3 / 4 : ℝ)).decode S.psi (p + (0, Real.pi)) =
      f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p at he
    rw [hgauge.1 (p + (0, Real.pi)), hgauge.1 p] at he
    simp only [Prod.fst_add, add_zero] at he
    linarith only [he]
  have h0 : 0 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hrestore := n06_primitive_compatibilityProjection_ae
    (r11b_source_memLp hD hγ hgraph.2.1) hgauge.1 h0
  refine ⟨?_, referenceBasisProjection (Finset.range (N + 1)) η,
    (fun p => referenceBasisProjection (Finset.range (N + 1))
      (fun q => f q - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi q) p +
        U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), ⟨?_, ?_⟩, ?_⟩
  · exact n06VolumeMember_fourierCut hV hvolume N
  · intro m
    exact n06_primitiveReferenceRemainder_fourierCut_ae h hradial m
      (U.1 m) (hreflect m) hη hηp U.2.1 (hrep.1 m) N
  · intro m
    rw [n06VolumeFourierCut_forget hV (3 / 4 : ℝ) 0 b N F m]
    exact (n06_primitiveReferenceSource_fourierCut_ae h hradial m _
      (n06Volume_forget_reflection hV (3 / 4 : ℝ) 0 b F m) hfp (hrep.2 m) N).trans
        (n06_primitiveReferenceTransforms_congr_ae_physical h hradial hrestore m).2
  · exact n06_referenceGraph_basisProjection_compatibility hD hb hγ f
      ((S.height (3 / 4 : ℝ)).decode S.psi) U.2.2.2 0 hgraph h0 h1

/-- Membership is in the same original N05 graph, and all scalar
coordinates are retained by the actual cutoff. -/
theorem n06N05_primitive_fourierProjection_mem_graph
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)
    (u : B.Space) (N : ℕ) (hN : 1 ≤ N) :
    (n06CanonicalUnknownFourierCut N u.val.1,
      n06VolumeFourierCut h.2.2.1 (3 / 4 : ℝ) 0 b N u.val.2) ∈ B.graph := by
  apply (h.2.2.2.2.2.2.2.1 _).mpr
  exact n06_primitive_referenceCanonicalRelation_fourierProjection h.1 hradial hgauge
    h.2.2.1 h.2.2.2.1 u.val.1 u.val.2
      ((h.2.2.2.2.2.2.2.1 u.val).mp u.property)
      (n06N05_height_reflection h.2 u) N hN

/-- The finite graph approximant has no additional compatibility-column
lift. Both modes zero and one are retained. -/
def n06PrimitiveN05GraphFourierCut
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)
    (N : ℕ) (u : B.Space) : B.Space :=
  ⟨(n06CanonicalUnknownFourierCut (N + 1) u.val.1,
      n06VolumeFourierCut h.2.2.1 (3 / 4 : ℝ) 0 b (N + 1) u.val.2),
    n06N05_primitive_fourierProjection_mem_graph h hradial hgauge u (N + 1) (by omega)⟩

section Approximation

variable
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hgauge : AuxiliaryColumnGauge S K)

theorem n06PrimitiveN05GraphFourierCut_source (N : ℕ) (u : B.Space) :
    (n06PrimitiveN05GraphFourierCut h hradial hgauge N u).val.2 =
      n06VolumeFourierCut h.2.2.1 (3 / 4 : ℝ) 0 b (N + 1) u.val.2 := rfl

theorem n06PrimitiveN05GraphFourierCut_height (N : ℕ) (u : B.Space) (m : ℕ) :
    (n06PrimitiveN05GraphFourierCut h hradial hgauge N u).val.1.1 m =
      n06CanonicalFourierCutL2 (N + 1) (u.val.1.1 m) := rfl

theorem n06PrimitiveN05GraphFourierCut_scalars (N : ℕ) (u : B.Space) :
    (n06PrimitiveN05GraphFourierCut h hradial hgauge N u).val.1.2 = u.val.1.2 := rfl

/-- The approximants are values of the same original inverse. -/
theorem n06PrimitiveN05GraphFourierCut_eq_inverse (N : ℕ) (u : B.Space) :
    n06PrimitiveN05GraphFourierCut h hradial hgauge N u =
      B.inverse (n06VolumeFourierCut h.2.2.1 (3 / 4 : ℝ) 0 b (N + 1) u.val.2) :=
  (h.2.2.2.2.2.2.2.2.2.1 (n06PrimitiveN05GraphFourierCut h hradial hgauge N u)).symm

/-- Strong convergence is in the original complete graph norm. -/
theorem n06PrimitiveN05GraphFourierCut_tendsto (u : B.Space) :
    Tendsto (fun N => n06PrimitiveN05GraphFourierCut h hradial hgauge N u)
      atTop (𝓝 u) := by
  have hsource := (n06VolumeFourierCut_tendsto h.2.2.1 (3 / 4 : ℝ) 0 b u.val.2).comp
    (tendsto_add_atTop_nat 1)
  have hlim := (B.inverse.continuous.tendsto u.val.2).comp hsource
  have hinv := h.2.2.2.2.2.2.2.2.2.1 u
  have hcut : ∀ N, B.inverse
      (n06VolumeFourierCut h.2.2.1 (3 / 4 : ℝ) 0 b (N + 1) u.val.2) =
        n06PrimitiveN05GraphFourierCut h hradial hgauge N u :=
    fun N => (n06PrimitiveN05GraphFourierCut_eq_inverse h hradial hgauge N u).symm
  simpa only [Function.comp_def, hcut, hinv] using hlim

theorem n06PrimitiveN05GraphFourierCut_mem_core (N : ℕ) (u : B.Space) :
    n06PrimitiveN05GraphFourierCut h hradial hgauge N u ∈
      n06CanonicalGraphFiniteAngularCore B := by
  refine ⟨Finset.range (N + 2), fun m => n06HalfCosineCoefficient (u.val.1.1 m),
    fun m i => ?_, fun m => ?_⟩
  · exact (n06_canonical_angularCoefficient_memLp (u.val.1.1 m)
      (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
        Real.pi⁻¹
  · exact n06CanonicalFourierCutL2_coe_cosine_ae (N + 1) (u.val.1.1 m)
      (n06N05_height_reflection h.2 u m)

include h hradial hgauge in
/-- Density inside the original graph follows from primitive radiality
and the actual radial auxiliary gauge, without coordinate cost bounds. -/
theorem n06CanonicalGraphFiniteAngularCore_dense_of_primitive :
    Dense (n06CanonicalGraphFiniteAngularCore B) := by
  intro u
  exact isClosed_closure.mem_of_tendsto
    (n06PrimitiveN05GraphFourierCut_tendsto h hradial hgauge u)
    (Eventually.of_forall (fun N => subset_closure
      (n06PrimitiveN05GraphFourierCut_mem_core h hradial hgauge N u)))

end Approximation

end ContinuousFlexibility.Statements
