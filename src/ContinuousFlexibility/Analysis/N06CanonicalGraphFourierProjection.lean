module

public import ContinuousFlexibility.Analysis.N06CompatibilityFourierSource
public import ContinuousFlexibility.Analysis.N06ReferenceProjectionRemainder
public import ContinuousFlexibility.Analysis.N06ReferenceGraphFourierProjection
public import ContinuousFlexibility.Analysis.N06NegativeForcingParity
public import ContinuousFlexibility.Analysis.N06ControlledReferenceSources

/-!
# Actual finite angular approximants in the same N05 graph

The height is cut off while all three scalar coordinates are retained.
The source is cut after subtracting the original compatibility column,
which is then restored unchanged. Physical reference graph projection
and the actual reference-coordinate identities prove membership in the
original graph. Its given inverse identifies these graph elements and
proves strong convergence in the original graph norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

/-- Projection is proved first in the original physical relation, before
introducing the selected closed graph subtype. -/
theorem n06_referenceCanonicalRelation_fourierProjection
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V)
    {γ M₀ M₁ ell : ℝ} (hγ : 0 < γ)
    (Psi : V.level (3 / 4 : ℝ) 0 b)
    (hPsi : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Psi m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode S.psi))
    (U : CanonicalUnknown S K) (F : V.level (3 / 4 : ℝ) 0 b)
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ ell U
      (V.forget (3 / 4 : ℝ) 0 b F))
    (hreflect : ∀ m, (fun p : PolarPoint => U.1 m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U.1 m : PolarPoint → ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    ReferenceCanonicalRelation D T S C K V γ M₀ M₁ ell
      (n06CanonicalUnknownFourierCut N U)
      (V.forget (3 / 4 : ℝ) 0 b (n06CompatibilityFourierSource hV Psi U.2.2.2 F N)) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have hD : IsAccumulatingProfile D := h01.1.1
  have hb : RadialTrueBorder D := h01.1.2.2.2.1
  obtain ⟨hvolume, η, f, hrep, hgraph⟩ := hrel
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hb hγ hgraph.1
  obtain ⟨a, ha⟩ := hgraph.1
  have hηp : Function.Periodic η (0, Real.pi) := ha.2.2.1
  have hg : Function.Periodic
      (fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p)
      (0, Real.pi) := hgraph.2.1.2.2.1
  have h0 : 0 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  refine ⟨?_, referenceBasisProjection (Finset.range (N + 1)) η,
    (fun p => referenceBasisProjection (Finset.range (N + 1))
      (fun q => f q - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi q) p +
        U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), ⟨?_, ?_⟩, ?_⟩
  · exact n06VolumeMember_fourierCut hV hvolume N
  · intro m
    exact n06_controlledReferenceRemainder_fourierCut_ae h hcoordinates m
      (U.1 m) (hreflect m) hη hηp U.2.1 (hrep.1 m) N
  · intro m
    exact n06CompatibilityFourierSource_physical h hcoordinates hV
      Psi U.2.2.2 F N m hg (hrep.2 m) (hPsi m)
  · exact n06_referenceGraph_basisProjection_compatibility hD hb hγ f
      ((S.height (3 / 4 : ℝ)).decode S.psi) U.2.2.2 0 hgraph h0 h1

/-- The original graph is preserved by the genuine finite projection,
with the same scalar coordinates and the unchanged compatibility field. -/
theorem n06N05_fourierProjection_mem_graph
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (Psi : V.level (3 / 4 : ℝ) 0 b)
    (hPsi : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Psi m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode S.psi))
    (u : B.Space) (N : ℕ) (hN : 1 ≤ N) :
    (n06CanonicalUnknownFourierCut N u.val.1,
      n06CompatibilityFourierSource h.2.2.1 Psi u.val.1.2.2.2 u.val.2 N) ∈ B.graph := by
  apply (h.2.2.2.2.2.2.2.1 _).mpr
  exact n06_referenceCanonicalRelation_fourierProjection h.1 hcoordinates h.2.2.1
    h.2.2.2.1 Psi hPsi u.val.1 u.val.2
    ((h.2.2.2.2.2.2.2.1 u.val).mp u.property) (n06N05_height_reflection h.2 u) N hN

/-- A canonical graph approximant; the index N retains modes through
N + 1, so both the mean and the true border mode are always present. -/
def n06N05GraphFourierCut
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (Psi : V.level (3 / 4 : ℝ) 0 b)
    (hPsi : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Psi m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode S.psi))
    (N : ℕ) (u : B.Space) : B.Space :=
  ⟨(n06CanonicalUnknownFourierCut (N + 1) u.val.1,
      n06CompatibilityFourierSource h.2.2.1 Psi u.val.1.2.2.2 u.val.2 (N + 1)),
    n06N05_fourierProjection_mem_graph h hcoordinates Psi hPsi u (N + 1) (by omega)⟩

section Approximation

variable
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (Psi : V.level (3 / 4 : ℝ) 0 b)
    (hPsi : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Psi m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode S.psi))

theorem n06N05GraphFourierCut_source (N : ℕ) (u : B.Space) :
    (n06N05GraphFourierCut h hcoordinates Psi hPsi N u).val.2 =
      n06CompatibilityFourierSource h.2.2.1 Psi u.val.1.2.2.2 u.val.2 (N + 1) := rfl

theorem n06N05GraphFourierCut_height (N : ℕ) (u : B.Space) (m : ℕ) :
    (n06N05GraphFourierCut h hcoordinates Psi hPsi N u).val.1.1 m =
      n06CanonicalFourierCutL2 (N + 1) (u.val.1.1 m) := rfl

theorem n06N05GraphFourierCut_scalars (N : ℕ) (u : B.Space) :
    (n06N05GraphFourierCut h hcoordinates Psi hPsi N u).val.1.2 = u.val.1.2 := rfl

/-- The graph approximants are values of the same given N05 inverse,
not solutions of a new boundary problem or a newly defined inverse. -/
theorem n06N05GraphFourierCut_eq_inverse (N : ℕ) (u : B.Space) :
    n06N05GraphFourierCut h hcoordinates Psi hPsi N u =
      B.inverse (n06CompatibilityFourierSource h.2.2.1 Psi u.val.1.2.2.2 u.val.2 (N + 1)) :=
  (h.2.2.2.2.2.2.2.2.2.1 (n06N05GraphFourierCut h hcoordinates Psi hPsi N u)).symm

theorem n06N05GraphFourierCut_source_tendsto (u : B.Space) :
    Tendsto (fun N => (n06N05GraphFourierCut h hcoordinates Psi hPsi N u).val.2)
      atTop (𝓝 u.val.2) := by
  exact (n06CompatibilityFourierSource_tendsto h.2.2.1 Psi u.val.1.2.2.2 u.val.2).comp
    (tendsto_add_atTop_nat 1)

/-- Strong convergence holds in the original complete graph norm. -/
theorem n06N05GraphFourierCut_tendsto (u : B.Space) :
    Tendsto (fun N => n06N05GraphFourierCut h hcoordinates Psi hPsi N u) atTop (𝓝 u) := by
  have hsource := n06N05GraphFourierCut_source_tendsto h hcoordinates Psi hPsi u
  have hlim := (B.inverse.continuous.tendsto u.val.2).comp hsource
  have hinv := h.2.2.2.2.2.2.2.2.2.1 u
  have hcut : ∀ N, B.inverse
      (n06CompatibilityFourierSource h.2.2.1 Psi u.val.1.2.2.2 u.val.2 (N + 1)) =
        n06N05GraphFourierCut h hcoordinates Psi hPsi N u :=
    fun N => (n06N05GraphFourierCut_eq_inverse h hcoordinates Psi hPsi N u).symm
  simpa only [Function.comp_def, n06N05GraphFourierCut_source, hcut, hinv] using hlim

end Approximation

end ContinuousFlexibility.Statements
