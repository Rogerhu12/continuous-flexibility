import ContinuousFlexibility.Analysis.N06CanonicalGraphFourierProjection

/-!
# Density of finite angular heights in the original canonical graph

The compatibility column is constructed in the original volume model from
its actual smooth compact physical field. The resulting approximants
belong to the same graph, retain all three original scalar coordinates,
and have one common finite frequency set on every canonical piece. Their
strong convergence is in the original complete graph norm.
-/

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

/-- This is the actual height core inside the original graph. Radial
coefficients belong to the original piece L2 spaces; finite support in
the piece index and smoothness of radial coefficients are not imposed. -/
def n06CanonicalGraphFiniteAngularCore (B : CanonicalDomainData S K V b) :
    Set B.Space :=
  {u | ∃ I : Finset ℕ, ∃ a : ℕ → ℕ → ℝ → ℝ,
    (∀ m i, MemLp (a m i) 2 (volume.restrict (Ioo (K.left m) (K.right m)))) ∧
    ∀ m, (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis I (a m) referenceAngularBasis}

/-- The genuine compatibility source is available without making it an
additional choice in the density theorem. -/
theorem n06Volume_exists_referenceCompatibilitySource
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (s : ℕ) :
    ∃ Psi : V.level γ t s, ∀ m,
      (V.forget γ t s Psi m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode S.psi) := by
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  obtain ⟨columns, hcolumns, _⟩ := n06Volume_exists_controlled_referenceScalarColumns
    h01.1.1 hT hS h01.1.2.2.2.1 hV h hcoordinates γ t s
  refine ⟨columns 2, fun m => ?_⟩
  simpa [n06ReferenceScalarField] using hcolumns (2 : Fin 3) m

section FixedColumn

variable
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (Psi : V.level (3 / 4 : ℝ) 0 b)
    (hPsi : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Psi m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode S.psi))

theorem n06N05GraphFourierCut_mem_core (N : ℕ) (u : B.Space) :
    n06N05GraphFourierCut h hcoordinates Psi hPsi N u ∈
      n06CanonicalGraphFiniteAngularCore B := by
  refine ⟨Finset.range (N + 2), fun m => n06HalfCosineCoefficient (u.val.1.1 m),
    fun m i => ?_, fun m => ?_⟩
  · exact (n06_canonical_angularCoefficient_memLp (u.val.1.1 m)
      (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
        Real.pi⁻¹
  · exact n06CanonicalFourierCutL2_coe_cosine_ae (N + 1) (u.val.1.1 m)
      (n06N05_height_reflection h.2 u m)

include h hcoordinates Psi hPsi in
/-- No change of graph or inverse is used to take the closure. -/
theorem n06CanonicalGraphFiniteAngularCore_dense_of_column :
    Dense (n06CanonicalGraphFiniteAngularCore B) := by
  intro u
  exact isClosed_closure.mem_of_tendsto
    (n06N05GraphFourierCut_tendsto h hcoordinates Psi hPsi u)
    (Eventually.of_forall (fun N => subset_closure
      (n06N05GraphFourierCut_mem_core h hcoordinates Psi hPsi N u)))

end FixedColumn

/-- The density theorem uses only the actual N05 construction and its
controlled reference coordinates, without a supplied source column. -/
theorem n06CanonicalGraphFiniteAngularCore_dense
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K) :
    Dense (n06CanonicalGraphFiniteAngularCore B) := by
  obtain ⟨Psi, hPsi⟩ := n06Volume_exists_referenceCompatibilitySource
    hT hS h.2.2.1 h.1 hcoordinates (3 / 4 : ℝ) 0 b
  exact n06CanonicalGraphFiniteAngularCore_dense_of_column h hcoordinates Psi hPsi

end ContinuousFlexibility.Statements
