module

public import ContinuousFlexibility.Analysis.N07bCanonicalSourceIntegrability
public import ContinuousFlexibility.Analysis.PointwiseCylinderJets
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual canonical source jets on a single dynamic piece

The stored boundary inverse germ makes the actual canonical source smooth
at every point of the closed canonical cylinder whenever the physical
source is smooth at every point of the actual physical closure. Compactness
is used only on the fixed canonical fundamental rectangle.

The generic extension lemmas also treat an arbitrary canonical field that
agrees on the open piece with a smooth closed-piece extension. They do not
require the original field to be smooth across interfaces. No estimate
uniform in the piece or state, and no global summability, is asserted.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A pointwise smooth extension has bounded actual jets on a compact
closed canonical fundamental rectangle. -/
theorem n07b_canonical_mixedDerivative_bound_closed
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    {e : PolarPoint → ℝ}
    (he : ∀ p ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e p) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈
      Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi,
        ‖mixedDerivative a b e p‖ ≤ B := by
  have hcont : ContinuousOn (mixedDerivative a b e)
      (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) := by
    intro p hp
    exact (contDiffAt_mixedDerivative (he p ⟨hp.1, mem_univ _⟩) a b).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image hcont.norm
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp
  exact (hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)

/-- Actual jets of a smooth closed-piece extension belong to the given
canonical L² space. Only the canonical rectangle is used. -/
theorem n07b_canonical_mixedDerivative_memLp_closed
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    {e : PolarPoint → ℝ}
    (he : ∀ p ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e p) (a b : ℕ) :
    MemLp (mixedDerivative a b e) 2 (canonicalMeasure S K m) := by
  have hcont : ContinuousOn (mixedDerivative a b e)
      (Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi) := by
    intro p hp
    exact (contDiffAt_mixedDerivative
      (he p ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩) a b).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (mixedDerivative a b e)
      (canonicalMeasure S K m) :=
    hcont.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioc)
  obtain ⟨B, _, hB⟩ := n07b_canonical_mixedDerivative_bound_closed m he a b
  refine MemLp.of_bound hmeas B ?_
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [ha] with p hp
  exact hB p ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2⟩⟩

/-- Equality on the actual canonical open set identifies all actual jets
there with those of a closed-piece extension. No boundary value of g is
used in the resulting bound. -/
theorem n07b_canonical_mixedDerivative_bound_of_extension
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    {g e : PolarPoint → ℝ} (hge : EqOn g e (canonicalOpen S K m))
    (he : ∀ p ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e p) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈
      Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi,
        ‖mixedDerivative a b g p‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := n07b_canonical_mixedDerivative_bound_closed m he a b
  have hjets := mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hge a b
  refine ⟨B, hB, ?_⟩
  intro p hp
  rw [hjets ⟨hp.1, mem_univ _⟩]
  exact hbound p ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2⟩⟩

/-- A smooth extension on the closed canonical piece suffices for the
actual open-piece jets of an arbitrary raw canonical field to be in L².
The raw field need not be globally smooth or smooth across interfaces. -/
theorem n07b_canonical_mixedDerivative_memLp_of_extension
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    {g e : PolarPoint → ℝ} (hge : EqOn g e (canonicalOpen S K m))
    (he : ∀ p ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e p) (a b : ℕ) :
    MemLp (mixedDerivative a b g) 2 (canonicalMeasure S K m) := by
  have hjets := mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hge a b
  have hAE : mixedDerivative a b e =ᵐ[canonicalMeasure S K m] mixedDerivative a b g := by
    have ha : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [ha] with p hp
    exact (hjets ⟨hp.1, mem_univ _⟩).symm
  exact MemLp.ae_eq hAE (n07b_canonical_mixedDerivative_memLp_closed m he a b)

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hK hz hsector

/-- The physical source factor is smooth at every point of the actual
physical closure where the physical source is smooth. -/
theorem n07b_contDiffAt_physicalSourceFactor (m : ℕ)
    {f : PolarPoint → ℝ} {p : PolarPoint}
    (hp : p ∈ physicalPieceClosed S K z m)
    (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞
      (fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|) p := by
  have hclosed := (hK.boundary z hz hsector m).2.2.2.2.1 p hp
  have hJ := ContinuousFlexibility.contDiffAt_planeJacobian hclosed.1
  exact (hclosed.2.1.mul hf).div (hJ.abs hclosed.2.2.1)
    (abs_ne_zero.mpr hclosed.2.2.1)

/-- The actual stored inverse, including its genuine boundary germ,
gives smoothness of the actual canonical source at closed-piece points. -/
theorem n07b_contDiffAt_canonicalSource_closed (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p)
    {p : PolarPoint} (hp : p ∈ canonicalClosed S K m) :
    ContDiffAt ℝ ∞ (canonicalSource S K z m f) p := by
  have hx := (hK.boundary z hz hsector m).2.1 hp
  have hraw := n07b_contDiffAt_physicalSourceFactor hK hz hsector m hx (hf _ hx)
  have hinv := n04b_inverseChart_contDiffAt_closed hK hz hsector m hp
  change ContDiffAt ℝ ∞
    ((fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|) ∘
      K.inverseChart z m) p
  exact hraw.comp p hinv

/-- Closed-piece physical smoothness gives the usual open canonical
smoothness without assuming a static physical rectangle. -/
theorem n07b_contDiffOn_canonicalSource (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) :
    ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m) := by
  intro p hp
  exact (n07b_contDiffAt_canonicalSource_closed hK hz hsector m hf
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩).contDiffWithinAt

/-- The actual mixed jet composed with the chart has a local bound at
every point of the actual physical closure. -/
theorem n07b_canonicalSource_mixedDerivative_local_bound
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ physicalPieceClosed S K z m) :
    ∃ B : ℝ, ∀ᶠ x in 𝓝 p, x ∈ physicalPieceOpen S K z m →
      ‖mixedDerivative a b (canonicalSource S K z m f) (K.chart z m x)‖ ≤ B := by
  have hclosed := hK.boundary z hz hsector m
  have hsource := n07b_contDiffAt_canonicalSource_closed hK hz hsector m hf (hclosed.1 hp)
  have hjet : ContinuousAt
      (fun x => mixedDerivative a b (canonicalSource S K z m f) (K.chart z m x)) p :=
    (contDiffAt_mixedDerivative hsource a b).continuousAt.comp
      (hclosed.2.2.2.2.1 p hp).1.continuousAt
  refine ⟨‖mixedDerivative a b (canonicalSource S K z m f) (K.chart z m p)‖ + 1, ?_⟩
  filter_upwards [hjet.norm.eventually_le_const (lt_add_one _)] with x hx
  exact fun _ => hx

/-- A compact canonical rectangle bounds every actual source jet, including
the canonical boundary values supplied by the genuine inverse germ. -/
theorem n07b_canonicalSource_mixedDerivative_bound_closed
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈
      Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi,
        ‖mixedDerivative a b (canonicalSource S K z m f) p‖ ≤ B :=
  n07b_canonical_mixedDerivative_bound_closed m
    (fun _ hp => n07b_contDiffAt_canonicalSource_closed hK hz hsector m hf hp) a b

/-- The original open fundamental-rectangle bound follows from the actual
closed canonical bound. -/
theorem n07b_canonicalSource_mixedDerivative_bound
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈
      Ioo (K.left m) (K.right m) ×ˢ Ioo (0 : ℝ) Real.pi,
        ‖mixedDerivative a b (canonicalSource S K z m f) p‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    n07b_canonicalSource_mixedDerivative_bound_closed hK hz hsector m hf a b
  exact ⟨B, hB, fun p hp =>
    hbound p ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩⟩

/-- Every actual mixed derivative of the actual source conversion belongs
to the prescribed piece's L² space. -/
theorem n07b_canonicalSource_mixedDerivative_memLp
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f p) (a b : ℕ) :
    MemLp (mixedDerivative a b (canonicalSource S K z m f))
      2 (canonicalMeasure S K m) :=
  n07b_canonical_mixedDerivative_memLp_closed m
    (fun _ hp => n07b_contDiffAt_canonicalSource_closed hK hz hsector m hf hp) a b

/-- Globally smooth physical data satisfy the actual closed-domain input. -/
theorem n07b_canonicalSource_mixedDerivative_memLp_of_contDiff
    (m : ℕ) {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℕ) :
    MemLp (mixedDerivative a b (canonicalSource S K z m f))
      2 (canonicalMeasure S K m) :=
  n07b_canonicalSource_mixedDerivative_memLp hK hz hsector m
    (fun _ _ => hf.contDiffAt) a b

end ContinuousFlexibility.Analysis
