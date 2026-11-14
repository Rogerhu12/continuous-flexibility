module

public import ContinuousFlexibility.Analysis.N06RelativeBoundarySymmetry
public import ContinuousFlexibility.Analysis.N06RelativeCanonicalBoundaryPatch
public import ContinuousFlexibility.Analysis.N05CanonicalBoundarySymmetry

/-!
# The actual relative N04 patches retain period and reflection

The original open-piece symmetries have already been extended to the
closed physical piece. Their true radial jets, including at the endpoints,
therefore supply the symmetries of the constructed Taylor corrections.
The new fields retain the original pi lift and the even/odd reflection
without a separate symmetry hypothesis on a chosen extension.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

private theorem n06_symmetryBoundary_data
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    (side : Bool) (θ : ℝ) :
    ContDiffAt ℝ ∞ (K.chart z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
      ContDiffAt ℝ ∞ (K.height z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
      0 < K.height z m (if side then K.physicalRight m else K.physicalLeft m, θ) :=
  n06_actualCanonical_boundary_data h04.1 hz hs m hΩ side θ

/-- The explicit current patch retains the original pi angular lift and
the height's pi periodicity on the whole closed physical piece. -/
theorem n06_relativeCanonicalPatch_closed_periodicity
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (δ : ℝ) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m) {x : ℝ}
    (hx : x ∈ Icc (K.physicalLeft m) (K.physicalRight m)) (θ : ℝ) :
    n06RelativeCanonicalChart C K δ z m (x, θ + Real.pi) =
        n06RelativeCanonicalChart C K δ z m (x, θ) + (0, Real.pi) ∧
      n06RelativeCanonicalHeight C K δ z m (x, θ + Real.pi) =
        n06RelativeCanonicalHeight C K δ z m (x, θ) := by
  have h₀ := n06_symmetryBoundary_data h04 href hsref m (h04.1.referenceDomain m)
  have hc := n06_symmetryBoundary_data h04 hz hs m hΩ
  have hperiod₀ (y : ℝ) (hy : y ∈ Icc (K.physicalLeft m) (K.physicalRight m))
      (η : ℝ) := n05_canonical_closed_periodicity h04 href hsref m (p := (y, η))
        (n06_mem_physicalPieceClosed_of_reference_rectangle h04.1 m (h04.1.referenceDomain m) hy)
  have hperiod (y : ℝ) (hy : y ∈ Icc (K.physicalLeft m) (K.physicalRight m))
      (η : ℝ) := n05_canonical_closed_periodicity h04 hz hs m (p := (y, η))
        (n06_mem_physicalPieceClosed_of_reference_rectangle h04.1 m hΩ hy)
  constructor
  · have he := n06RelativeChartPatch_transform (δ := δ) (h04.1.referenceBounds m).1
      (fun side η => (h₀ side η).1) (fun side η => (hc side η).1)
      (fun η => η + Real.pi) (1, 1) (fun _ => (0, Real.pi))
      (fun y hy η => by
        simpa only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd,
          Prod.mk_add_mk, add_zero, one_mul] using (hperiod₀ y hy η).1)
      (fun _ y hy η => by
        simpa only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd,
          Prod.mk_add_mk, add_zero, one_mul] using (hperiod y hy η).1) hx θ
    simpa only [n06RelativeCanonicalChart, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
      Prod.fst, Prod.snd, add_zero, one_mul] using he
  · exact n06RelativeHeightPatch_transform (δ := δ) (h04.1.referenceBounds m).1
      (fun side η => (h₀ side η).2.1) (fun side η => (hc side η).2.1)
      (fun side η => (h₀ side η).2.2) (fun side η => (hc side η).2.2)
      (fun η => η + Real.pi)
      (fun y hy η => by simpa only [Prod.mk_add_mk, add_zero] using (hperiod₀ y hy η).2)
      (fun _ y hy η => by simpa only [Prod.mk_add_mk, add_zero] using (hperiod y hy η).2)
      hx θ

/-- The explicit current patch retains the original even radial / odd
angular reflection and the even positive height on the closed piece. -/
theorem n06_relativeCanonicalPatch_closed_reflection
    (h04 : N04Properties D T S C L K base loss ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (δ : ℝ) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m) {x : ℝ}
    (hx : x ∈ Icc (K.physicalLeft m) (K.physicalRight m)) (θ : ℝ) :
    n06RelativeCanonicalChart C K δ z m (x, -θ) =
        ((n06RelativeCanonicalChart C K δ z m (x, θ)).1,
          -(n06RelativeCanonicalChart C K δ z m (x, θ)).2) ∧
      n06RelativeCanonicalHeight C K δ z m (x, -θ) =
        n06RelativeCanonicalHeight C K δ z m (x, θ) := by
  have h₀ := n06_symmetryBoundary_data h04 href hsref m (h04.1.referenceDomain m)
  have hc := n06_symmetryBoundary_data h04 hz hs m hΩ
  have hreflect₀ (y : ℝ) (hy : y ∈ Icc (K.physicalLeft m) (K.physicalRight m))
      (η : ℝ) := n05_canonical_closed_reflection h04 href hsref m (p := (y, η))
        (n06_mem_physicalPieceClosed_of_reference_rectangle h04.1 m (h04.1.referenceDomain m) hy)
  have hreflect (y : ℝ) (hy : y ∈ Icc (K.physicalLeft m) (K.physicalRight m))
      (η : ℝ) := n05_canonical_closed_reflection h04 hz hs m (p := (y, η))
        (n06_mem_physicalPieceClosed_of_reference_rectangle h04.1 m hΩ hy)
  constructor
  · have he := n06RelativeChartPatch_transform (δ := δ) (h04.1.referenceBounds m).1
      (fun side η => (h₀ side η).1) (fun side η => (hc side η).1)
      (fun η => -η) (1, -1) (fun _ => (0, 0))
      (fun y hy η => by
        simpa only [Prod.fst, Prod.snd, one_mul, neg_one_mul, add_zero]
          using (hreflect₀ y hy η).1)
      (fun _ y hy η => by
        simpa only [Prod.fst, Prod.snd, one_mul, neg_one_mul, add_zero]
          using (hreflect y hy η).1) hx θ
    simpa only [n06RelativeCanonicalChart, Prod.fst, Prod.snd, one_mul, neg_one_mul,
      add_zero] using he
  · exact n06RelativeHeightPatch_transform (δ := δ) (h04.1.referenceBounds m).1
      (fun side η => (h₀ side η).2.1) (fun side η => (hc side η).2.1)
      (fun side η => (h₀ side η).2.2) (fun side η => (hc side η).2.2)
      (fun η => -η) (fun y hy η => (hreflect₀ y hy η).2)
      (fun _ y hy η => (hreflect y hy η).2) hx θ

end ContinuousFlexibility.Statements
