import ContinuousFlexibility.Analysis.N07bPrimitiveGeometryHeight
import ContinuousFlexibility.Analysis.N07bPrimitiveTransport
import ContinuousFlexibility.Analysis.N07bReferenceBulkEnergy
import ContinuousFlexibility.Analysis.N07bReferenceSourceAssembly
import ContinuousFlexibility.Analysis.N07bFixedGraphIdentification

/-!
# Constructing the fixed graph element of the physical scalar solution

The canonical height sequence is constructed from its actual density. The
transported remainder supplies the reference graph and the smooth local
forcing representatives. The actual finite expansion supplies its source
level; compact corrections then add the prescribed left constant and
border scalar. Only after these constructions is the fixed graph inverse
used to identify the physical solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base : ℕ} {ε : ℝ}

/-- Assemble the actual reference source while the transported remainder
and its physical height are independent of the scalar inverse and graph. -/
private theorem n07b_referenceSourceLift_of_remainder
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε) (hV : IsVolumeModel T S K V)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {u R : PolarPoint → ℝ} (hu : HeightMember D T (3 / 4 : ℝ) u)
    (hR : ContDiff ℝ 2 R) (hRp : Function.Periodic R (0, Real.pi))
    (hRe : ∀ r θ, R (r, -θ) = R (r, θ))
    (hpiece : ∀ m, EqOn
      (canonicalSource S K (C.referenceState, 0) m
        (fun p : PolarPoint => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2))
      (n07bReferencePieceCanonicalSource D C K z m u) (canonicalOpen S K m))
    (hclosed : ∀ m p, p ∈ canonicalClosed S K m →
      ContDiffAt ℝ ∞ (n07bReferencePieceCanonicalSource D C K z m u) p)
    (hsource : ∀ f : S.Source, ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode f.val))
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
          n07bReferenceBulkCoefficient D T C K z m (3 / 4 : ℝ) j.val i x) ^ 2 ≤
            A * T.M x.1 ^ 2)
    (a μ : ℝ) :
    ∃ Fref : V.level (3 / 4 : ℝ) 0 b,
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b Fref m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          (n07bReferenceForcing D μ (fun p : PolarPoint => R p + a * S.chiLeft p.1)) := by
  let g : ℕ → PolarPoint → ℝ := fun m => canonicalSource S K (C.referenceState, 0) m
    (fun p : PolarPoint => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2)
  have hPp := n07b_radialPDE_periodic D.w hRp
  have hPe := n07b_radialPDE_even D.w hRe
  obtain ⟨Fbulk, hFbulk, _⟩ := n07b_exists_referenceBulkLift hK href hsref hz hs
    hD hT hV (3 / 4 : ℝ) hu b g hpiece hclosed
    (fun m _ hr => n07b_canonicalSource_periodic hK href hsref _ hPp m hr)
    (fun m => n07b_canonicalSource_reflection_ae hK href hsref _ hPe hPp m) hA hcoeff
  exact n07b_exists_referenceSource_of_bulk
    hD hT hS hborder hsource hR a μ Fbulk hFbulk

/-- The reference relation is constructed using independent physical data
and numerical weights. No scalar inverse or Banach graph is unfolded in
the height encoding, transport or source construction. -/
private theorem n07b_exists_referenceRelation_of_height
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε) (hV : IsVolumeModel T S K V)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {u : PolarPoint → ℝ} (hu : HeightMember D T (3 / 4 : ℝ) u)
    {γ : ℝ} (hγ : 0 < γ) (hγβ : γ < (3 / 4 : ℝ))
    (loss : ℝ) (hloss : 0 ≤ loss) (a μ M₀ M₁ : ℝ)
    (hrow : referenceRow D (fun p : PolarPoint => u p + a * S.chiLeft p.1) = 0)
    (hsource : ∀ f : S.Source, ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode f.val))
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
          n07bReferenceBulkCoefficient D T C K z m (3 / 4 : ℝ) j.val i x) ^ 2 ≤
            A * T.M x.1 ^ 2) :
    ∃ U₀ : CanonicalL2Sequence S K, ∃ Fref : V.level (3 / 4 : ℝ) 0 b,
      (∀ m, (U₀ m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m u) ∧
      ReferenceCanonicalRelation D T S C K V γ M₀ M₁ loss (U₀, (a, μ, 0))
        (V.forget (3 / 4 : ℝ) 0 b Fref) := by
  obtain ⟨U₀, hUvolume, hUheight⟩ :=
    n07b_exists_canonicalHeightSequence_of_primitive_geometry hD hT hV hK hz hs
      hgeom loss hloss hu
  obtain ⟨τ, q, R, η, _, hηeq, hR, _, hRp, hRe, _, _, _,
    hheight, hpiece, hclosed, hgraph⟩ :=
    n07b_exists_referenceTransport_of_primitive_geometry hD hT hborder hS.2.2.1
      hK href hsref hgeom hz hs hu hγ hγβ a μ M₀ M₁ hrow
  obtain ⟨Fref, hFref⟩ := n07b_referenceSourceLift_of_remainder
    hD hT hS hborder hK hV href hsref hz hs hu hR hRp hRe
    hpiece hclosed hsource hA hcoeff a μ
  have hFrefη : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Fref m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (n07bReferenceForcing D μ η) := by
    simpa only [hηeq] using hFref
  refine ⟨U₀, Fref, hUheight, hUvolume, η, n07bReferenceForcing D μ η,
    ⟨?_, hFrefη⟩, ?_⟩
  · intro m
    have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
        p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
      ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
    filter_upwards [hUheight m, hmem] with p hp hpmem
    exact hp.trans (hheight m ⟨hpmem.1, mem_univ _⟩).symm
  · simpa only [zero_mul, sub_zero] using hgraph

/-- Combine actual height and source representatives using only raw
physical fields and canonical sequences. -/
private theorem n07b_hasCanonicalRepresentation_of_remainder
    {z : AnnularState S × ℝ} (U₀ : CanonicalL2Sequence S K)
    (Fseq : CanonicalSequence S K) (u η f : PolarPoint → ℝ) (a μ : ℝ)
    (hη : η = fun p : PolarPoint => u p + a * S.chiLeft p.1)
    (hu : ∀ m, (U₀ m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m u)
    (hf : ∀ m, (Fseq m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f) :
    HasCanonicalRepresentation D S C K z (U₀, (a, μ, 0)) Fseq η f := by
  have hrem : (fun p : PolarPoint => η p - a * S.chiLeft p.1) = u := by
    funext p
    exact (congrArg (fun v : ℝ => v - a * S.chiLeft p.1) (congrFun hη p)).trans
      (add_sub_cancel_right (u p) (a * S.chiLeft p.1))
  refine ⟨?_, hf⟩
  intro m
  exact (hu m).trans (Filter.Eventually.of_forall (fun p =>
    congrFun (congrArg (canonicalHeight S K z m) hrem.symm) p))

/-- The chosen source coordinate represents the actual physical field. -/
def N07bCanonicalSourceRepresentation (S : PhysicalSpacesData) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (z : AnnularState S × ℝ)
    (F : V.level (3 / 4 : ℝ) 0 b) (f : PolarPoint → ℝ) : Prop :=
  ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
    =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f

/-- Every physical source has its actual reference source coordinate. -/
def N07bReferenceSourceLiftProperty (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) : Prop :=
  ∀ f : S.Source, ∃ F : V.level (3 / 4 : ℝ) 0 b,
    N07bCanonicalSourceRepresentation S K V b (C.referenceState, 0) F
      ((S.height (3 / 4 : ℝ)).decode.toFun f.val)

/-- A uniform bound for the genuine reference bulk expansion coefficients. -/
def N07bReferenceBulkCoefficientBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (b : ℕ) (A : ℝ) : Prop :=
  ∀ m x, x ∈ physicalPieceOpen S K z m →
    ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
      (n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
        n07bReferenceBulkCoefficient D T C K z m (3 / 4 : ℝ) j.val i x) ^ 2 ≤
          A * T.M x.1 ^ 2

/-- Identification of the canonical inverse with a given physical value. -/
def N07bScalarBridgeConclusion (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
    (b : ℕ) (B : CanonicalDomainData S K V b)
    (P : RelativeInverseData S K V b B) (z : AnnularState S × ℝ)
    (F : V.level (3 / 4 : ℝ) 0 b) (sol : HeightPair S × ℝ)
    (f : PolarPoint → ℝ) : Prop :=
  let d := B.inverse (P.inverse z F)
  d.val.1.2.2.2 = 0 ∧ d.val.1.2.1 = sol.1.2 ∧
    d.val.1.2.2.1 = sol.2 ∧
    HasCanonicalRepresentation D S C K z d.val.1
      (V.forget (3 / 4 : ℝ) 0 b F) (heightPairField S sol.1) f

variable
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {G : ScalarInverseData S}

local instance n07bScalarBridgeLevelNormedAddCommGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n07bScalarBridgeLevelNormedSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n07bScalarBridgeUnknownNormedAddCommGroup :
    NormedAddCommGroup (CanonicalUnknown S K) := inferInstance
local instance n07bScalarBridgeUnknownNormedSpace :
    NormedSpace ℝ (CanonicalUnknown S K) := inferInstance
local instance n07bScalarBridgeDomainNormedAddCommGroup :
    NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _
local instance n07bScalarBridgeDomainNormedSpace :
    NormedSpace ℝ B.Space := Submodule.normedSpace _

set_option diagnostics true in
/-- At each state the represented physical scalar solution is the actual
chosen Banach solution, with all scalar coordinates retained. The only
quantitative premise concerns genuine geometric finite-expansion fields. -/
theorem n07b_scalarInverse_banach_identification
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hborder : RadialTrueBorder D)
    (hK : N04PartA D S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hsource : N07bReferenceSourceLiftProperty S C K V b)
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : N07bReferenceBulkCoefficientBound D T S C K z b A)
    (f : S.Source) (F : V.level (3 / 4 : ℝ) 0 b)
    (hF : N07bCanonicalSourceRepresentation S K V b z F
      ((S.height (3 / 4 : ℝ)).decode.toFun f.val)) :
    N07bScalarBridgeConclusion D S C K V b B P z F
      ((G.G z).toLinearMap.toFun f) ((S.height (3 / 4 : ℝ)).decode.toFun f.val) := by
  run_tac Lean.logInfo "N07b scalar bridge body entered"
  let sol : HeightPair S × ℝ := (G.G z).toLinearMap.toFun f
  let decodeRaw : (S.height (3 / 4 : ℝ)).Space → PolarPoint → ℝ :=
    (S.height (3 / 4 : ℝ)).decode.toFun
  let u : PolarPoint → ℝ := decodeRaw sol.1.1
  let a : ℝ := sol.1.2
  let μ : ℝ := sol.2
  have hu : HeightMember D T (3 / 4 : ℝ) u :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.1 sol.1.1
  have hprofile : RadialProfileGeometry D := hD.choose_spec.1
  have hrow : referenceRow D (fun p => u p + a * S.chiLeft p.1) = 0 :=
    (hG.1 z hz hs f).1
  obtain ⟨U₀, Fref, hUheight, hreference⟩ :=
    n07b_exists_referenceRelation_of_height hD hT hS hborder hK h05.2.1 hgeom
      href hsref hz hs hu h05.2.2.1 h05.2.2.2.1 B.lossMaterial h05.2.2.2.2.1
      a μ B.sourceMaterial B.outputMaterial hrow hsource hA hcoeff
  let U : CanonicalUnknown S K := (U₀, (a, μ, 0))
  have hrep : HasCanonicalRepresentation D S C K z U
      (V.forget (3 / 4 : ℝ) 0 b F)
      (heightPairField S sol.1) (decodeRaw f.val) :=
    n07b_hasCanonicalRepresentation_of_remainder (D := D) (C := C) (z := z)
      U₀ (V.forget (3 / 4 : ℝ) 0 b F) u (heightPairField S sol.1)
      (decodeRaw f.val) a μ rfl hUheight hF
  have hdone : N07bScalarBridgeConclusion D S C K V b B P z F sol (decodeRaw f.val) :=
    n07b_fixedGraph_scalarInverse_identification hT hS hK h05 h06 hG hgeom
      hprofile.2.1 hz hs f F Fref U hreference hrep rfl rfl rfl
  run_tac Lean.logInfo "N07b scalar bridge final term elaborated"
  exact hdone

end ContinuousFlexibility.Analysis
