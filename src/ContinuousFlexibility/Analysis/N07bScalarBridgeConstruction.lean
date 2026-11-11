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
  {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {G : ScalarInverseData S}

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
    (hsource : ∀ f : S.Source, ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          ((S.height (3 / 4 : ℝ)).decode f.val))
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bReferenceBulkIndex j.val,
        (n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
          n07bReferenceBulkCoefficient D T C K z m (3 / 4 : ℝ) j.val i x) ^ 2 ≤
            A * T.M x.1 ^ 2)
    (f : S.Source) (F : V.level (3 / 4 : ℝ) 0 b)
    (hF : ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m
        ((S.height (3 / 4 : ℝ)).decode f.val)) :
    let d := B.inverse (P.inverse z F)
    d.val.1.2.2.2 = 0 ∧ d.val.1.2.1 = (G.G z f).1.2 ∧
      d.val.1.2.2.1 = (G.G z f).2 ∧
      HasCanonicalRepresentation D S C K z d.val.1
        (V.forget (3 / 4 : ℝ) 0 b F)
        (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val) := by
  let u : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode (G.G z f).1.1
  let a : ℝ := (G.G z f).1.2
  let μ : ℝ := (G.G z f).2
  have hu : HeightMember D T (3 / 4 : ℝ) u :=
    (hS.1 (3 / 4 : ℝ)).2.2.2.1 (G.G z f).1.1
  have hV : IsVolumeModel T S K V := h05.2.1
  have hprofile : RadialProfileGeometry D := hD.choose_spec.1
  obtain ⟨U₀, hUvolume, hUheight⟩ :=
    n07b_exists_canonicalHeightSequence_of_primitive_geometry hD hT hV hK hz hs
      hgeom B.lossMaterial h05.2.2.2.2.1 hu
  let U : CanonicalUnknown S K := (U₀, (a, μ, 0))
  have hrow : referenceRow D (fun p => u p + a * S.chiLeft p.1) = 0 :=
    (hG.1 z hz hs f).1
  obtain ⟨τ, q, R, η, _, hηeq, hR, _, hRp, hRe, _, _, hRpiece,
    hheight, hpiece, hclosed, hgraph⟩ :=
    n07b_exists_referenceTransport_of_primitive_geometry hD hT hborder hS.2.2.1
      hK href hsref hgeom hz hs hu h05.2.2.1 h05.2.2.2.1
      a μ B.sourceMaterial B.outputMaterial hrow
  let g : ℕ → PolarPoint → ℝ := fun m => canonicalSource S K (C.referenceState, 0) m
    (fun p => radialPDE D.w (fun r θ => R (r, θ)) p.1 p.2)
  have hPp := n07b_radialPDE_periodic D.w hRp
  have hPe := n07b_radialPDE_even D.w hRe
  obtain ⟨Fbulk, hFbulk, _⟩ := n07b_exists_referenceBulkLift hK href hsref hz hs
    hD hT hV (3 / 4 : ℝ) hu b g hpiece hclosed
    (fun m _ hr => n07b_canonicalSource_periodic hK href hsref _ hPp m hr)
    (fun m => n07b_canonicalSource_reflection_ae hK href hsref _ hPe hPp m) hA hcoeff
  obtain ⟨Fref, hFref⟩ := n07b_exists_referenceSource_of_bulk
    hD hT hS hborder hsource hR a μ Fbulk hFbulk
  have hFrefη : ∀ m, (V.forget (3 / 4 : ℝ) 0 b Fref m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        (n07bReferenceForcing D μ η) := by
    simpa only [hηeq] using hFref
  have hreference : ReferenceCanonicalRelation D T S C K V B.weakExponent
      B.sourceMaterial B.outputMaterial B.lossMaterial U
        (V.forget (3 / 4 : ℝ) 0 b Fref) := by
    refine ⟨hUvolume, η, n07bReferenceForcing D μ η, ⟨?_, hFrefη⟩, ?_⟩
    · intro m
      have hmem : ∀ᵐ p ∂canonicalMeasure S K m,
          p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
        ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
      filter_upwards [hUheight m, hmem] with p hp hpmem
      exact hp.trans (hheight m ⟨hpmem.1, mem_univ _⟩).symm
    · simpa only [U, zero_mul, sub_zero] using hgraph
  have hrem : (fun p => heightPairField S (G.G z f).1 p - a * S.chiLeft p.1) = u := by
    funext p
    change u p + a * S.chiLeft p.1 - a * S.chiLeft p.1 = u p
    ring
  have hrep : HasCanonicalRepresentation D S C K z U
      (V.forget (3 / 4 : ℝ) 0 b F)
      (heightPairField S (G.G z f).1) ((S.height (3 / 4 : ℝ)).decode f.val) := by
    refine ⟨?_, hF⟩
    intro m
    change (U₀ m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m (fun p => heightPairField S (G.G z f).1 p - a * S.chiLeft p.1)
    rw [hrem]
    exact hUheight m
  exact n07b_fixedGraph_scalarInverse_identification hT hS hK h05 h06 hG hgeom
    hprofile.2.1 hz hs f F Fref U hreference hrep rfl rfl rfl

end ContinuousFlexibility.Analysis
