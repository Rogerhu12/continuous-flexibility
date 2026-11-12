import ContinuousFlexibility.Analysis.N06ReferenceWeakTransport

/-!
# The original N05 graph has the canonical reference equation

The physical witnesses in the reference relation are eliminated using
their actual almost-everywhere height and source representations. The
resulting forcing keeps the original source and all three scalar columns,
with the space model's actual left cutoff. This is a consequence of the
frozen N05 graph, not an additional equation imposed on its elements.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- The actual reference forcing after subtracting the left height and
applying the positive canonical sign. -/
def n06ReferenceCanonicalForcing (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ) :
    PolarPoint → ℝ := fun p =>
  -F m p + U.2.1 * canonicalSource S K (C.referenceState, 0) m
    (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) p +
  U.2.2.1 * canonicalSource S K (C.referenceState, 0) m (n06ReferenceNuField D) p +
  U.2.2.2 * canonicalSource S K (C.referenceState, 0) m
    ((S.height (3 / 4 : ℝ)).decode S.psi) p

theorem n06ReferenceCanonicalForcing_ae
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    {f : PolarPoint → ℝ} {m : ℕ}
    (hF : (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K (C.referenceState, 0) m f) :
    (fun p => -canonicalSource S K (C.referenceState, 0) m
      (n06ReferenceRemainderForcing D S.chiLeft
        (fun q => f q - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi q)
          U.2.2.1 U.2.1) p) =ᵐ[canonicalMeasure S K m]
      n06ReferenceCanonicalForcing D S C K U F m := by
  filter_upwards [hF] with p hp
  simp only [n06ReferenceCanonicalForcing, hp, n06ReferenceRemainderForcing,
    canonicalSource, div_eq_mul_inv]
  ring

/-- The original reference relation supplies the physical weak equation
and both genuine integrable pairings used by the change of coordinates. -/
theorem n06_referenceCanonicalRelation_positive_weak
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base m : ℕ} {ε γ M₀ M₁ loss : ℝ}
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (hm : K.positive m = true)
    {U : CanonicalUnknown S K} {F : CanonicalSequence S K}
    (hrel : ReferenceCanonicalRelation D T S C K V γ M₀ M₁ loss U F)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, U.1 m p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, n06ReferenceCanonicalForcing D S C K U F m p * φ p
        ∂canonicalMeasure S K m := by
  obtain ⟨_, η, f, hrep, hgraph⟩ := hrel
  have hχ : ContDiff ℝ ∞ S.chiLeft := hS.2.2.1.1
  have heq := n06_referenceGraph_canonicalWeakPairing hD hb hN03 hA href hz hs hm
    hχ hgraph U.2.1 (U.1 m) (hrep.1 m) hφ
  refine heq.trans ?_
  apply integral_congr_ae
  filter_upwards [n06ReferenceCanonicalForcing_ae (D := D) (U := U) (hrep.2 m)] with p hp
  rw [hp]

/-- Every element of the same graph used by N05 satisfies this equation;
neither a new graph domain nor a smooth forcing core is substituted. -/
theorem n06N05_positive_canonicalWeakPairing
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base b m : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    (hS : IsPhysicalSpaces D T S)
    (hN03 : N03Properties D T S C R L base ε)
    (hA : N04PartA D S C K base ε)
    (hN05 : N05Properties D T S C K V b B)
    (href : referenceStateConditions D S C)
    (hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S C.referenceState) (u : B.Space) (hm : K.positive m = true)
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, u.val.1.1 m p * canonicalOperator S K L (C.referenceState, 0) m φ p
      ∂canonicalMeasure S K m) =
      ∫ p, n06ReferenceCanonicalForcing D S C K u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) m p * φ p ∂canonicalMeasure S K m := by
  have hgraph := hN05.2.2.2.2.2.2.1
  exact n06_referenceCanonicalRelation_positive_weak hD hb hS hN03 hA href hz hs hm
    ((hgraph u.val).mp u.property) hφ

end ContinuousFlexibility.Analysis
