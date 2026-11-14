module

public import ContinuousFlexibility.Analysis.N06PhysicalHeightAffinePairing
public import ContinuousFlexibility.Analysis.N06LeftColumnSymmetry
public import ContinuousFlexibility.Analysis.N06NuPhysicalRegularity

/-!
# The three actual current columns in finite canonical pairings

The current left-cutoff, nu and compatibility columns are kept as their
literal physical functions. Their regularity and half-periodicity follow
from the original contracts. The same current change of variables then
converts their full-period pairings to the finite atlas sum.

Subtracting these three actual columns from an arbitrary original source
gives the precise remainder source used by the positive and negative
Green identities. All integrability is proved in the original canonical
L2 spaces before the sums or integrals are split.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- These are the original three scalar columns at the current state. -/
def n06CurrentScalarField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) : Fin 3 → PolarPoint → ℝ :=
  ![n06CurrentLeftColumn S L z, nuColumnField D S C z,
    (S.height (3 / 4 : ℝ)).decode S.psi]

theorem n06_currentScalarField_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (i : Fin 3) :
    ContDiff ℝ ∞ (n06CurrentScalarField D S C L z i) := by
  fin_cases i
  · exact n06_currentLeftColumn_contDiff hT hS h01 h03 hz hs
  · exact n06_nuColumn_contDiff hT hS h01 hz hs
  · exact (physical_height_contDiff_and_flatJets hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) S.psi).1

theorem n06_currentScalarField_periodic
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (i : Fin 3) :
    Function.Periodic (n06CurrentScalarField D S C L z i) (0, Real.pi) := by
  fin_cases i
  · exact n06_currentLeftColumn_periodic hS h03 hz hs
  · exact n06_nuColumn_periodic hT hS h01 z
  · exact ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.2.1

theorem n06_currentScalarSource_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (i : Fin 3) (m : ℕ) :
    MemLp (canonicalSource S K z m (n06CurrentScalarField D S C L z i))
      2 (canonicalMeasure S K m) :=
  n06_current_canonicalSource_memLp h04 hz hs m
    (n06_currentScalarField_contDiff hT hS h01 h03 hz hs i).continuous.continuousOn

/-- The normalization is exactly the original full angular mean, hence
the factor pi inverse in front of the unnormalized canonical half tile. -/
theorem n06_currentScalarField_full_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ)
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) (i : Fin 3) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06CurrentScalarField D S C L z i (r, θ) * φ (r, θ))) =
      Real.pi⁻¹ * ∑ m ∈ hfinite.toFinset,
        ∫ p, canonicalSource S K z m (n06CurrentScalarField D S C L z i) p *
          canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m := by
  let F : CanonicalSequence S K := fun m =>
    (n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs i m).toLp
      (canonicalSource S K z m (n06CurrentScalarField D S C L z i))
  have hrep (m : ℕ) : (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m (n06CurrentScalarField D S C L z i) :=
    (n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs i m).coeFn_toLp
  have hφshift : ContDiff ℝ ∞ (fun p : PolarPoint => φ (p + (0, Real.pi))) :=
    hφ.1.comp (contDiff_id.add contDiff_const)
  have hp := n06_fullCanonical_source_pairing h01.1.1.choose_spec.1.2.1.le h04 hz hs
    hfinite F hrep (n06_currentScalarField_periodic hT hS h01 h03 hz hs i)
    (fun m => n06_current_canonicalHeight_memLp h04 hz hs m hφ.1.continuous.continuousOn)
    (fun m => n06_current_canonicalHeight_memLp h04 hz hs m hφshift.continuous.continuousOn)
    hsupport
  refine hp.trans (congrArg (fun t : ℝ => Real.pi⁻¹ * t) ?_)
  apply Finset.sum_congr rfl
  intro m _
  apply integral_congr_ae
  filter_upwards [hrep m] with p he
  rw [he]

/-- The literal current remainder source after removing exactly the
three original scalar columns. Its sign agrees with physical divergence. -/
def n06CurrentRemainderSource (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (u : CanonicalUnknown S K) (F : CanonicalSequence S K)
    (m : ℕ) (p : PolarPoint) : ℝ :=
  F m p - u.2.1 * canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p -
    u.2.2.1 * canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p -
    u.2.2.2 * canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p

theorem n06_currentRemainderSource_memLp
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ) :
    MemLp (n06CurrentRemainderSource D S C L K z u F m) 2 (canonicalMeasure S K m) := by
  have he : n06CurrentRemainderSource D S C L K z u F m =
      (((F m : PolarPoint → ℝ) -
        (fun p => u.2.1 * canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p)) -
        (fun p => u.2.2.1 * canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p)) -
        (fun p => u.2.2.2 * canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p) := by
    funext p
    simp only [n06CurrentRemainderSource, Pi.sub_apply]
  rw [he]
  exact
    (((Lp.memLp (F m)).sub
      ((n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs 0 m).const_mul u.2.1)).sub
      ((n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs 1 m).const_mul u.2.2.1)).sub
      ((n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs 2 m).const_mul u.2.2.2)

/-- Splitting the exact remainder inside a single original canonical
L2 pairing is legitimate for any genuine L2 test. -/
theorem n06_currentRemainderSource_pairing
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ)
    {ψ : PolarPoint → ℝ} (hψ : MemLp ψ 2 (canonicalMeasure S K m)) :
    (∫ p, n06CurrentRemainderSource D S C L K z u F m p * ψ p ∂canonicalMeasure S K m) =
      (∫ p, F m p * ψ p ∂canonicalMeasure S K m) -
      u.2.1 * (∫ p, canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p * ψ p
        ∂canonicalMeasure S K m) -
      u.2.2.1 * (∫ p, canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p * ψ p
        ∂canonicalMeasure S K m) -
      u.2.2.2 * (∫ p, canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p * ψ p
        ∂canonicalMeasure S K m) := by
  have hF : Integrable (fun p => F m p * ψ p) (canonicalMeasure S K m) :=
    (Lp.memLp (F m)).integrable_mul hψ
  have hc (i : Fin 3) : Integrable (fun p =>
      canonicalSource S K z m (n06CurrentScalarField D S C L z i) p * ψ p)
        (canonicalMeasure S K m) :=
    (n06_currentScalarSource_memLp hT hS h01 h03 h04 hz hs i m).integrable_mul hψ
  have h₀ : Integrable (fun p => u.2.1 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p * ψ p))
        (canonicalMeasure S K m) := (hc 0).const_mul u.2.1
  have h₁ : Integrable (fun p => u.2.2.1 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p * ψ p))
        (canonicalMeasure S K m) := (hc 1).const_mul u.2.2.1
  have h₂ : Integrable (fun p => u.2.2.2 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p * ψ p))
        (canonicalMeasure S K m) := (hc 2).const_mul u.2.2.2
  have hF₀ : Integrable (fun p => F m p * ψ p - u.2.1 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p * ψ p))
        (canonicalMeasure S K m) := hF.sub h₀
  have hF₁ : Integrable (fun p => F m p * ψ p - u.2.1 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p * ψ p) - u.2.2.1 *
      (canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p * ψ p))
        (canonicalMeasure S K m) := hF₀.sub h₁
  have he : (fun p => n06CurrentRemainderSource D S C L K z u F m p * ψ p) =
      (fun p => F m p * ψ p -
        u.2.1 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 0) p * ψ p) -
        u.2.2.1 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 1) p * ψ p) -
        u.2.2.2 * (canonicalSource S K z m (n06CurrentScalarField D S C L z 2) p * ψ p)) := by
    funext p
    simp only [n06CurrentRemainderSource]
    ring
  rw [he, integral_sub hF₁ h₂, integral_sub hF₀ h₁, integral_sub hF h₀]
  simp only [integral_const_mul]

end ContinuousFlexibility.Statements
