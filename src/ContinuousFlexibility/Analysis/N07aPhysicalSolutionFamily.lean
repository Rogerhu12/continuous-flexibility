module

public import ContinuousFlexibility.Analysis.N07aPhysicalRemainder
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Choosing the actual physical solution as one family

Every chosen field represents the same canonical unknown. The choice is
used only before linearity is deduced from uniqueness of the real equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_exists_actualPhysicalSolutionFamily
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (hborder : RadialTrueBorder D)
    (Ω : Set (CanonicalGeometry.Parameter S))
    (hΩ : Ω ⊆ sectorNeighborhood S base ε ε)
    (U : CanonicalGeometry.Parameter S → S.Source → CanonicalUnknown S K)
    (F : CanonicalGeometry.Parameter S → S.Source → CanonicalSequence S K)
    (hrel : ∀ z ∈ Ω, ∀ f, PerturbedCanonicalRelation D S C K L
      (liftSectorParameter S C z) (U z f) (F z f))
    (hregular : ∀ z ∈ Ω, ∀ f m k, N07aCanonicalNormalRegular S K m ((U z f).1 m) k)
    (hreference : ∀ z ∈ Ω, ∀ f, N07aReferenceGraphRepresentation D S C K (U z f))
    (heven : ∀ z ∈ Ω, ∀ f m, n07aAngularReflection m ((U z f).1 m) = (U z f).1 m)
    (hsource : ∀ z ∈ Ω, ∀ f m, (F z f m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode f.val))
    (w : CanonicalGeometry.Parameter S → S.Source → ℕ → PolarPoint → ℝ)
    (hw : ∀ z (hz : z ∈ Ω) f m, w z f m =
      n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨(U z f).1 m, hregular z hz f m⟩)
    (hnormal : ∀ z ∈ Ω, ∀ f, N07aActualNormalEquation D S C L K z (U z f) f (w z f)) :
    ∃ v : CanonicalGeometry.Parameter S → S.Source → PolarPoint → ℝ,
      ∀ z ∈ Ω, ∀ f,
        ContDiffOn ℝ ∞ (v z f) (annularOpen D) ∧
        Function.Periodic (v z f) (0, Real.pi) ∧
        (∀ r θ, v z f (r, -θ) = v z f (r, θ)) ∧
        referenceRow D (v z f) = 0 ∧
        (∀ p ∈ annularOpen D,
          divergenceOperator (L.coefficients (liftSectorParameter S C z)) (v z f) p +
            (U z f).2.2.1 * nuColumnField D S C (liftSectorParameter S C z) p +
            (U z f).2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p =
              (S.height (3 / 4 : ℝ)).decode f.val p) ∧
        ∀ m, EqOn (n07aPhysicalRemainder D S (U z f).2.1 (v z f))
          (fun p => K.height (liftSectorParameter S C z) m p *
            w z f m (K.chart (liftSectorParameter S C z) m p)) (physicalPieceOpen S K (liftSectorParameter S C z) m) := by
  classical
  have hequ (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      N07aActualNormalEquation D S C L K z (U z f) f
        (fun m => n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
          ⟨(U z f).1 m, hregular z hz f m⟩) := by
    intro m
    simpa only [hw z hz f m] using hnormal z hz f m
  have hex (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :=
    n07a_perturbedCanonical_smooth_solution hD hT hS h01 h03 h04 href hcur
      hcanonical hborder z (hΩ hz)
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hΩ hz) le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) (hrel z hz f)
      (hregular z hz f) (hreference z hz f) (heven z hz f) f (hsource z hz f)
      (hequ z hz f)
  let v : CanonicalGeometry.Parameter S → S.Source → PolarPoint → ℝ :=
    fun z f => if hz : z ∈ Ω then (hex z hz f).choose else 0
  refine ⟨v, fun z hz f => ?_⟩
  have hv : v z f = (hex z hz f).choose := by simp only [v, dif_pos hz]
  have hd := (hex z hz f).choose_spec
  rw [hv]
  refine ⟨hd.1, hd.2.1, hd.2.2.1,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2, fun m => ?_⟩
  rw [hw z hz f m]
  exact n07aPhysicalRemainder_eqOn hS h04
    (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hΩ hz) le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) hd.2.2.2.2.1
    (hregular z hz f) hd.1 hd.2.1 m

end ContinuousFlexibility.Analysis
