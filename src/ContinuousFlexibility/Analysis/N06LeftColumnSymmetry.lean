module

public import ContinuousFlexibility.Analysis.N06LeftColumnPhysical
public import ContinuousFlexibility.Analysis.N06NuPhysicalSmooth
public import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Symmetries of the actual corrected left column

The original two flux coefficients inherit the period of the actual
height. N03 supplies the reflection signs of the corrected coefficients.
The cutoff fluxes are smooth and vanish outside the original annulus,
so their actual partial derivatives retain the required even symmetry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n06_polarLinearAB_periodic (w : ℝ → ℝ) {u : PolarPoint → ℝ} {t : ℝ}
    (hu : Function.Periodic u (0, t)) :
    Function.Periodic (polarLinearA w u) (0, t) ∧
      Function.Periodic (polarLinearB w u) (0, t) := by
  have hk : Function.Periodic (heightRadial u) (0, t) := periodic_radialPartial hu
  have hp : Function.Periodic (heightAngular u) (0, t) := by
    intro p
    simp only [heightAngular, periodic_angularPartial hu p, Prod.fst_add, add_zero]
  have hpr := periodic_radialPartial hp
  have hpt := periodic_angularPartial hp
  have hscale : Function.Periodic (polarScale w u) (0, t) := by
    intro p
    simp only [polarScale, polarDiscriminant, profileEnergy, Prod.fst_add, add_zero,
      hk p, hp p]
  constructor <;> intro p <;>
    simp only [polarLinearA, polarLinearB, profileEnergy, Prod.fst_add, add_zero,
      hk p, hpr p, hpt p, hscale p]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

theorem n06_stateHeight_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  have hu := n06_stateU_periodic hS z.1
  intro p
  simp only [stateHeight, Prod.fst_add, add_zero, hu p]

theorem n06_originalCoefficients_ab_periodic (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (originalCoefficients D S C z).a (0, Real.pi) ∧
      Function.Periodic (originalCoefficients D S C z).b (0, Real.pi) :=
  n06_polarLinearAB_periodic (stateProfile D S C z.1) (n06_stateHeight_periodic hS z)

theorem n06_currentLeftColumn_periodic
    (hS : IsPhysicalSpaces D T S) (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    Function.Periodic (n06CurrentLeftColumn S L z) (0, Real.pi) := by
  have hχ : ContDiff ℝ ∞ S.chiLeft := hS.2.2.1.1
  have hχper : Function.Periodic (fun p : PolarPoint => deriv S.chiLeft p.1)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  have hcoef := n06_originalCoefficients_ab_periodic (C := C) hS z
  have hperiod := (periodic_radialPartial (hcoef.1.mul hχper)).add
    (periodic_angularPartial (hcoef.2.mul hχper))
  have he (p : PolarPoint) : n06CurrentLeftColumn S L z p =
      radialPartial (fun q => (originalCoefficients D S C z).a q * deriv S.chiLeft q.1) p +
      angularPartial (fun q => (originalCoefficients D S C z).b q * deriv S.chiLeft q.1) p :=
    (n06_currentLeftColumn_eq_original hS h03 hz hs p).trans
      (n06_divergence_radial_cutoff_flux (originalCoefficients D S C z) hχ p)
  intro p
  exact (he (p + (0, Real.pi))).trans ((hperiod p).trans (he p).symm)

theorem n06_currentLeftFluxes_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) :
    ContDiff ℝ ∞ (fun p => (L.coefficients z).a p * deriv S.chiLeft p.1) ∧
      ContDiff ℝ ∞ (fun p => (L.coefficients z).b p * deriv S.chiLeft p.1) := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, hJ, hJD, hpos, hzero⟩ := hχ.2.2
  have hreg (p : PolarPoint) (hp : p.1 ∈ J) :=
    n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs
      (p := p) ⟨hJD hp, mem_univ _⟩ (hpos p.1 hp).le
  exact ⟨n06_cutoff_flux_contDiff _ hχ.1 hJ.isClosed hzero (fun p hp => (hreg p hp).1),
    n06_cutoff_flux_contDiff _ hχ.1 hJ.isClosed hzero (fun p hp => (hreg p hp).2.1)⟩

theorem n06_currentLeftColumn_even
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (p : PolarPoint) :
    n06CurrentLeftColumn S L z (p.1, -p.2) = n06CurrentLeftColumn S L z p := by
  have hχ : CutoffConditions D S.chiLeft := hS.2.2.1
  obtain ⟨J, _hJ, hJD, _hpos, hzero⟩ := hχ.2.2
  have hflux := n06_currentLeftFluxes_contDiff hT hS h01 h03 hz hs
  have houtside (a : PolarPoint → ℝ) (q : PolarPoint) (hq : q ∉ annularOpen D) :
      a q * deriv S.chiLeft q.1 = 0 := by
    have hnot : q.1 ∉ J := fun hqJ => hq ⟨hJD hqJ, mem_univ _⟩
    simp only [hzero q.1 hnot, mul_zero]
  have heven : ∀ r θ, (L.coefficients z).a (r, -θ) * deriv S.chiLeft r =
      (L.coefficients z).a (r, θ) * deriv S.chiLeft r := by
    intro r θ
    exact congrArg (fun x : ℝ => x * deriv S.chiLeft r)
      (h03.2.2.2.1 z hz hs r θ).1
  have hodd : ∀ r θ, (L.coefficients z).b (r, -θ) * deriv S.chiLeft r =
      (-1 : ℝ) * ((L.coefficients z).b (r, θ) * deriv S.chiLeft r) := by
    intro r θ
    exact (congrArg (fun x : ℝ => x * deriv S.chiLeft r)
      (h03.2.2.2.1 z hz hs r θ).2.1).trans (by ring)
  have hrad := scalar_radialPartial_even (D := D) hflux.1.contDiffOn heven
    (houtside (L.coefficients z).a) p.1 p.2
  have hang : angularPartial (fun q => (L.coefficients z).b q * deriv S.chiLeft q.1)
      (p.1, -p.2) =
      angularPartial (fun q => (L.coefficients z).b q * deriv S.chiLeft q.1) p := by
    simpa only [neg_neg, one_mul] using
      scalar_angularPartial_reflection (D := D) (σ := -1) hflux.2.contDiffOn hodd
        (houtside (L.coefficients z).b) p.1 p.2
  exact (n06_divergence_radial_cutoff_flux (L.coefficients z) hχ.1 (p.1, -p.2)).trans
    ((congrArg₂ (fun a b : ℝ => a + b) hrad hang).trans
      (n06_divergence_radial_cutoff_flux (L.coefficients z) hχ.1 p).symm)

end ContinuousFlexibility.Statements
