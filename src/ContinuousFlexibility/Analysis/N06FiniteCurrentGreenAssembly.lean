import ContinuousFlexibility.Analysis.N06FiniteCurrentBoundaryGluing
import ContinuousFlexibility.Analysis.N06CurrentResidualPairing

/-!
# Finite current Green gluing in the original physical equation

The local positive and negative Green formulas both have the displayed
canonical right-minus-left form. Their finite fields represent the same
original canonical unknown almost everywhere. Actual endpoint jets and
the explicit two-sided density identities cancel the boundary sum on the
original atlas; no global PDE or zero-total-boundary hypothesis is used.

After the genuine full-period change of variables, only the separately
identified left-cutoff scalar Green defect remains. This construction
works for finite H2 modal fields and requires only C1 regularity of their
value representatives at the boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

/-- Exact replacement of a finite value representative in the local
Green formula. This is an AE integral identity, not a boundary rewrite. -/
theorem n06_current_pieceGreen_of_representative
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K) (m : ℕ)
    (Q : N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (W : PolarPoint → ℝ) (a : ℝ → ℝ) (reverse : Bool)
    (hW : ContDiff ℝ 1 W)
    (hvalue : (u.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] W)
    (hgreen :
      (∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, W p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.right m) * (Q.value (K.right m, θ) * radialPartial W (K.right m, θ) -
          W (K.right m, θ) * Q.radial (K.right m, θ)) -
        a (K.left m) * (Q.value (K.left m, θ) * radialPartial W (K.left m, θ) -
          W (K.left m, θ) * Q.radial (K.left m, θ))) :
    (∫ p, n06CurrentRemainderSource D S C L K z u F m p *
      canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
    (∫ p, u.1 m p * canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
        ∂canonicalMeasure S K m) =
      (∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse true θ) -
      ∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse false θ := by
  have he : (∫ p, u.1 m p * canonicalSource S K z m
      (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
        ∂canonicalMeasure S K m) =
      ∫ p, W p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [hvalue] with p hp
    rw [hp]
  rw [he, hgreen]
  exact (n06_orientedCanonicalBoundary_difference Q a hW reverse).symm

/-- The actual finite local Green formulas and actual matching normal
rows give the full physical equation up to its explicit affine cutoff
defect. All outer terms vanish by the same original test support. -/
theorem n06_current_finiteGreen_assembly
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CanonicalUnknown S K) (F : CanonicalSequence S K)
    (hφ : RadialTest D φ)
    (Q : ∀ m, N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ))
    (W : ℕ → PolarPoint → ℝ) (a : ℕ → ℝ → ℝ) (reverse : ℕ → Bool)
    (hW : ∀ m, ContDiff ℝ 1 (W m))
    (hvalue : ∀ m, (u.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] W m)
    (hends : ∀ m, ∀ side : Bool, ∃ σ : ℝ, ∃ β H ρ κ Hr : ℝ → ℝ,
      Nonempty (N06RootFirstJets (K.chart z m) (K.height z m)
        (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side)
        (n06Endpoint (K.left m) (K.right m) (if reverse m then !side else side))
          σ β H ρ κ Hr))
    (hgreen : ∀ m,
      (∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      (∫ p, W m p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a m (K.right m) * ((Q m).value (K.right m, θ) * radialPartial (W m) (K.right m, θ) -
          W m (K.right m, θ) * (Q m).radial (K.right m, θ)) -
        a m (K.left m) * ((Q m).value (K.left m, θ) * radialPartial (W m) (K.left m, θ) -
          W m (K.left m, θ) * (Q m).radial (K.left m, θ)))
    (hmatch : ∀ i j, K.physicalRight i = K.physicalLeft j →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        n06OrientedCanonicalBoundary (Q i) (W i) (a i) (reverse i) true θ =
          n06OrientedCanonicalBoundary (Q j) (W j) (a j) (reverse j) false θ) :
    ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalHeight K z (fun m => (u.1 m : PolarPoint → ℝ)) u.2.1 (r, θ) *
        divergenceOperator (L.coefficients z) φ (r, θ))) +
      u.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        nuColumnField D S C z (r, θ) * φ (r, θ))) +
      u.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) -
      (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (F m : PolarPoint → ℝ)) (r, θ) * φ (r, θ)))) =
      u.2.1 * ((∫ r in D.a..D.b, radialAngularMean (fun θ =>
        S.chiLeft r * divergenceOperator (L.coefficients z) φ (r, θ))) -
        ∫ r in D.a..D.b, radialAngularMean (fun θ =>
          n06CurrentLeftColumn S L z (r, θ) * φ (r, θ))) := by
  obtain ⟨J, l, r, hJ, _hlr, hJwindow, hwindow, hsupport⟩ :=
    n06_radialTest_supportWindow h01.1.1 hφ
  obtain ⟨hfinite, hboundary⟩ := n06_current_finiteAtlas_boundary_sum h01.1.1 hcoords h04 hz hs
    hJ.isClosed hJwindow hwindow (n06_average_radial_support hsupport) Q W a reverse hends hmatch
  have hzero : (∑ m ∈ hfinite.toFinset,
      ((∫ p, n06CurrentRemainderSource D S C L K z u F m p *
        canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
      ∫ p, u.1 m p * canonicalSource S K z m
        (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
          ∂canonicalMeasure S K m)) = 0 := by
    refine (Finset.sum_congr rfl (fun m _ =>
      n06_current_pieceGreen_of_representative u F m (Q m) (W m) (a m) (reverse m)
        (hW m) (hvalue m) (hgreen m))).trans hboundary
  have hsupportWindow : ∀ x, x ∉ Icc l r → ∀ θ, φ (x, θ) = 0 := by
    intro x hx θ
    exact hsupport x (fun hxJ => hx (Ioo_subset_Icc_self (hJwindow hxJ))) θ
  rw [n06_current_physicalResidual_eq_finiteGreen hT hS h01 h03 h04 hz hs u F
    isClosed_Icc hfinite hφ hsupportWindow, hzero, mul_zero, zero_add]

end ContinuousFlexibility.Statements
