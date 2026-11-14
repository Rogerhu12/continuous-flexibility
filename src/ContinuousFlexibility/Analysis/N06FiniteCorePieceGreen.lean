module

public import ContinuousFlexibility.Analysis.N06OriginalPositiveGraphFamily
public import ContinuousFlexibility.Analysis.N06PositiveFiniteCoreGreen
public import ContinuousFlexibility.Analysis.N06NegativeFiniteCoreGreen
public import ContinuousFlexibility.Analysis.N06FiniteHeightModes

/-!
# One actual finite modal family for every canonical piece

For an element of the original finite angular graph core, the original
N05 inverse supplies the positive graph family and the negative weak
mode representatives. Choosing those families once and recovering their
actual Fourier coefficients gives one common finite set on all pieces.

The literal relative source satisfies both signed local Green formulas
for these same finite C1 values. The result retains the modal coefficient
identities needed by the existing reference/current transmission proofs;
no matching trace or global physical equation is imposed here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Actual all-piece modal selection and local Green formulas for the
same finite core element. The remaining endpoint geometry can be applied
to the displayed modes and their true coefficient identities. -/
theorem n06N05_finiteCore_pieceGreen
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {Vol : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
    {B : CanonicalDomainData S K Vol b} {z : AnnularState S × ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K Vol b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (a c pot q : ℕ → ℝ → ℝ) (κ : ℕ → ℝ) (Cref : ℝ)
    (hgeometry : N06PositiveUnitGeometry T K a c pot q κ Cref)
    (hea : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a m p.1) (canonicalOpen S K m))
    (heb : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hec : ∀ m, K.positive m = true → EqOn (K.coefficients (C.referenceState, 0) m).c
      (fun p => c m p.1) (canonicalOpen S K m))
    (hepot : ∀ m, K.positive m = true → EqOn (K.potential (C.referenceState, 0) m)
      (fun p => pot m p.1) (canonicalOpen S K m))
    (hcd : ∀ m, K.positive m = true → ∀ y ∈ Ioo (K.left m) (K.right m),
      DifferentiableAt ℝ (c m) y)
    {scale : ℕ → ℝ} {δ : ℝ}
    (hcoeff : N06PositiveCubicControl K b scale δ
      (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
      (fun n => (K.dividedDifference z n).c))
    (u : B.Space) (hu : u ∈ n06CanonicalGraphFiniteAngularCore B)
    (G Fcur : CanonicalSequence S K)
    (hsource : ∀ m, (Fcur m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      n06CurrentRelativeSourceField D S C L K z u.val.1
        (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) G m)
    (hweak : ∀ m ψ, CanonicalTest S K m ψ →
      (∫ p, G m p * ψ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * n06PositiveCubicTestOperator K
          (fun n => (K.dividedDifference z n).a) (fun n => (K.dividedDifference z n).b)
          (fun n => (K.dividedDifference z n).c) m ψ p ∂canonicalMeasure S K m) :
    ∃ s : Finset ℕ, ∃ v : ℕ → ℕ → ℝ → ℝ,
      (∀ m i, ContDiff ℝ 1 (v m i)) ∧
      (∀ m i, n06HalfCosineCoefficient (u.val.1.1 m) i
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m i) ∧
      (∀ m, (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis s (v m) referenceAngularBasis) ∧
      (∀ m, ContDiff ℝ 1 (r11bFiniteSynthesis s (v m) referenceAngularBasis)) ∧
      ∀ φ, RadialTest D φ →
        ∀ Q : ∀ m, N06CurrentHeightTestTraces S K z m (n06_radialTestAverage φ),
          ∀ m,
            (∫ p, n06CurrentRemainderSource D S C L K z u.val.1 Fcur m p *
              canonicalHeight S K z m (n06_radialTestAverage φ) p ∂canonicalMeasure S K m) -
            (∫ p, r11bFiniteSynthesis s (v m) referenceAngularBasis p * canonicalSource S K z m
              (n06_radialTestAverage (divergenceOperator (L.coefficients z) φ)) p
                ∂canonicalMeasure S K m) =
            ∫ θ in (0 : ℝ)..Real.pi,
              (if K.positive m = true then a m (K.right m) else 1) *
                ((Q m).value (K.right m, θ) *
                    radialPartial (r11bFiniteSynthesis s (v m) referenceAngularBasis) (K.right m, θ) -
                  r11bFiniteSynthesis s (v m) referenceAngularBasis (K.right m, θ) *
                    (Q m).radial (K.right m, θ)) -
              (if K.positive m = true then a m (K.left m) else 1) *
                ((Q m).value (K.left m, θ) *
                    radialPartial (r11bFiniteSynthesis s (v m) referenceAngularBasis) (K.left m, θ) -
                  r11bFiniteSynthesis s (v m) referenceAngularBasis (K.left m, θ) *
                    (Q m).radial (K.left m, θ)) := by
  classical
  obtain ⟨F, W, Ppos, hheight, hforcing⟩ := n06N05_exists_original_positiveGraphFamily
    hT hS h hcoordinates a c pot q κ Cref hgeometry hea heb hec hepot hcd u
  have hex (m : ℕ) (hm : K.positive m = false) :
      ∃ Gn : CanonicalL2 S K m,
        (Gn : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          n06NegativePrincipalForcing D S C K u.val.1
            (Vol.forget (3 / 4 : ℝ) 0 b u.val.2) m ∧
        Nonempty (N06NegativeGraphApproximation (u.val.1.1 m) Gn) :=
    n06N05_negative_graphApproximation hT hS h u m hm
  choose Gn hGn hPn using hex
  let Pneg (m : ℕ) (hm : K.positive m = false) :
      N06NegativeGraphApproximation (u.val.1.1 m) (Gn m hm) := Classical.choice (hPn m hm)
  let v (m : ℕ) : ℕ → ℝ → ℝ :=
    if hm : K.positive m = true then (Ppos m hm).modes
    else (Pneg m (Bool.eq_false_of_not_eq_true hm)).modes
  have hregular (m i : ℕ) : ContDiff ℝ 1 (v m i) := by
    by_cases hm : K.positive m = true
    · simpa only [v, dif_pos hm] using ((Ppos m hm).representative i).contDiffOne
    · simpa only [v, dif_neg hm] using
        (Pneg m (Bool.eq_false_of_not_eq_true hm)).contDiff i
  have hmode (m i : ℕ) : n06HalfCosineCoefficient (u.val.1.1 m) i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v m i := by
    by_cases hm : K.positive m = true
    · have he := ((Ppos m hm).representative i).ae_eq
      rw [hheight m] at he
      simpa only [hgeometry.left m hm, hgeometry.right m hm, v, dif_pos hm] using he
    · simpa only [v, dif_neg hm] using
        (Pneg m (Bool.eq_false_of_not_eq_true hm)).coefficient i
  obtain ⟨s, hvalue⟩ := n06CanonicalGraphFiniteAngularCore_actual_modes u hu v hmode
  refine ⟨s, v, hregular, hmode, hvalue, ?_, ?_⟩
  · intro m
    exact n06_contDiff_one_finiteSynthesis s (v m) referenceAngularBasis
      (fun i _ => hregular m i)
      (fun i _ => (contDiff_referenceAngularBasis i).of_le (by simp))
  · intro φ hφ Q m
    by_cases hm : K.positive m = true
    · have hv : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          r11bFiniteSynthesis s (Ppos m hm).modes referenceAngularBasis := by
        simpa only [v, dif_pos hm] using hvalue m
      have he := n06N05_positive_finite_relative_green hT hS h hz hs u hm
        (Ppos m hm) (hheight m) (hforcing m) (hgeometry.left m hm) (hgeometry.right m hm)
        (hgeometry.a_smooth m hm) (hgeometry.c_continuous m hm)
        (hgeometry.potential_continuous m hm) (hcd m hm)
        (hea m hm) (heb m hm) (hec m hm) (hepot m hm) hcoeff s hv G Fcur
        (hsource m) (hweak m) hφ (Q m)
      simpa only [v, dif_pos hm, if_pos hm] using he
    · have hn : K.positive m = false := Bool.eq_false_of_not_eq_true hm
      have hv : (u.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
          r11bFiniteSynthesis s (Pneg m hn).modes referenceAngularBasis := by
        simpa only [v, dif_neg hm] using hvalue m
      have he := n06N05_negative_finite_relative_green hT hS h hz hs u m hn
        (Pneg m hn) (hGn m hn) s hv G Fcur (hsource m) (hweak m) hφ (Q m)
      simpa only [v, dif_neg hm, if_neg hm, one_mul] using he

end ContinuousFlexibility.Analysis
