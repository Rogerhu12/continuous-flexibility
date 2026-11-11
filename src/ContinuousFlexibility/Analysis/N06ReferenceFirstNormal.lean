import ContinuousFlexibility.Analysis.N06ReferenceNormalLp
import ContinuousFlexibility.Radial.R11bGlobalL2

/-!
# The original physical first normal estimate in actual canonical coordinates

The field selected by the original radial inverse already belongs to
physical L2: this follows from its actual output realization at a positive
exponent. The same fact applies to its weak normal derivative. Subtracting
the specified physical-space cutoff therefore gives both physical L2
inputs of the genuine normal-coordinate transport.

This module retains the original inverse, its first-normal constant and
its chosen derivative. No canonical derivative or canonical L2 membership
is supplied as an additional hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {Y h : ℝ → ℝ}

/-- The specified smooth cutoff can be subtracted before transport. Both
canonical L2 fields and their true weak derivative identity follow from
physical L2 and the primitive coordinate bounds. -/
theorem n06_reference_remainder_normal_of_bounds
    (h04 : N04Properties D T S C L K base loss ε) (hab : D.a < D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ContDiffOn ℝ ∞ h (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ p ∈ physicalPieceOpen S K m, K.chart z m p = (Y p.1, p.2))
    (hheight : ∀ p ∈ physicalPieceOpen S K m, K.height z m p = h p.1)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m),
      |h r| + |(h r)⁻¹| + |deriv h r| + |deriv Y r| + |(deriv Y r)⁻¹| ≤ B)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {η ur : PolarPoint → ℝ} (aL : ℝ)
    (hweak : WeakNormalDerivative D η ur)
    (hη : MemLp η 2 (radialPhysicalMeasure D))
    (hur : MemLp ur 2 (radialPhysicalMeasure D))
    (hηp : Function.Periodic η (0, Real.pi))
    (hurp : Function.Periodic ur (0, Real.pi)) :
    MemLp (canonicalHeight S K z m (n06ReferenceRemainder χ η aL)) 2
        (canonicalMeasure S K m) ∧
      MemLp (n06ReferenceNormalField S K z m Y h (n06ReferenceRemainder χ η aL)
        (fun p => ur p - aL * deriv χ p.1)) 2 (canonicalMeasure S K m) ∧
      ∀ φ, CanonicalTest S K m φ →
        (∫ p, n06ReferenceNormalField S K z m Y h (n06ReferenceRemainder χ η aL)
            (fun q => ur q - aL * deriv χ q.1) p * φ p ∂canonicalMeasure S K m) =
          -(∫ p, canonicalHeight S K z m (n06ReferenceRemainder χ η aL) p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
  have hK := (n06_N04_qualitative_parts h04).1
  have hχL : MemLp (fun p : PolarPoint => χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (hχ.continuous.comp continuous_fst)
  have hdχL : MemLp (fun p : PolarPoint => deriv χ p.1) 2 (radialPhysicalMeasure D) :=
    r11b_continuous_memLp
      ((contDiff_infty_iff_deriv.mp hχ).2.continuous.comp continuous_fst)
  have hremL : MemLp (n06ReferenceRemainder χ η aL) 2 (radialPhysicalMeasure D) :=
    hη.sub (hχL.const_mul aL)
  have hremrL : MemLp (fun p => ur p - aL * deriv χ p.1) 2 (radialPhysicalMeasure D) :=
    hur.sub (hdχL.const_mul aL)
  have hsub : Ioo (K.physicalLeft m) (K.physicalRight m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi) := by
    intro p hp
    exact ⟨(hK.2.2.2.1 m).2.2 hp.1, hp.2.1,
      hp.2.2.trans (by linarith [Real.pi_pos])⟩
  have hwPiece := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hremL
  have hdwPiece := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) hremrL
  obtain ⟨⟨hW, _⟩, hG, _⟩ :=
    n06_reference_height_normal_lp h04 hz hs hY hh hchart hheight hB hcoeff hwPiece hdwPiece
  exact ⟨hW, hG, n06_reference_remainder_normal_transport hK hab hz hs hY hh
    hchart hheight hχ aL hweak hη hur hηp hurp hW hG⟩

/-- The original physical inverse and its original first-normal estimate
produce the actual canonical derivative. The same selected physical
derivative works on every piece and for every left-tail coefficient,
and retains precisely the original weighted estimate. In particular `S.chiLeft` is used here,
without identifying it with the distinct `D.chiLeft`. -/
theorem n06_reference_firstNormal_transport
    (hA : IsRadialReference D)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (Y h : ℕ → ℝ → ℝ)
    (hY : ∀ m, ContDiffOn ℝ ∞ (Y m) (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hh : ∀ m, ContDiffOn ℝ ∞ (h m) (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ m p, p ∈ physicalPieceOpen S K m → K.chart z m p = (Y m p.1, p.2))
    (hheight : ∀ m p, p ∈ physicalPieceOpen S K m → K.height z m p = h m p.1)
    (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hcoeff : ∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
      |h m r| + |(h m r)⁻¹| + |deriv (h m) r| + |deriv (Y m) r| +
        |(deriv (Y m) r)⁻¹| ≤ B m)
    (hχ : ContDiff ℝ ∞ S.chiLeft)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D γ M₀ M₁ G)
    (hN : FirstNormalInverseEstimate D γ M₀ M₁ G) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ F fθ,
      SourceMember D γ M₀ F → WeakAngularDerivative D F.1 fθ →
      SourceDerivativeMember D γ M₀ fθ →
      ∃ ur : PolarPoint → ℝ,
        WeakNormalDerivative D (G F).1 ur ∧ OutputRealization D γ M₁ 0 (ur, 0) ∧
        outputNormSquare D γ M₁ 0 (ur, 0) ≤ C0 ^ 2 *
          (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (fθ, 0)) ∧
        ∀ (aL : ℝ) (m : ℕ),
          MemLp (canonicalHeight S K z m (n06ReferenceRemainder S.chiLeft (G F).1 aL)) 2
              (canonicalMeasure S K m) ∧
            MemLp (n06ReferenceNormalField S K z m (Y m) (h m)
              (n06ReferenceRemainder S.chiLeft (G F).1 aL)
              (fun p => ur p - aL * deriv S.chiLeft p.1)) 2 (canonicalMeasure S K m) ∧
            ∀ φ, CanonicalTest S K m φ →
              (∫ p, n06ReferenceNormalField S K z m (Y m) (h m)
                  (n06ReferenceRemainder S.chiLeft (G F).1 aL)
                  (fun q => ur q - aL * deriv S.chiLeft q.1) p * φ p
                    ∂canonicalMeasure S K m) =
                -(∫ p, canonicalHeight S K z m
                    (n06ReferenceRemainder S.chiLeft (G F).1 aL) p *
                    mixedDerivative 1 0 φ p ∂canonicalMeasure S K m) := by
  obtain ⟨C0, hC0, hnormal⟩ := hN
  refine ⟨C0, hC0, ?_⟩
  intro F fθ hF hfθ hθ
  obtain ⟨ur, hweak, houtput, hbound⟩ := hnormal F fθ hF hfθ hθ
  have hgraph := hG.1 F hF
  have hD : IsAccumulatingProfile D := hA.1
  have hborder : RadialTrueBorder D := hA.2.2.2.1
  have hη : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ hgraph.1
  have hur : MemLp ur 2 (radialPhysicalMeasure D) := by
    have he : outputRemainder D 0 (ur, 0) = ur := by
      funext p
      change ur p - 0 * D.chiLeft p.1 = ur p
      ring
    have hu := r11b_outputRemainder_memLp hD hγ houtput
    rw [he] at hu
    exact hu
  have hηp : Function.Periodic (G F).1 (0, Real.pi) := hgraph.1.choose_spec.2.2.1
  have hurp : Function.Periodic ur (0, Real.pi) := houtput.2.2.1
  refine ⟨ur, hweak, houtput, hbound, ?_⟩
  intro aL m
  exact n06_reference_remainder_normal_of_bounds h04 hD.choose_spec.1.2.1 hz hs
    (hY m) (hh m) (hchart m) (hheight m) (hB m) (hcoeff m) hχ aL hweak hη hur hηp hurp

end ContinuousFlexibility.Analysis
