module

public import ContinuousFlexibility.Analysis.N07aCurrentCanonicalEquation
public import ContinuousFlexibility.Analysis.N07aReferenceOperatorIdentity
public import ContinuousFlexibility.Analysis.N07aCanonicalCoefficientDifference

/-!
# Exact local identification of the actual relative operator

Subtracting the two proved canonical equations identifies `P.relative`
with the principal difference and the actual potential and scalar-column
differences. The compatibility column retains its current transformation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

def n07aCanonicalLowerDifference {m : ℕ}
    (q q₀ : N07aCanonicalOpenCoefficient S K m)
    (col col₀ : Fin 3 → N07aCanonicalOpenCoefficient S K m)
    (U : CanonicalUnknown S K) : CanonicalL2 S K m :=
  (q.sub q₀).mul (U.1 m) + U.2.1 • ((col 0).sub (col₀ 0)).toLp +
    U.2.2.1 • ((col 1).sub (col₀ 1)).toLp +
    U.2.2.2 • ((col 2).sub (col₀ 2)).toLp

def n07aRelativeCanonicalLower
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (U : CanonicalUnknown S K) : CanonicalL2 S K m :=
  n07aCanonicalLowerDifference
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aCurrentOpenCoefficient href hcur z hz m hm 4))
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient href m hm 4))
    (n07aCurrentScalarOpenCoefficient href hcur z hz m hm)
    (n07aReferenceScalarOpenCoefficient href m hm) U

theorem n07a_relativeCanonical_pairing
    (hab : D.a ≤ D.b) (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) (hm : K.left m < K.right m)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    (∫ p, V.forget (3 / 4 : ℝ) 0 b (P.relative (liftSectorParameter S C z) F) m p * W p
      ∂canonicalMeasure S K m) =
      (∫ p, (B.inverse F).val.1.1 m p *
        (divergenceOperator (K.coefficients (liftSectorParameter S C z) m) W p -
          divergenceOperator (K.coefficients (C.referenceState, 0) m) W p)
          ∂canonicalMeasure S K m) +
      ∫ p, n07aRelativeCanonicalLower href hcur z hz m hm (B.inverse F).val.1 p * W p
        ∂canonicalMeasure S K m := by
  let u := B.inverse F
  let z' := liftSectorParameter S C z
  let Fz := V.forget (3 / 4 : ℝ) 0 b (P.operator z' u)
  let F₀ := V.forget (3 / 4 : ℝ) 0 b F
  let Δ := n07aRelativeCanonicalLower href hcur z hz m hm u.val.1
  have hcurr := n07a_currentOperator_distribution hab hS h01.2.2.1 h04 href hcur h06
    z hz m hm u W hW
  have hrefeq := n07a_referenceDomain_distribution hab hS hT h01 h02 h03 h04 href
    h05 h06 u m hm W hW
  have husource : u.val.2 = F := h05.2.2.2.2.2.2.2.1 F
  rw [husource] at hrefeq
  have hrelative : V.forget (3 / 4 : ℝ) 0 b (P.relative z' F) m = Fz m - F₀ m := by
    rw [(h06.2 z' (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z)).2.1 F, map_sub, Pi.sub_apply]
  have hrhs : n07aCurrentCanonicalRhs href hcur z hz m hm u.val.1 Fz -
      n07aReferenceCanonicalRhs href m hm u.val.1 F₀ =
      V.forget (3 / 4 : ℝ) 0 b (P.relative z' F) m - Δ := by
    rw [hrelative]
    simp only [n07aCurrentCanonicalRhs, n07aReferenceCanonicalRhs, Δ,
      n07aRelativeCanonicalLower, n07aCanonicalLowerDifference,
      N07aCanonicalOpenCoefficient.sub_mul, N07aCanonicalOpenCoefficient.sub_toLp, smul_sub]
    abel
  have htest := n07a_canonicalTest_memLp hW
  have hpair :
      (∫ p, V.forget (3 / 4 : ℝ) 0 b (P.relative z' F) m p * W p ∂canonicalMeasure S K m) -
        (∫ p, Δ p * W p ∂canonicalMeasure S K m) =
      (∫ p, u.val.1.1 m p * divergenceOperator (K.coefficients z' m) W p
        ∂canonicalMeasure S K m) -
      (∫ p, u.val.1.1 m p * divergenceOperator (K.coefficients (C.referenceState, 0) m) W p
        ∂canonicalMeasure S K m) := by
    have he := congrArg (n07aCanonicalTestPairing W htest) hrhs
    simp only [map_sub, n07aCanonicalTestPairing_apply] at he
    exact he.symm.trans (congrArg₂ (· - ·) hcurr.symm hrefeq.symm)
  let a := n07aCurrentOpenCoefficient href hcur z hz m hm 0
  let d := n07aCurrentOpenCoefficient href hcur z hz m hm 1
  let c := n07aCurrentOpenCoefficient href hcur z hz m hm 2
  let a₀ := n07aReferenceOpenCoefficient href m hm 0
  let d₀ := n07aReferenceOpenCoefficient href m hm 1
  let c₀ := n07aReferenceOpenCoefficient href m hm 2
  have hdiv := n07a_canonicalTest_divergence (K.coefficients z' m)
    a.smooth d.smooth c.smooth a.periodic d.periodic c.periodic hW
  have hdiv₀ := n07a_canonicalTest_divergence (K.coefficients (C.referenceState, 0) m)
    a₀.smooth d₀.smooth c₀.smooth a₀.periodic d₀.periodic c₀.periodic hW
  have hi : Integrable (fun p => u.val.1.1 m p * divergenceOperator (K.coefficients z' m) W p)
      (canonicalMeasure S K m) := (Lp.memLp (u.val.1.1 m)).integrable_mul
    (n07a_canonicalTest_memLp hdiv)
  have hi₀ : Integrable (fun p => u.val.1.1 m p *
      divergenceOperator (K.coefficients (C.referenceState, 0) m) W p)
      (canonicalMeasure S K m) := (Lp.memLp (u.val.1.1 m)).integrable_mul
    (n07a_canonicalTest_memLp hdiv₀)
  have he : (∫ p, u.val.1.1 m p *
      (divergenceOperator (K.coefficients z' m) W p -
        divergenceOperator (K.coefficients (C.referenceState, 0) m) W p)
        ∂canonicalMeasure S K m) =
      (∫ p, u.val.1.1 m p * divergenceOperator (K.coefficients z' m) W p
        ∂canonicalMeasure S K m) -
      ∫ p, u.val.1.1 m p * divergenceOperator (K.coefficients (C.referenceState, 0) m) W p
        ∂canonicalMeasure S K m := by
    simp only [mul_sub]
    exact integral_sub hi hi₀
  rw [he]
  linarith only [hpair]

end ContinuousFlexibility.Analysis
