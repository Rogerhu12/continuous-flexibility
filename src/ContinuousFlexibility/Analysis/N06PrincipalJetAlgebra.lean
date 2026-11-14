module

public import ContinuousFlexibility.Statements.N06PrimitiveGeometryBridge
public import ContinuousFlexibility.Analysis.N07aOpenDivergenceExpansion
public import ContinuousFlexibility.Analysis.N07aCanonicalCoefficientDifference
public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients

/-!
# Actual principal jet algebra before constructing a relative inverse

This is the pure weak-jet prefix of upstream N07aRelativeExpanded at
b4270fe18a9f5461b4593084da1cf11975701b5c.  The actual multiplier and all
identities retain their upstream names.  The N06Properties-dependent
operator identification is deliberately a later client of this algebra.
When the upstream module is integrated, these declarations must have one
owner and that module can import this compatibility layer.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem N07aCanonicalOpenCoefficient.jet_sub_mul
    (a a₀ : N07aCanonicalOpenCoefficient S K m) (i j : ℕ) (u : CanonicalL2 S K m) :
    ((a.sub a₀).jet i j).mul u = (a.jet i j).mul u - (a₀.jet i j).mul u := by
  apply Lp.ext
  filter_upwards [((a.sub a₀).jet i j).mul_ae u, (a.jet i j).mul_ae u,
    (a₀.jet i j).mul_ae u, Lp.coeFn_sub ((a.jet i j).mul u) ((a₀.jet i j).mul u),
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p h₁ h₂ h₃ h₄ hp
  rw [h₁, h₄, Pi.sub_apply, h₂, h₃]
  change mixedDerivative i j (fun q => a.value q - a₀.value q) p * u p = _
  have he : (fun q => a.value q - a₀.value q) =
      fun q => a.value q + (-1 : ℝ) * a₀.value q := by funext q; ring
  rw [he, n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    a.smooth (contDiffOn_const.mul a₀.smooth) i j hp,
    spaces_mixedDerivative_const_mul]
  change (mixedDerivative i j a.value p + (-1 : ℝ) * mixedDerivative i j a₀.value p) * u p =
    mixedDerivative i j a.value p * u p - mixedDerivative i j a₀.value p * u p
  ring

theorem n07aOpenDivergence_sub
    (a b c a₀ b₀ c₀ : N07aCanonicalOpenCoefficient S K m)
    (ur uθ urr urθ uθθ : CanonicalL2 S K m) :
    n07aOpenDivergence (a.sub a₀) (b.sub b₀) (c.sub c₀) ur uθ urr urθ uθθ =
      n07aOpenDivergence a b c ur uθ urr urθ uθθ -
        n07aOpenDivergence a₀ b₀ c₀ ur uθ urr urθ uθθ := by
  simp only [n07aOpenDivergence, N07aCanonicalOpenCoefficient.sub_mul,
    N07aCanonicalOpenCoefficient.jet_sub_mul]
  abel

theorem n07aOpenDivergence_sub_pairing
    (a b c a₀ b₀ c₀ : N07aCanonicalOpenCoefficient S K m)
    (ur uθ urr urθ uθθ lower : CanonicalL2 S K m)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    (∫ p, (n07aOpenDivergence (a.sub a₀) (b.sub b₀) (c.sub c₀) ur uθ urr urθ uθθ + lower) p * W p
      ∂canonicalMeasure S K m) =
      (∫ p, n07aOpenDivergence a b c ur uθ urr urθ uθθ p * W p ∂canonicalMeasure S K m) -
      (∫ p, n07aOpenDivergence a₀ b₀ c₀ ur uθ urr urθ uθθ p * W p ∂canonicalMeasure S K m) +
      ∫ p, lower p * W p ∂canonicalMeasure S K m := by
  rw [← n07aCanonicalTestPairing_apply W (n07a_canonicalTest_memLp hW), map_add,
    n07aOpenDivergence_sub, map_sub]
  simp only [n07aCanonicalTestPairing_apply]

variable {D : ReferenceData} {T : MaterialData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {V : VolumeModelData S K}
  {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

def n07aRelativePrincipalJet
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m)
    (ur uθ urr urθ uθθ : CanonicalL2 S K m) : CanonicalL2 S K m :=
  n07aOpenDivergence
    ((n07aCurrentOpenCoefficient href hcur z hz m hm 0).sub (n07aReferenceOpenCoefficient href m hm 0))
    ((n07aCurrentOpenCoefficient href hcur z hz m hm 1).sub (n07aReferenceOpenCoefficient href m hm 1))
    ((n07aCurrentOpenCoefficient href hcur z hz m hm 2).sub (n07aReferenceOpenCoefficient href m hm 2))
    ur uθ urr urθ uθθ

end ContinuousFlexibility.Analysis
