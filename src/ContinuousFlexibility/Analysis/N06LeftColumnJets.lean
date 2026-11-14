module

public import ContinuousFlexibility.Analysis.N06LeftColumnPhysical
public import ContinuousFlexibility.Analysis.CylinderMixedJets
public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# Angular jets of the genuine left-column difference

Only the a and b flux coefficients act on the radial cutoff. The formula
below retains the original cutoff derivatives and the actual mixed jets
of the original coefficient differences. The corrected operator is
identified with that formula by N03 on the cutoff support.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

theorem n06_divergence_radial_cutoff_formula (A : SymmetricCoefficients)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {p : PolarPoint}
    (ha : DifferentiableAt ℝ A.a p) (hb : DifferentiableAt ℝ A.b p) :
    divergenceOperator A (n06ReferenceLeftField χ) p =
      deriv (deriv χ) p.1 * A.a p + deriv χ p.1 * radialPartial A.a p +
        deriv χ p.1 * angularPartial A.b p := by
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hd : DifferentiableAt ℝ (fun q : PolarPoint => deriv χ q.1) p :=
    (hχ'.comp contDiff_fst).differentiable (by simp) p
  have hr : radialPartial (fun q : PolarPoint => deriv χ q.1) p =
      deriv (deriv χ) p.1 := radialPartial_radialHeightField (hχ'.differentiable (by simp) p.1)
  have ht : angularPartial (fun q : PolarPoint => deriv χ q.1) p = 0 :=
    angularPartial_radialHeightField (hχ'.differentiable (by simp) p.1)
  rw [n06_divergence_radial_cutoff_flux A hχ p,
    radialPartial_mul ha hd, angularPartial_mul hb hd, hr, ht]
  ring

theorem n06_radial_cutoff_angularJet_on_strip
    {l r : ℝ} (A : SymmetricCoefficients) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (ha : ContDiffOn ℝ ∞ A.a (Ioo l r ×ˢ (univ : Set ℝ)))
    (hb : ContDiffOn ℝ ∞ A.b (Ioo l r ×ˢ (univ : Set ℝ)))
    (k : ℕ) {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    mixedDerivative 0 k (divergenceOperator A (n06ReferenceLeftField χ)) p =
      deriv (deriv χ) p.1 * mixedDerivative 0 k A.a p +
        deriv χ p.1 * mixedDerivative 1 k A.a p +
        deriv χ p.1 * mixedDerivative 0 (k + 1) A.b p := by
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have he : EqOn (divergenceOperator A (n06ReferenceLeftField χ))
      (fun q => deriv (deriv χ) q.1 * A.a q + deriv χ q.1 * radialPartial A.a q +
        deriv χ q.1 * angularPartial A.b q) (Ioo l r ×ˢ (univ : Set ℝ)) := by
    intro q hq
    exact n06_divergence_radial_cutoff_formula A hχ (p := q)
      (ha.contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp))
      (hb.contDiffAt (hU.mem_nhds hq) |>.differentiableAt (by simp))
  have hs {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ (univ : Set ℝ))) :
      ContDiff ℝ ∞ (fun θ => f (p.1, θ)) :=
    hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun θ => ⟨hp.1, mem_univ θ⟩)
  have h₁ : ContDiff ℝ ∞ (fun θ => deriv (deriv χ) p.1 * A.a (p.1, θ)) :=
    contDiff_const.mul (hs ha)
  have h₂ : ContDiff ℝ ∞ (fun θ => deriv χ p.1 * radialPartial A.a (p.1, θ)) :=
    contDiff_const.mul (hs (scalar_contDiffOn_radialPartial hU ha))
  have h₃ : ContDiff ℝ ∞ (fun θ => deriv χ p.1 * angularPartial A.b (p.1, θ)) :=
    contDiff_const.mul (hs (scalar_contDiffOn_angularPartial hU hb))
  have hsum : mixedDerivative 0 k
      (fun q => deriv (deriv χ) q.1 * A.a q + deriv χ q.1 * radialPartial A.a q +
        deriv χ q.1 * angularPartial A.b q) p =
      deriv (deriv χ) p.1 * mixedDerivative 0 k A.a p +
        deriv χ p.1 * mixedDerivative 0 k (radialPartial A.a) p +
        deriv χ p.1 * mixedDerivative 0 k (angularPartial A.b) p := by
    simp only [mixedDerivative, iteratedDeriv_zero]
    rw [iteratedDeriv_fun_add ((h₁.add h₂).contDiffAt.of_le (by simp))
      (h₃.contDiffAt.of_le (by simp)),
      iteratedDeriv_fun_add (h₁.contDiffAt.of_le (by simp)) (h₂.contDiffAt.of_le (by simp))]
    simp only [iteratedDeriv_const_mul_field]
  refine (mixedDerivative_eqOn_of_isOpen hU he 0 k hp).trans (hsum.trans ?_)
  rw [mixedDerivative_radialPartial hU ha 0 k hp, mixedDerivative_angularPartial hU hb 0 k hp]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

def n06OriginalCoefficientDifference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) : SymmetricCoefficients where
  a := fun p => (originalCoefficients D S C z).a p -
    (originalCoefficients D S C (C.referenceState, 0)).a p
  b := fun p => (originalCoefficients D S C z).b p -
    (originalCoefficients D S C (C.referenceState, 0)).b p
  c := fun p => (originalCoefficients D S C z).c p -
    (originalCoefficients D S C (C.referenceState, 0)).c p

def n06LeftColumnDifference (D : ReferenceData) (S : PhysicalSpacesData)
    (L : ReturnCorrectionData S) (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  fun p => n06CurrentLeftColumn S L z p -
    n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) p

theorem n06_leftColumnDifference_eq_divergence
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    n06LeftColumnDifference D S L z p =
      divergenceOperator (n06OriginalCoefficientDifference D S C z)
        (n06ReferenceLeftField S.chiLeft) p := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hc := n06_originalCoefficients_contDiffAt hT hS h01 hz hs hp
  have hr := n06_originalCoefficients_contDiffAt hT hS h01 href hsector hp
  have hleft := n06_currentLeftColumn_eq_original hS h03 hz hs p
  have hright := (n06_currentLeftColumn_reference hS h01 h03 p).symm.trans
    (n06_currentLeftColumn_eq_original hS h03 href hsector p)
  have hχ : ContDiff ℝ ∞ (n06ReferenceLeftField S.chiLeft) :=
    n06_referenceLeftField_contDiff hS.2.2.1.1
  exact (congrArg₂ (fun a b : ℝ => a - b) hleft hright).trans
    (n06_divergenceOperator_sub (hc.1.differentiableAt (by simp))
      (hc.2.1.differentiableAt (by simp)) (hc.2.2.differentiableAt (by simp))
      (hr.1.differentiableAt (by simp)) (hr.2.1.differentiableAt (by simp))
      (hr.2.2.differentiableAt (by simp)) (hχ.contDiffAt.of_le (by simp)))

theorem n06_leftColumnDifference_angularJet
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (k : ℕ) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    mixedDerivative 0 k (n06LeftColumnDifference D S L z) p =
      deriv (deriv S.chiLeft) p.1 * coefficientFamily D S C 0 0 k p z +
        deriv S.chiLeft p.1 * coefficientFamily D S C 0 1 k p z +
        deriv S.chiLeft p.1 * coefficientFamily D S C 1 0 (k + 1) p z := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hc (q : PolarPoint) (hq : q ∈ annularOpen D) :=
    n06_originalCoefficients_contDiffAt hT hS h01 hz hs hq
  have hr (q : PolarPoint) (hq : q ∈ annularOpen D) :=
    n06_originalCoefficients_contDiffAt hT hS h01 href hsector hq
  have ha : ContDiffOn ℝ ∞ (n06OriginalCoefficientDifference D S C z).a (annularOpen D) :=
    fun q hq => ((hc q hq).1.sub (hr q hq).1).contDiffWithinAt
  have hb : ContDiffOn ℝ ∞ (n06OriginalCoefficientDifference D S C z).b (annularOpen D) :=
    fun q hq => ((hc q hq).2.1.sub (hr q hq).2.1).contDiffWithinAt
  have he : EqOn (n06LeftColumnDifference D S L z)
      (divergenceOperator (n06OriginalCoefficientDifference D S C z)
        (n06ReferenceLeftField S.chiLeft)) (annularOpen D) :=
    fun q hq => n06_leftColumnDifference_eq_divergence hT hS h01 h03 hz hs hq
  have hj := n06_radial_cutoff_angularJet_on_strip (n06OriginalCoefficientDifference D S C z)
    hS.2.2.1.1 ha hb k hp
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  exact (mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) he 0 k hp).trans
    (by simpa only [coefficientFamily, n06OriginalCoefficientDifference,
      if_pos rfl, if_neg h10, ite_true, ite_false] using hj)

end ContinuousFlexibility.Statements
