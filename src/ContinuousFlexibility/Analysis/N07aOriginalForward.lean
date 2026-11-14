module

public import ContinuousFlexibility.Analysis.N07aMixedCoefficientSum
public import ContinuousFlexibility.Analysis.N07aForwardConservation
public import ContinuousFlexibility.Analysis.N07aDiagonalCoefficientParameter
public import ContinuousFlexibility.Analysis.N07aMixedCoefficientParameter

/-!
# The original physical forward map on the common height space

N01's two diagonal coefficient fields and the actual primitive of its
mixed coefficient determine this continuous linear operator. The zero
reference operator supplies the fixed background. Conservation places
the literal output in the prescribed source kernel.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n07aOriginalForwardHeightCLM
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  scalarCoefficientOperatorCLM h01.1.1 hT hS 0 0 0 +
    n07aMixedCoefficientOperatorCLM h01.1.1 hT hS (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
        0 (by decide) z)
      (n07aMixedCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64) z)
      (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
        2 (by decide) z)

theorem n07aOriginalForwardHeightCLM_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) (u : ScalarCommonHeight S) :
    n07aOriginalForwardHeightCLM hS hT h01 z u =
      scalarCoefficientOperatorCLM h01.1.1 hT hS 0 0 0 u +
        n07aMixedCoefficientOperatorCLM h01.1.1 hT hS (by norm_num : (0 : ℝ) ≤ 1 / 64)
          (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
            0 (by decide) z)
          (n07aMixedCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64) z)
          (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
            2 (by decide) z) u :=
  ContinuousLinearMap.add_apply _ _ _

theorem n07aOriginalForwardHeightCLM_Q_zero
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) (u : ScalarCommonHeight S) :
    S.Q (n07aOriginalForwardHeightCLM hS hT h01 z u) = 0 := by
  have href := n07a_scalarCoefficientOperator_Q_zero h01.1.1 hT hS 0 0 0 u
  have hdelta := n07aMixedCoefficientOperator_Q_zero h01.1.1 hT hS
    (by norm_num : (0 : ℝ) < 1 / 64)
    (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
      0 (by decide) z)
    (n07aMixedCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64) z)
    (n07aDiagonalCoefficientHeight hS hT h01 (by norm_num : (1 / 64 : ℝ) < 3 / 64)
      2 (by decide) z) u
  exact (congrArg S.Q (n07aOriginalForwardHeightCLM_apply hS hT h01 z u)).trans
    ((map_add S.Q _ _).trans ((congrArg₂ (· + ·) href hdelta).trans (zero_add 0)))

def n07aOriginalForwardCLM
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) : HeightPair S →L[ℝ] S.Source :=
  (n07aOriginalForwardHeightCLM hS hT h01 z).codRestrict S.Q.toLinearMap.ker
    (n07aOriginalForwardHeightCLM_Q_zero hS hT h01 z)

theorem n07aOriginalForwardCLM_apply_val
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (z : StateDirections S × ℝ) (u : HeightPair S) :
    (n07aOriginalForwardCLM hS hT h01 z u).val =
      n07aOriginalForwardHeightCLM hS hT h01 z u := by
  exact ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

theorem n07aOriginalForwardHeightCLM_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : ScalarCommonHeight S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height scalarBeta).decode (n07aOriginalForwardHeightCLM hS hT h01 z u) p =
      divergenceOperator (originalCoefficients D S C (liftSectorParameter S C z))
        (scalarCommonHeightDecode S u) p := by
  let a : (S.height (1 / 64 : ℝ)).Space := n07aDiagonalCoefficientHeight hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64) 0 (by decide) z
  let b : (S.height (1 / 64 : ℝ)).Space := n07aMixedCoefficientHeight hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64) z
  let c : (S.height (1 / 64 : ℝ)).Space := n07aDiagonalCoefficientHeight hS hT h01
    (by norm_num : (1 / 64 : ℝ) < 3 / 64) 2 (by decide) z
  let da : PolarPoint → ℝ := (S.height (1 / 64 : ℝ)).decode a
  let db : PolarPoint → ℝ := angularPartial ((S.height (1 / 64 : ℝ)).decode b)
  let dc : PolarPoint → ℝ := (S.height (1 / 64 : ℝ)).decode c
  have hcoeff (q : PolarPoint) (hq : q ∈ annularOpen D) :
      D.w q.1 + da q = (originalCoefficients D S C (liftSectorParameter S C z)).a q ∧
      (0 : ℝ) + db q = (originalCoefficients D S C (liftSectorParameter S C z)).b q ∧
      deriv D.w q.1 / q.1 + dc q =
        (originalCoefficients D S C (liftSectorParameter S C z)).c q := by
    have href := n07a_originalCoefficients_reference hS hT h01 q
    have hda : da q = (originalCoefficients D S C (liftSectorParameter S C z)).a q - D.w q.1 := by
      change (S.height (1 / 64 : ℝ)).decode a q = _
      rw [n07aDiagonalCoefficientHeight_decode hS hT h01 _ _ _ hz]
      rw [n07aCoefficientDifferenceField_eqOn _ _ hq]
      simpa [n07aOriginalCoefficientField] using congrArg
        (fun t => (originalCoefficients D S C (liftSectorParameter S C z)).a q - t) href.1
    have hdb : db q = (originalCoefficients D S C (liftSectorParameter S C z)).b q := by
      change angularPartial ((S.height (1 / 64 : ℝ)).decode b) q = _
      rw [n07aMixedCoefficientHeight_angularPartial hS hT h01 _ hz hq,
        n07aCoefficientDifferenceField_eqOn _ _ hq]
      norm_num [n07aOriginalCoefficientField, href.2.1]
    have hdc : dc q = (originalCoefficients D S C (liftSectorParameter S C z)).c q -
        deriv D.w q.1 / q.1 := by
      change (S.height (1 / 64 : ℝ)).decode c q = _
      rw [n07aDiagonalCoefficientHeight_decode hS hT h01 _ _ _ hz,
        n07aCoefficientDifferenceField_eqOn _ _ hq]
      norm_num [n07aOriginalCoefficientField, href.2.2]
    exact ⟨by rw [hda]; ring, by rw [hdb, zero_add], by rw [hdc]; ring⟩
  have hneigh : ∀ᶠ q in 𝓝 p, q ∈ annularOpen D :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  have heq := n07a_symmetricDivergence_coeff_congr
    (hneigh.mono (fun q hq => (hcoeff q hq).1))
    (hneigh.mono (fun q hq => (hcoeff q hq).2.1))
    (hneigh.mono (fun q hq => (hcoeff q hq).2.2)) (u := scalarCommonHeightDecode S u)
  exact (congrArg (fun v : ScalarHeightSpace S => (S.height scalarBeta).decode v p)
    (n07aOriginalForwardHeightCLM_apply hS hT h01 z u)).trans
    ((n07a_reference_add_mixed_decode h01.1.1 hT hS
      (by norm_num : (0 : ℝ) < 1 / 64) a b c u hp).trans heq)

/-- The literal source-kernel output decodes to the original physical operator. -/
theorem n07aOriginalForwardCLM_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n07aOriginalForwardCLM hS hT h01 z u).val p =
      divergenceOperator (originalCoefficients D S C (liftSectorParameter S C z))
        (heightPairField S u) p := by
  exact (congrArg (fun v : ScalarHeightSpace S => (S.height scalarBeta).decode v p)
    (n07aOriginalForwardCLM_apply_val hS hT h01 z u)).trans
    (n07aOriginalForwardHeightCLM_decode hS hT h01 hz u hp)

end ContinuousFlexibility.Analysis
