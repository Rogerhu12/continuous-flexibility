import ContinuousFlexibility.Scalar.WeightedCommonHeightCalculus
import ContinuousFlexibility.Scalar.WeightedBilinearSlots
import ContinuousFlexibility.Scalar.WeightedOddProductMap
import ContinuousFlexibility.Scalar.WeightedAngularJetProduct
import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# The actual corrected operator from its three weighted coefficients

The radial flux is an even height. The angular flux is represented by the
angular derivative of an even primitive. Applying the actual radial and
second angular derivative maps therefore gives a continuous linear operator
on the common height domain, including its free cutoff constant.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def scalarCoefficientNormalCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ScalarHeightSpace S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  let M := SobolevModelData.decodedProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le 1
  let O := SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le
  (scalarReferenceWCLM hD hT hS).comp (scalarCommonRadialCLM hD hT hS) +
    (scalarBilinearFixLeft M a).comp (scalarCommonRadialCLM hD hT hS) +
    (scalarBilinearFixLeft O b).comp (scalarCommonProjectionCLM S)

def scalarCoefficientAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (b c : ScalarHeightSpace S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  let P := SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos
  (scalarBilinearFixRight P b).comp (scalarCommonRadialCLM hD hT hS) +
    (scalarBilinearFixLeft P c).comp (scalarCommonProjectionCLM S) +
    (scalarReferenceCorrectedCLM hD hT hS).comp (scalarCommonProjectionCLM S)

def scalarCoefficientOperatorCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b c : ScalarHeightSpace S) :
    ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S :=
  (SobolevModelData.radialCLM hT (hS.1 scalarBeta)).comp
      (scalarCoefficientNormalCLM hD hT hS a b) +
    (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)).comp
      (scalarCoefficientAngularPrimitiveCLM hD hT hS b c)

theorem scalarCoefficientNormalCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    scalarCoefficientNormalCLM hD hT hS a b u =
      scalarReferenceWCLM hD hT hS (scalarCommonRadialCLM hD hT hS u) +
        scalarHeightMul hT hS a (scalarCommonRadialCLM hD hT hS u) +
        SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos.le ![b, u.1] := by
  simp only [scalarCoefficientNormalCLM, add_apply, ContinuousLinearMap.comp_apply,
    scalarBilinearFixLeft_apply] <;> rfl

theorem scalarCoefficientAngularPrimitiveCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (b c : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    scalarCoefficientAngularPrimitiveCLM hD hT hS b c u =
      SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
        (scalarHeightInterpolation hS) scalarBeta_pos ![scalarCommonRadialCLM hD hT hS u, b] +
      SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
        (scalarHeightInterpolation hS) scalarBeta_pos ![c, u.1] +
      scalarReferenceCorrectedCLM hD hT hS u.1 := by
  simp only [scalarCoefficientAngularPrimitiveCLM, add_apply, ContinuousLinearMap.comp_apply,
    scalarBilinearFixLeft_apply, scalarBilinearFixRight_apply] <;> rfl

theorem scalarCoefficientOperatorCLM_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b c : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    scalarCoefficientOperatorCLM hD hT hS a b c u =
      SobolevModelData.radialCLM hT (hS.1 scalarBeta)
        (scalarCoefficientNormalCLM hD hT hS a b u) +
      SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)
        (scalarCoefficientAngularPrimitiveCLM hD hT hS b c u) := rfl

theorem scalarHeightDecode_add (S : PhysicalSpacesData) (u v : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (u + v) =
      fun p => (S.height scalarBeta).decode u p + (S.height scalarBeta).decode v p :=
  (S.height scalarBeta).decode.map_add u v

theorem scalarHeightDecode_add_three (S : PhysicalSpacesData)
    (u v w : ScalarHeightSpace S) :
    (S.height scalarBeta).decode (u + v + w) =
      fun p => (S.height scalarBeta).decode u p +
        (S.height scalarBeta).decode v p + (S.height scalarBeta).decode w p := by
  rw [scalarHeightDecode_add S (u + v) w, scalarHeightDecode_add S u v]

theorem scalarHeightDecode_angularPartial_add
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u v : ScalarHeightSpace S) :
    angularPartial ((S.height scalarBeta).decode (u + v)) =
      fun p => angularPartial ((S.height scalarBeta).decode u) p +
        angularPartial ((S.height scalarBeta).decode v) p := by
  rw [map_add]
  funext p
  exact angularPartial_add
    ((scalarHeight_decode_contDiff_and_flatJets hT hS u).1.differentiable (by simp) p)
    ((scalarHeight_decode_contDiff_and_flatJets hT hS v).1.differentiable (by simp) p)

theorem scalarHeightDecode_angularPartial_add_three
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v w : ScalarHeightSpace S) :
    angularPartial ((S.height scalarBeta).decode (u + v + w)) =
      fun p => angularPartial ((S.height scalarBeta).decode u) p +
        angularPartial ((S.height scalarBeta).decode v) p +
        angularPartial ((S.height scalarBeta).decode w) p := by
  rw [scalarHeightDecode_angularPartial_add hT hS (u + v) w,
    scalarHeightDecode_angularPartial_add hT hS u v]

theorem decode_scalarCoefficientNormalCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCoefficientNormalCLM hD hT hS a b u) =
      fun p => (D.w p.1 + (S.height scalarBeta).decode a p) *
          radialPartial (scalarCommonHeightDecode S u) p +
        angularPartial ((S.height scalarBeta).decode b) p *
          angularPartial (scalarCommonHeightDecode S u) p := by
  have hur := decode_scalarCommonRadialCLM hD hT hS u
  have hup := scalarCommonHeightDecode_angularPartial hT hS u
  have hO := SobolevModelData.decode_angularJetProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos ![b, u.1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hO
  have hsplit := (congrArg (S.height scalarBeta).decode
    (scalarCoefficientNormalCLM_apply hD hT hS a b u)).trans
      (scalarHeightDecode_add_three S
        (scalarReferenceWCLM hD hT hS (scalarCommonRadialCLM hD hT hS u))
        (scalarHeightMul hT hS a (scalarCommonRadialCLM hD hT hS u))
        (SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos.le ![b, u.1]))
  funext p
  calc
    _ = (S.height scalarBeta).decode
          (scalarReferenceWCLM hD hT hS (scalarCommonRadialCLM hD hT hS u)) p +
        (S.height scalarBeta).decode
          (scalarHeightMul hT hS a (scalarCommonRadialCLM hD hT hS u)) p +
        (S.height scalarBeta).decode
          (SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
            (scalarHeightInterpolation hS) scalarBeta_pos.le ![b, u.1]) p :=
      congrFun hsplit p
    _ = D.w p.1 * radialPartial (scalarCommonHeightDecode S u) p +
        (S.height scalarBeta).decode a p * radialPartial (scalarCommonHeightDecode S u) p +
        angularPartial ((S.height scalarBeta).decode b) p *
          angularPartial (scalarCommonHeightDecode S u) p :=
      congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y)
          ((decode_scalarReferenceWCLM hD hT hS
            (scalarCommonRadialCLM hD hT hS u) p).trans
              (congrArg (fun z : ℝ => D.w p.1 * z) (congrFun hur p)))
          ((decode_scalarHeightMul hT hS a (scalarCommonRadialCLM hD hT hS u) p).trans
            (congrArg (fun z : ℝ => (S.height scalarBeta).decode a p * z)
              (congrFun hur p))))
        ((congrFun hO p).trans
          (congrArg (fun z : ℝ => angularPartial ((S.height scalarBeta).decode b) p * z)
            (congrFun hup.symm p)))
    _ = _ := by ring

theorem angularPartial_decode_scalarCoefficientAngularPrimitiveCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (b c : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    angularPartial ((S.height scalarBeta).decode
      (scalarCoefficientAngularPrimitiveCLM hD hT hS b c u)) =
      fun p => angularPartial ((S.height scalarBeta).decode b) p *
          radialPartial (scalarCommonHeightDecode S u) p +
        (deriv D.w p.1 / p.1 + (S.height scalarBeta).decode c p) *
          angularPartial (scalarCommonHeightDecode S u) p := by
  have hur := decode_scalarCommonRadialCLM hD hT hS u
  have hup := scalarCommonHeightDecode_angularPartial hT hS u
  have hP₁ := SobolevModelData.angularPartial_decode_oddProductPrimitiveMap hT
    (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos
    ![scalarCommonRadialCLM hD hT hS u, b]
  have hP₂ := SobolevModelData.angularPartial_decode_oddProductPrimitiveMap hT
    (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos ![c, u.1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hP₁ hP₂
  have hC := angularPartial_decode_scalarReferenceCorrectedCLM hD hT hS u.1
  have hsplit := (congrArg
    (fun v : ScalarHeightSpace S => angularPartial ((S.height scalarBeta).decode v))
    (scalarCoefficientAngularPrimitiveCLM_apply hD hT hS b c u)).trans
      (scalarHeightDecode_angularPartial_add_three hT hS
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos
          ![scalarCommonRadialCLM hD hT hS u, b])
        (SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
          (scalarHeightInterpolation hS) scalarBeta_pos ![c, u.1])
        (scalarReferenceCorrectedCLM hD hT hS u.1))
  funext p
  apply (congrFun hsplit p).trans
  calc
    _ = radialPartial (scalarCommonHeightDecode S u) p *
          angularPartial ((S.height scalarBeta).decode b) p +
        (S.height scalarBeta).decode c p * angularPartial (scalarCommonHeightDecode S u) p +
        (deriv D.w p.1 / p.1) * angularPartial (scalarCommonHeightDecode S u) p :=
      congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y)
          ((congrFun hP₁ p).trans
            (congrArg (fun z : ℝ => z * angularPartial ((S.height scalarBeta).decode b) p)
              (congrFun hur p)))
          ((congrFun hP₂ p).trans
            (congrArg (fun z : ℝ => (S.height scalarBeta).decode c p * z)
              (congrFun hup.symm p))))
        ((congrFun hC p).trans
          (congrArg (fun z : ℝ => (deriv D.w p.1 / p.1) * z) (congrFun hup.symm p)))
    _ = _ := by ring

/-- Exact divergence decoding before substituting any scalar-state formula. -/
theorem decode_scalarCoefficientOperatorCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b c : ScalarHeightSpace S) (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCoefficientOperatorCLM hD hT hS a b c u) =
      symmetricDivergence
        (fun p => D.w p.1 + (S.height scalarBeta).decode a p)
        (angularPartial ((S.height scalarBeta).decode b))
        (fun p => deriv D.w p.1 / p.1 + (S.height scalarBeta).decode c p)
        (scalarCommonHeightDecode S u) := by
  have hR := (SobolevModelData.decode_radialCLM hT (hS.1 scalarBeta)
    (scalarCoefficientNormalCLM hD hT hS a b u)).trans
      (congrArg radialPartial (decode_scalarCoefficientNormalCLM hD hT hS a b u))
  have hA := (SobolevModelData.decode_angularSecondCLM hT (hS.1 scalarBeta)
    (scalarCoefficientAngularPrimitiveCLM hD hT hS b c u)).trans
      (congrArg angularPartial
        (angularPartial_decode_scalarCoefficientAngularPrimitiveCLM hD hT hS b c u))
  have hsplit := (congrArg (S.height scalarBeta).decode
    (scalarCoefficientOperatorCLM_apply hD hT hS a b c u)).trans
      (scalarHeightDecode_add S
        (SobolevModelData.radialCLM hT (hS.1 scalarBeta)
          (scalarCoefficientNormalCLM hD hT hS a b u))
        (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta)
          (scalarCoefficientAngularPrimitiveCLM hD hT hS b c u)))
  exact hsplit.trans
    (congrArg₂ (fun f g : PolarPoint → ℝ => fun p => f p + g p) hR hA)

/-- The original corrected operator follows from the actual coefficient
decoders; its common-domain endpoint constant is retained. -/
theorem decode_scalarCoefficientOperatorCLM_of_actual
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : ScalarWeightedState S) (a b c : ScalarHeightSpace S)
    (ha : ∀ p, (S.height scalarBeta).decode a p = scalarStateA D S x p - D.w p.1)
    (hb : ∀ p, angularPartial ((S.height scalarBeta).decode b) p = scalarStateB D S x p)
    (hc : ∀ p, (S.height scalarBeta).decode c p =
      scalarStateCorrectedC D S x p - deriv D.w p.1 / p.1)
    (u : ScalarCommonHeight S) :
    (S.height scalarBeta).decode (scalarCoefficientOperatorCLM hD hT hS a b c u) =
      scalarStateOperator D S x u := by
  have hA : (fun p => D.w p.1 + (S.height scalarBeta).decode a p) = scalarStateA D S x := by
    funext p
    rw [ha p]
    ring
  have hB : angularPartial ((S.height scalarBeta).decode b) = scalarStateB D S x := funext hb
  have hC : (fun p => deriv D.w p.1 / p.1 + (S.height scalarBeta).decode c p) =
      scalarStateCorrectedC D S x := by
    funext p
    rw [hc p]
    ring
  rw [decode_scalarCoefficientOperatorCLM hD hT hS a b c u, hA, hB, hC] <;> rfl

end ContinuousFlexibility.Statements
