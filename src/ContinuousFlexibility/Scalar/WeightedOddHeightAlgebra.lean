import ContinuousFlexibility.Scalar.WeightedHeightAlgebra
import ContinuousFlexibility.Scalar.WeightedOddProductMap
import ContinuousFlexibility.Scalar.WeightedAngularJetProduct
import ContinuousFlexibility.Scalar.WeightedStateRegularity

/-!
# Even primitives for the actual odd scalar algebra

Odd coefficients are represented by their even angular primitives. These
operations retain the actual product decoder and never assert that an odd
coefficient is an even height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem angularPartial_decode_height_add
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (u + v)) p =
      angularPartial ((S.height scalarBeta).decode u) p +
        angularPartial ((S.height scalarBeta).decode v) p := by
  rw [map_add]
  change angularPartial (fun q => (S.height scalarBeta).decode u q +
    (S.height scalarBeta).decode v q) p = _
  exact angularPartial_add
    ((scalarHeight_decode_contDiff_and_flatJets hT hS u).1.differentiable (by simp) p)
    ((scalarHeight_decode_contDiff_and_flatJets hT hS v).1.differentiable (by simp) p)

theorem angularPartial_decode_height_smul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (c : ℝ) (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (c • u)) p =
      c * angularPartial ((S.height scalarBeta).decode u) p := by
  rw [map_smul]
  change angularPartial (fun q => c * (S.height scalarBeta).decode u q) p = _
  rw [angularPartial_mul (differentiableAt_const c)
    ((scalarHeight_decode_contDiff_and_flatJets hT hS u).1.differentiable (by simp) p),
    angularPartial_const, zero_mul, zero_add]

theorem angularPartial_decode_height_neg
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (-u)) p =
      -angularPartial ((S.height scalarBeta).decode u) p := by
  simpa only [neg_one_smul, neg_one_mul] using
    angularPartial_decode_height_smul hT hS (-1) u p

theorem angularPartial_decode_height_zero (S : PhysicalSpacesData) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode 0) p = 0 := by
  rw [map_zero]
  exact angularPartial_const 0

def scalarHeightOddMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  SobolevModelData.oddProductPrimitiveMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos ![u, v]

theorem angularPartial_decode_scalarHeightOddMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarHeightOddMul hT hS u v)) p =
      (S.height scalarBeta).decode u p * angularPartial ((S.height scalarBeta).decode v) p := by
  simpa only [scalarHeightOddMul, Matrix.cons_val_zero, Matrix.cons_val_one] using
    congrFun (SobolevModelData.angularPartial_decode_oddProductPrimitiveMap hT
      (hS.1 scalarBeta) (scalarHeightInterpolation hS) scalarBeta_pos ![u, v]) p

def scalarHeightOddUnitalAct
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  v + scalarHeightOddMul hT hS u v

theorem angularPartial_decode_scalarHeightOddUnitalAct
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarHeightOddUnitalAct hT hS u v)) p =
      (1 + (S.height scalarBeta).decode u p) *
        angularPartial ((S.height scalarBeta).decode v) p := by
  have hv := (scalarHeight_decode_contDiff_and_flatJets hT hS v).1
  have hm := (scalarHeight_decode_contDiff_and_flatJets hT hS
    (scalarHeightOddMul hT hS u v)).1
  simp only [scalarHeightOddUnitalAct, map_add]
  rw [show (S.height scalarBeta).decode v +
      (S.height scalarBeta).decode (scalarHeightOddMul hT hS u v) =
      (fun q => (S.height scalarBeta).decode v q +
        (S.height scalarBeta).decode (scalarHeightOddMul hT hS u v) q) from rfl,
    angularPartial_add (hv.differentiable (by simp) p) (hm.differentiable (by simp) p),
    angularPartial_decode_scalarHeightOddMul]
  ring

def scalarHeightAngularMul (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) : ScalarHeightSpace S :=
  SobolevModelData.angularJetProductMap hT (hS.1 scalarBeta)
    (scalarHeightInterpolation hS) scalarBeta_pos.le ![u, v]

theorem decode_scalarHeightAngularMul
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u v : ScalarHeightSpace S) (p : PolarPoint) :
    (S.height scalarBeta).decode (scalarHeightAngularMul hT hS u v) p =
      angularPartial ((S.height scalarBeta).decode u) p *
        angularPartial ((S.height scalarBeta).decode v) p := by
  simpa only [scalarHeightAngularMul, Matrix.cons_val_zero, Matrix.cons_val_one] using
    congrFun (SobolevModelData.decode_angularJetProductMap hT (hS.1 scalarBeta)
      (scalarHeightInterpolation hS) scalarBeta_pos ![u, v]) p

theorem scalarHeightAngularMul_zero_left
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    scalarHeightAngularMul hT hS 0 u = 0 := by
  apply (hS.1 scalarBeta).2.2.2.2.2.1
  funext p
  simp only [decode_scalarHeightAngularMul, map_zero]
  change angularPartial (fun _ : PolarPoint => (0 : ℝ)) p *
    angularPartial ((S.height scalarBeta).decode u) p = 0
  rw [angularPartial_const, zero_mul]

theorem scalarHeightAngularMul_zero_right
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    scalarHeightAngularMul hT hS u 0 = 0 := by
  apply (hS.1 scalarBeta).2.2.2.2.2.1
  funext p
  simp only [decode_scalarHeightAngularMul, map_zero]
  change angularPartial ((S.height scalarBeta).decode u) p *
    angularPartial (fun _ : PolarPoint => (0 : ℝ)) p = 0
  rw [angularPartial_const, mul_zero]

/-- A fixed radial reference multiplier acts on odd primitives with the
same literal multiplier on their decoded angular derivatives. -/
theorem angularPartial_decode_scalarReferenceWCLM
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarHeightSpace S) (p : PolarPoint) :
    angularPartial ((S.height scalarBeta).decode (scalarReferenceWCLM hD hT hS u)) p =
      D.w p.1 * angularPartial ((S.height scalarBeta).decode u) p := by
  have heq : (S.height scalarBeta).decode (scalarReferenceWCLM hD hT hS u) =
      fun q => D.w q.1 * (S.height scalarBeta).decode u q :=
    funext (decode_scalarReferenceWCLM hD hT hS u)
  obtain ⟨B, hB⟩ := hD
  have hw : ContDiff ℝ ∞ D.w := hB.1.2.2.1.1
  have hu := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  rw [heq, angularPartial_mul ((hw.comp contDiff_fst).differentiable (by simp) p)
    (hu.differentiable (by simp) p)]
  have hz : angularPartial (fun q : PolarPoint => D.w q.1) p = 0 :=
    Radial.angularPartial_radialHeightField (hw.differentiable (by simp) p.1)
  rw [hz, zero_mul, zero_add]

end ContinuousFlexibility.Statements
