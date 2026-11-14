module

public import ContinuousFlexibility.Analysis.CoupledErrorParity
public import ContinuousFlexibility.Analysis.CoupledDerivativeAlgebra
public import ContinuousFlexibility.Analysis.CoupledWeakScalarError
public import ContinuousFlexibility.Scalar.WeightedScalarError
public import ContinuousFlexibility.Scalar.WeightedErrorConservation

/-!
# Source-valued bilinear errors and the coupled quadratic candidate

The scalar error is a second angular derivative of an actual weighted
height. Its conservation law therefore holds for every normalized type
coefficient, before that coefficient is identified with the nonlinear
geometry. Both independent variables remain linear. The circle component
uses the existing even projection and agrees with the actual N02 error on
the geometric domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

section Bilinear

variable {E F G E' F' G' : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup E'] [Module ℝ E']
  [AddCommGroup F'] [Module ℝ F'] [AddCommGroup G'] [Module ℝ G']

/-- Linear changes of both independent inputs and the output preserve the
actual curried bilinear map. -/
def coupledBilinearTransport (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (L : E' →ₗ[ℝ] E) (M : F' →ₗ[ℝ] F) (N : G →ₗ[ℝ] G') :
    E' →ₗ[ℝ] F' →ₗ[ℝ] G' where
  toFun x := N.comp ((B (L x)).comp M)
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem coupledBilinearTransport_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (L : E' →ₗ[ℝ] E) (M : F' →ₗ[ℝ] F) (N : G →ₗ[ℝ] G') (x : E') (y : F') :
    coupledBilinearTransport B L M N x y = N (B (L x) (M y)) := by
  change (N.comp ((B (L x)).comp M)) y = _
  simp only [LinearMap.comp_apply]

/-- Pair two bilinear maps before substituting the concrete physical spaces. -/
def coupledBilinearProd (A : E →ₗ[ℝ] F →ₗ[ℝ] G) (B : E →ₗ[ℝ] F →ₗ[ℝ] G') :
    E →ₗ[ℝ] F →ₗ[ℝ] G × G' where
  toFun x := (A x).prod (B x)
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro v
    simp only [LinearMap.prod_apply, Function.prod_apply, map_add,
      LinearMap.add_apply, Prod.mk_add_mk]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro v
    simp only [LinearMap.prod_apply, Function.prod_apply, map_smul,
      LinearMap.smul_apply, Prod.smul_mk, RingHom.id_apply]

theorem coupledBilinearProd_apply (A : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G') (x : E) (y : F) :
    coupledBilinearProd A B x y = (A x y, B x y) := by
  change ((A x).prod (B x)) y = _
  simp only [LinearMap.prod_apply, Function.prod_apply]

/-- Restrict the range of a bilinear map once its actual values belong to
the submodule. The restriction preserves both independent linearities. -/
def coupledBilinearCodRestrict (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (W : Submodule ℝ G) (hB : ∀ x y, B x y ∈ W) :
    E →ₗ[ℝ] F →ₗ[ℝ] W where
  toFun x := (B x).codRestrict W (hB x)
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.add_apply, Submodule.coe_add, LinearMap.codRestrict_apply,
      map_add]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.codRestrict_apply,
      map_smul, RingHom.id_apply]

theorem coupledBilinearCodRestrict_val (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (W : Submodule ℝ G) (hB : ∀ x y, B x y ∈ W) (x : E) (y : F) :
    (coupledBilinearCodRestrict B W hB x y).val = B x y :=
  LinearMap.codRestrict_apply _ _ _

end Bilinear

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Every second angular derivative in the actual height model is a source.
Only smoothness on the annulus and angular periodicity enter conservation. -/
theorem coupled_angularSecondCLM_compatible
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarHeightSpace S) :
    S.Q (SobolevModelData.angularSecondCLM hT (hS.1 scalarBeta) u) = 0 := by
  have hQ : ∀ f : ScalarHeightSpace S,
      S.Q f = physicalSourceIntegral D ((S.height scalarBeta).decode f) := by
    obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hS
    exact hQ
  rw [hQ, SobolevModelData.decode_angularSecondCLM]
  have hu := (hS.1 scalarBeta).2.2.2.1 u
  have hflux : ContDiffOn ℝ ∞ (angularPartial ((S.height scalarBeta).decode u))
      (annularOpen D) :=
    scalar_contDiffOn_angularPartial (isOpen_Ioo.prod isOpen_univ) hu.1
  exact physicalSourceIntegral_angularPartial_eq_zero hD.choose_spec.1.2.1.le
    hflux (periodic_angularPartial hu.2.2.1)

/-- The independent scalar error uses the actual weak normalized coefficient. -/
def coupledScalarTypeErrorSourceLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (t : CoupledWeakHeight S) :
    ScalarHeightSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] S.Source :=
  coupledWeakTypeErrorSourceLinear hD hT hS t

theorem coupledScalarTypeErrorSourceLinear_val
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (t : CoupledWeakHeight S)
    (r : ScalarHeightSpace S) (η : HeightPair S) :
    (coupledScalarTypeErrorSourceLinear hD hT hS t r η).val =
      coupledWeakTypeErrorLinear hD hT hS t r η :=
  coupledWeakTypeErrorSourceLinear_val hD hT hS t r η

/-- The normalized weak coefficient gives the exact angular-divergence formula. -/
theorem coupledScalarTypeErrorSourceLinear_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (t : CoupledWeakHeight S) (F : PolarPoint → ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height coupledWeakProfileWeight).decode t p =
      D.w p.1 * F p - (1 + D.w p.1 ^ 2) / p.1)
    (r : ScalarHeightSpace S) (η : HeightPair S) :
    (S.height (3 / 4 : ℝ)).decode (coupledScalarTypeErrorSourceLinear hD hT hS t r η).val =
      scalarCorrectionError F ((S.height (3 / 4 : ℝ)).decode r) (heightPairField S η) :=
  coupledWeakTypeErrorSourceLinear_decode hD hT hS t F ht r η

/-- The height component of the given coupled inverse, as a linear map. -/
def coupledErrorHeightLinear (V : CoupledInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] HeightPair S :=
  (LinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))).comp (V.V z)

theorem coupledErrorHeightLinear_apply (V : CoupledInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledErrorHeightLinear V z y = (V.V z y).1 := by
  change ((LinearMap.fst ℝ (HeightPair S)
    (ℝ × (CircleSpace S × CircleSpace S))).comp (V.V z)) y = _
  simp only [LinearMap.comp_apply, LinearMap.fst_apply]

def coupledErrorKappaLinear (V : CoupledInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  (LinearMap.fst ℝ (CircleSpace S) (CircleSpace S)).comp
    ((LinearMap.snd ℝ ℝ (CircleSpace S × CircleSpace S)).comp
      ((LinearMap.snd ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S))).comp (V.V z)))

theorem coupledErrorKappaLinear_apply (V : CoupledInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledErrorKappaLinear V z y = (V.V z y).2.2.1 := by
  simp only [coupledErrorKappaLinear, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

/-- The small-divisor inverse of the actual remaining circle row is linear
in the complete independent source. -/
def coupledErrorInverseLinear (R : ReturnEquationData S) (B : ControlColumnData S)
    (V : CoupledInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  R.inverse.comp
    ((evenCircleSubmodule S).subtype.comp (LinearMap.snd ℝ S.Source (EvenCircle S)) -
      z.2 • (B.heightRow z).toLinearMap.comp (coupledErrorHeightLinear V z) -
      (B.circleColumn z).toLinearMap.comp (coupledErrorKappaLinear V z))

theorem coupledErrorInverseLinear_apply (R : ReturnEquationData S) (B : ControlColumnData S)
    (V : CoupledInverseData S) (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledErrorInverseLinear R B V z y =
      R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
        B.circleColumn z (V.V z y).2.2.1) := by
  simp only [coupledErrorInverseLinear, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.snd_apply, Submodule.subtype_apply,
    coupledErrorHeightLinear_apply, coupledErrorKappaLinear_apply,
    ContinuousLinearMap.coe_coe]

/-- Both scalar errors are already Source-valued before they are added. -/
def coupledScalarQuadraticLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (L : ReturnCorrectionData S)
    (V : CoupledInverseData S) (t : CoupledWeakHeight S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] ResidualSpace S →ₗ[ℝ] S.Source :=
  z.2 • coupledBilinearTransport (coupledScalarTypeErrorSourceLinear hD hT hS t)
    (S.Q.toLinearMap.ker.subtype.comp (LinearMap.fst ℝ S.Source (EvenCircle S)))
    (coupledErrorHeightLinear V z) (LinearMap.id : S.Source →ₗ[ℝ] S.Source) +
  coupledBilinearTransport (L.error z)
    ((evenCircleSubmodule S).subtype.comp (LinearMap.snd ℝ S.Source (EvenCircle S)))
    (coupledErrorHeightLinear V z) (LinearMap.id : S.Source →ₗ[ℝ] S.Source)

theorem coupledScalarQuadraticLinear_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (L : ReturnCorrectionData S)
    (V : CoupledInverseData S) (t : CoupledWeakHeight S) (z : AnnularState S × ℝ)
    (r y : ResidualSpace S) :
    coupledScalarQuadraticLinear hD hT hS L V t z r y =
      z.2 • coupledScalarTypeErrorSourceLinear hD hT hS t r.1.val (V.V z y).1 +
        L.error z r.2.val (V.V z y).1 := by
  simp only [coupledScalarQuadraticLinear, LinearMap.add_apply, LinearMap.smul_apply,
    coupledBilinearTransport_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Submodule.subtype_apply, coupledErrorHeightLinear_apply,
    LinearMap.id_apply] <;> rfl

/-- A total even-circle-valued bilinear map. On the N02 domain the
projection will preserve the actual independent return error. -/
def coupledCircleQuadraticLinear (hS : IsPhysicalSpaces D T S)
    (R : ReturnEquationData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] ResidualSpace S →ₗ[ℝ] EvenCircle S :=
  coupledBilinearTransport (R.error z)
    ((evenCircleSubmodule S).subtype.comp (LinearMap.snd ℝ S.Source (EvenCircle S)))
    (coupledErrorInverseLinear R B V z) (coupledEvenProjectionCLM hS).toLinearMap

theorem coupledCircleQuadraticLinear_apply (hS : IsPhysicalSpaces D T S)
    (R : ReturnEquationData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (z : AnnularState S × ℝ) (r y : ResidualSpace S) :
    coupledCircleQuadraticLinear hS R B V z r y =
      coupledEvenProjectionCLM hS
        (R.error z r.2.val
          (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
            B.circleColumn z (V.V z y).2.2.1))) := by
  simp only [coupledCircleQuadraticLinear, coupledBilinearTransport_apply,
    LinearMap.comp_apply, LinearMap.snd_apply, Submodule.subtype_apply,
    coupledErrorInverseLinear_apply, ContinuousLinearMap.coe_coe]

/-- The total coupled error, retaining exact linearity in both independent
residual variables and the original Source and even-circle codomains. -/
def coupledQuadraticLinear
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (t : CoupledWeakHeight S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] ResidualSpace S →ₗ[ℝ] ResidualSpace S :=
  coupledBilinearProd (coupledScalarQuadraticLinear hD hT hS L V t z)
    (coupledCircleQuadraticLinear hS R B V z)

theorem coupledQuadraticLinear_apply
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (t : CoupledWeakHeight S) (z : AnnularState S × ℝ) (r y : ResidualSpace S) :
    coupledQuadraticLinear hD hT hS R L B V t z r y =
      (coupledScalarQuadraticLinear hD hT hS L V t z r y,
        coupledCircleQuadraticLinear hS R B V z r y) :=
  coupledBilinearProd_apply _ _ r y

def coupledQuadraticErrorData
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S) : QuadraticErrorData S where
  Q z := coupledQuadraticLinear hD hT hS R L B V (typeCoefficient z) z

theorem coupledQuadraticErrorData_scalar
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    (z : AnnularState S × ℝ) (r y : ResidualSpace S) :
    ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).1 =
      z.2 • coupledScalarTypeErrorSourceLinear hD hT hS (typeCoefficient z)
          r.1.val (V.V z y).1 + L.error z r.2.val (V.V z y).1 := by
  exact (congrArg Prod.fst
    (coupledQuadraticLinear_apply hD hT hS R L B V (typeCoefficient z) z r y)).trans
      (coupledScalarQuadraticLinear_apply hD hT hS L V (typeCoefficient z) z r y)

theorem coupledQuadraticErrorData_circle
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    (z : AnnularState S × ℝ) (r y : ResidualSpace S) :
    ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).2 =
      coupledEvenProjectionCLM hS
        (R.error z r.2.val
          (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
            B.circleColumn z (V.V z y).2.2.1))) := by
  exact (congrArg Prod.snd
    (coupledQuadraticLinear_apply hD hT hS R L B V (typeCoefficient z) z r y)).trans
      (coupledCircleQuadraticLinear_apply hS R B V z r y)

/-- The scalar decoding clause is forced by the normalized coefficient
identity; the Source and bilinear structures were constructed independently. -/
theorem coupledQuadraticErrorData_scalar_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    (z : AnnularState S × ℝ)
    (ht : ∀ p ∈ annularOpen D, (S.height coupledWeakProfileWeight).decode (typeCoefficient z) p =
      D.w p.1 * residualErrorCoefficient D S C z p - (1 + D.w p.1 ^ 2) / p.1)
    (r y : ResidualSpace S) (p : PolarPoint) :
    (S.height (3 / 4 : ℝ)).decode
        ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).1.val p =
      z.2 * angularPartial (fun x => residualErrorCoefficient D S C z x *
        (S.height (3 / 4 : ℝ)).decode r.1.val x *
        angularPartial (heightPairField S (V.V z y).1) x) p +
      (S.height (3 / 4 : ℝ)).decode (L.error z r.2.val (V.V z y).1).val p := by
  have hscalar := coupledQuadraticErrorData_scalar hD hT hS R L B V typeCoefficient z r y
  have heval := congrArg (coupledSourceEvaluation S p) hscalar
  simp only [map_add, map_smul, smul_eq_mul, coupledSourceEvaluation_apply] at heval
  have he := congrFun (coupledScalarTypeErrorSourceLinear_decode hD hT hS
    (typeCoefficient z) (residualErrorCoefficient D S C z) ht r.1.val (V.V z y).1) p
  exact heval.trans (congrArg (fun a : ℝ => z.2 * a +
    (S.height (3 / 4 : ℝ)).decode (L.error z r.2.val (V.V z y).1).val p) he)

/-- On the N02 domain the total circle component decodes to the unmodified
independent chart error prescribed by N10. -/
theorem coupledQuadraticErrorData_circle_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) {C : NonlinearGeometryData S}
    (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    {base : ℕ} {ε : ℝ} (h2 : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (r y : ResidualSpace S) (m : ℕ) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode
        ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).2.val m θ =
      circleChartError S C z r.2.val
        (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
          B.circleColumn z (V.V z y).2.2.1)) m θ := by
  have hcircle := coupledQuadraticErrorData_circle hD hT hS R L B V typeCoefficient z r y
  have hproject := coupled_projected_returnError_eq hS h2 hz hs r.2
    (R.inverse (y.2.val - z.2 • B.heightRow z (V.V z y).1 -
      B.circleColumn z (V.V z y).2.2.1))
  exact (congrArg (fun f : EvenCircle S => (S.circle (3 / 4 : ℝ)).decode f.val m θ)
    hcircle).trans
      ((congrArg (fun f : CircleSpace S => (S.circle (3 / 4 : ℝ)).decode f m θ) hproject).trans
        (h2.2.2.2.2.1 z hz hs r.2.val _ m θ))

/-- Conservation holds for every value of the constructed error, including
outside the geometric neighborhood, because its scalar component is a Source. -/
theorem coupledQuadraticErrorData_source_integral
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (L : ReturnCorrectionData S) (B : ControlColumnData S) (V : CoupledInverseData S)
    (typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S)
    (z : AnnularState S × ℝ) (r y : ResidualSpace S) :
    physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode
      ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).1.val) = 0 := by
  have hQ : ∀ f : (S.height (3 / 4 : ℝ)).Space,
      S.Q f = physicalSourceIntegral D ((S.height (3 / 4 : ℝ)).decode f) := by
    obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hS
    exact hQ
  rw [← hQ]
  exact ((coupledQuadraticErrorData hD hT hS R L B V typeCoefficient).Q z r y).1.property

end ContinuousFlexibility.Statements
