module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Algebra of the genuine coupled derivative

The scalar inverse is applied once to the difference of the two sources,
so recovery does not assume an unproved linearity property of a spatial
divergence. The first jet of an actual smooth directional tower combines
the four coordinate directions. Pointwise height differentiation and the
weighted realization of the two error components remain separate analytic
steps; none is substituted for a conclusion of the nonlinear target.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section LineTransport

variable {E V F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Affine changes of the source preserve the actual line quotient. -/
theorem coupled_lineDerivAt_affine_iff (L : E →ₗ[ℝ] V) (a : V)
    {f : V → F} {df : F} {x v : E} :
    HasProjectiveLineDerivAt (fun y => f (a + L y)) df x v ↔
      HasProjectiveLineDerivAt f df (a + L x) (L v) := by
  simp only [HasProjectiveLineDerivAt, map_add, map_smul, add_assoc]

/-- Equality near the base point along the particular line is sufficient.
An ambient open-set equality is unnecessary for sector directions. -/
theorem coupled_lineDerivAt_congr_line
    {f g : E → F} {df : F} {x v : E}
    (hf : HasProjectiveLineDerivAt f df x v)
    (heq : (fun t : ℝ => g (x + t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => f (x + t • v))) :
    HasProjectiveLineDerivAt g df x v := by
  have hx : g x = f x := by
    simpa only [zero_smul, add_zero] using heq.self_of_nhds
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at hf ⊢
  simp only [zero_add, zero_smul, add_zero] at hf ⊢
  apply hf.congr'
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with t ht
  rw [ht, hx]

end LineTransport

section FirstJet

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [T2Space G]

/-- The actual first jet, expressed as a linear map in the direction. -/
theorem coupled_smoothDirections_first_derivative
    {f : E → F} {U : Set E} (J : SmoothDirections U f)
    {x : E} (hx : x ∈ U) (v : E) :
    HasProjectiveLineDerivAt f
      (projectiveJetHeadLinear J.D 0 x Fin.elim0 v) x v := by
  simpa only [projectiveFirstJetValue, projectiveJetHeadLinear_apply] using
    J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hx v

/-- Eight component derivatives identify the first jet on four directions.
Its linearity then gives the derivative in their sum. -/
theorem coupled_derivative_of_four_columns
    {f : E → F × G} {U : Set E} (J : SmoothDirections U f)
    {x v₁ v₂ v₃ v₄ : E} (hx : x ∈ U)
    {a₁ a₂ a₃ a₄ : F} {b₁ b₂ b₃ b₄ : G}
    (h₁ : HasProjectiveLineDerivAt (fun y => (f y).1) a₁ x v₁)
    (h₂ : HasProjectiveLineDerivAt (fun y => (f y).1) a₂ x v₂)
    (h₃ : HasProjectiveLineDerivAt (fun y => (f y).1) a₃ x v₃)
    (h₄ : HasProjectiveLineDerivAt (fun y => (f y).1) a₄ x v₄)
    (k₁ : HasProjectiveLineDerivAt (fun y => (f y).2) b₁ x v₁)
    (k₂ : HasProjectiveLineDerivAt (fun y => (f y).2) b₂ x v₂)
    (k₃ : HasProjectiveLineDerivAt (fun y => (f y).2) b₃ x v₃)
    (k₄ : HasProjectiveLineDerivAt (fun y => (f y).2) b₄ x v₄) :
    HasProjectiveLineDerivAt f
      (a₁ + a₂ + a₃ + a₄, b₁ + b₂ + b₃ + b₄) x (v₁ + v₂ + v₃ + v₄) := by
  let D : E →L[ℝ] F × G := projectiveJetHeadLinear J.D 0 x Fin.elim0
  have hD (v : E) : HasProjectiveLineDerivAt f (D v) x v :=
    coupled_smoothDirections_first_derivative J hx v
  have identify {v : E} {a : F} {b : G}
      (ha : HasProjectiveLineDerivAt (fun y => (f y).1) a x v)
      (hb : HasProjectiveLineDerivAt (fun y => (f y).2) b x v) : D v = (a, b) := by
    apply Prod.ext
    · exact ((hD v).clm_comp (ContinuousLinearMap.fst ℝ F G)).unique ha
    · exact ((hD v).clm_comp (ContinuousLinearMap.snd ℝ F G)).unique hb
  have hd := hD (v₁ + v₂ + v₃ + v₄)
  rw [map_add, map_add, map_add,
    identify h₁ k₁, identify h₂ k₂, identify h₃ k₃, identify h₄ k₄] at hd
  exact hd

/-- The scalar and circle rows cancel exactly after the recovered columns
have been identified. The two error entries remain independent values. -/
theorem coupled_derivative_of_corrected_columns
    {f : E → F × G} {U : Set E} (J : SmoothDirections U f)
    {x vη vν vκ vψ : E} (hx : x ∈ U)
    (y e : F × G) (K N : F) (H C : G)
    (hη : HasProjectiveLineDerivAt (fun u => (f u).1)
      (y.1 - K - N + e.1) x vη)
    (hν : HasProjectiveLineDerivAt (fun u => (f u).1) N x vν)
    (hκ : HasProjectiveLineDerivAt (fun u => (f u).1) K x vκ)
    (hψ : HasProjectiveLineDerivAt (fun u => (f u).1) 0 x vψ)
    (kη : HasProjectiveLineDerivAt (fun u => (f u).2) H x vη)
    (kν : HasProjectiveLineDerivAt (fun u => (f u).2) 0 x vν)
    (kκ : HasProjectiveLineDerivAt (fun u => (f u).2) C x vκ)
    (kψ : HasProjectiveLineDerivAt (fun u => (f u).2)
      (y.2 - H - C + e.2) x vψ) :
    HasProjectiveLineDerivAt f (y + e) x (vη + vν + vκ + vψ) := by
  have hd := coupled_derivative_of_four_columns J hx hη hν hκ hψ kη kν kκ kψ
  have he : ((y.1 - K - N + e.1) + N + K + 0,
      H + 0 + C + (y.2 - H - C + e.2)) = y + e := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  rw [he] at hd
  exact hd

end FirstJet

/-- Recovery can be checked by applying the scalar solver to one source
difference. No linearity of the expression `A` is needed. -/
theorem coupled_scalar_recovery_algebra
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (G : F →ₗ[ℝ] E × ℝ) (decode : F →ₗ[ℝ] ℝ)
    (A : E → ℝ) (ν : ℝ)
    (hG : ∀ f : F, A (G f).1 + (G f).2 * ν = decode f)
    {f K : F} {η : E} {μ : ℝ}
    (hrecover : (η, μ) = G f - G K) :
    A η + μ * ν + decode K = decode f := by
  have hvalue : G (f - K) = (η, μ) := (map_sub G f K).trans hrecover.symm
  have hsolve := hG (f - K)
  rw [hvalue, map_sub] at hsolve
  linarith only [hsolve]

private theorem coupled_scalar_completion_algebra
    {original corrected error correction nu control source totalError : ℝ}
    (hsolve : corrected + nu + control = source)
    (hcompletion : original - corrected = correction)
    (herror : totalError = error + correction) :
    original + error + nu + control = source + totalError := by
  linarith only [hsolve, hcompletion, herror]

private theorem coupled_fill_circle_row {E : Type*} [AddCommGroup E]
    (height control source inverse : E)
    (hinverse : inverse = source - height - control) :
    height + control + inverse = source := by
  rw [hinverse]
  abel

private theorem coupled_lineDerivAt_replace
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {f : E → F} {df dg : F} {x v w : E}
    (h : HasProjectiveLineDerivAt f df x v) (hd : df = dg) (hv : v = w) :
    HasProjectiveLineDerivAt f dg x w := hd ▸ hv ▸ h

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- Evaluation of the actual source, with the kernel inclusion made explicit. -/
def coupledSourceEvaluation (S : PhysicalSpacesData) (p : PolarPoint) :
    S.Source →ₗ[ℝ] ℝ :=
  (LinearMap.proj p).comp
    ((S.height (3 / 4 : ℝ)).decode.comp S.Q.toLinearMap.ker.subtype)

theorem coupledSourceEvaluation_apply (S : PhysicalSpacesData)
    (p : PolarPoint) (f : S.Source) :
    coupledSourceEvaluation S p f = (S.height (3 / 4 : ℝ)).decode f.val p := rfl

/-- The first recovered row is the genuine corrected scalar equation. -/
theorem coupled_corrected_scalar_equation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {B : ControlColumnData S} {N : ControlInverseData S} {V : CoupledInverseData S}
    {base : ℕ} {ε q0 : ℝ}
    (hG : ScalarInverseProperties D S C L G base ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (L.coefficients z) (heightPairField S (V.V z y).1) p +
      (V.V z y).2.1 * nuColumnField D S C z p +
      (S.height (3 / 4 : ℝ)).decode
        (B.heightColumn z (controlSolution S B G N z y)).val p =
      (S.height (3 / 4 : ℝ)).decode y.1.val p := by
  have hnear : z ∈ stateNeighborhood S C base ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
  exact coupled_scalar_recovery_algebra (G.G z).toLinearMap
    (coupledSourceEvaluation S p)
    (fun η => divergenceOperator (L.coefficients z) (heightPairField S η) p)
    (nuColumnField D S C z p)
    (fun f => (hG.1 z hnear hs f).2 p hp)
    ((h9.2.2.2.2.1 z hz hs y).2.2.1)

/-- The return correction and the realized scalar error convert the first
recovered row to the exact original-operator identity. -/
theorem coupled_scalar_equation_with_return_error
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {G : ScalarInverseData S}
    {B : ControlColumnData S} {N : ControlInverseData S} {V : CoupledInverseData S}
    {base : ℕ} {ε q0 : ℝ}
    (h3 : N03Properties D T S C R L base ε)
    (hG : ScalarInverseProperties D S C L G base ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    (e : S.Source) (E : PolarPoint → ℝ)
    (he : ∀ p ∈ annularOpen D,
      (S.height (3 / 4 : ℝ)).decode e.val p = E p +
        (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) (V.V z y).1).val) p)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C z) (heightPairField S (V.V z y).1) p +
      E p + (V.V z y).2.1 * nuColumnField D S C z p +
      (S.height (3 / 4 : ℝ)).decode
        (B.heightColumn z (controlSolution S B G N z y)).val p =
      (S.height (3 / 4 : ℝ)).decode (y.1 + e).val p := by
  have hnear : z ∈ stateNeighborhood S C base ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
  have hsolve := coupled_corrected_scalar_equation
    (D := D) (T := T) (S := S) (C := C) (R := R) (L := L) (G := G)
    (B := B) (N := N) (V := V) hG h9 hz hs y hp
  have hcompletion :
      divergenceOperator (originalCoefficients D S C z) (heightPairField S (V.V z y).1) p -
        divergenceOperator (L.coefficients z) (heightPairField S (V.V z y).1) p =
          (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) (V.V z y).1).val) p :=
    h3.2.2.2.2.2.1 z hnear hs (V.V z y).1 p hp
  have herror := he p hp
  have hadd : (S.height (3 / 4 : ℝ)).decode (y.1 + e).val p =
      (S.height (3 / 4 : ℝ)).decode y.1.val p +
        (S.height (3 / 4 : ℝ)).decode e.val p :=
    (coupledSourceEvaluation S p).map_add y.1 e
  exact (coupled_scalar_completion_algebra hsolve hcompletion herror).trans hadd.symm

/-- The inverse of the zero-mean circle row exactly fills the remaining
source after the height and control columns have been removed. -/
theorem coupled_corrected_circle_equation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {G : ScalarInverseData S}
    {B : ControlColumnData S} {N : ControlInverseData S} {V : CoupledInverseData S}
    {base : ℕ} {ε q0 : ℝ}
    (h2 : N02Properties D T S C R base ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S) :
    let w := V.V z y
    let f := y.2.val - z.2 • B.heightRow z w.1 - B.circleColumn z w.2.2.1
    z.2 • B.heightRow z w.1 + B.circleColumn z w.2.2.1 +
      R.linearPart (R.inverse f) = y.2.val := by
  let w := V.V z y
  let f := y.2.val - z.2 • B.heightRow z w.1 - B.circleColumn z w.2.2.1
  have hf : IsEvenZeroMeanCircle S f := (h9.2.2.2.2.1 z hz hs y).2.2.2.1
  have hi : R.linearPart (R.inverse f) = f := (h2.2.2.2.2.2.2.2.1 f hf).1
  change z.2 • B.heightRow z w.1 + B.circleColumn z w.2.2.1 +
    R.linearPart (R.inverse f) = y.2.val
  exact coupled_fill_circle_row (z.2 • B.heightRow z w.1)
    (B.circleColumn z w.2.2.1) y.2.val (R.linearPart (R.inverse f)) hi

/-- The chart direction in the recovered state is precisely the one to
which the true N02 return-derivative formula applies. -/
theorem coupled_recovered_chart_derivative
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {G : ScalarInverseData S}
    {B : ControlColumnData S} {N : ControlInverseData S} {V : CoupledInverseData S}
    {base : ℕ} {ε q0 : ℝ}
    (h2 : N02Properties D T S C R base ε)
    (h9 : N09Properties D T S C R G B N V base ε q0)
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S) :
    let w := V.V z y
    let f := y.2.val - z.2 • B.heightRow z w.1 - B.circleColumn z w.2.2.1
    HasProjectiveLineDerivAt (fun x => R.residual (x, z.2))
      (f + R.error z (R.residual z) (R.inverse f))
      z.1 (0, (0, (0, w.2.2.2))) := by
  let w := V.V z y
  let f := y.2.val - z.2 • B.heightRow z w.1 - B.circleColumn z w.2.2.1
  have hr := h9.2.2.2.2.1 z hz hs y
  have hf : IsEvenZeroMeanCircle S f := hr.2.2.2.1
  have hinv := h2.2.2.2.2.2.2.2.1 f hf
  have hnear : z ∈ stateNeighborhood S C base ε := ⟨hz.1, hz.2.trans_le h9.2.1⟩
  have hd := h2.2.2.2.2.2.2.1 z hnear hs (R.inverse f) hinv.2
  have hchart : w.2.2.2 = R.chartIncrement z (R.inverse f) := hr.2.2.2.2.1
  have hvalue : R.linearPart (R.inverse f) + R.error z (R.residual z) (R.inverse f) =
      f + R.error z (R.residual z) (R.inverse f) :=
    congrArg (fun a : CircleSpace S => a + R.error z (R.residual z) (R.inverse f)) hinv.1
  have hdirection : ((0, (0, (0, R.chartIncrement z (R.inverse f)))) : AnnularState S) =
      (0, (0, (0, w.2.2.2))) :=
    congrArg (fun a : CircleSpace S => (0, (0, (0, a))) : CircleSpace S → AnnularState S)
      hchart.symm
  exact coupled_lineDerivAt_replace hd hvalue hdirection

end ContinuousFlexibility.Statements
