module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledTransportWords
public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledCoefficientSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceAngleSamplePrefix
public import ContinuousFlexibility.Analysis.N04PositiveGeometryTransportSamplePrefix

/-!
# The common sample prefix of the actual positive transports

The angular and radial packets use one low order. Their shifts are
aligned by increasing the angular horizon before composition, so the
normalized denominator remains identical throughout. The final added
shift pays precisely for boundary coefficients becoming plane fields.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements

private theorem transport_high_order_le {a low sa ca s c K : ℕ}
    (h : a ≤ low) (he : sa + ca * K = s + c * K) :
    a + sa + ca * K + 1 ≤ low + s + c * K + 1 := by
  omega

private theorem transportSavedWords_boolChoice
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} {f g : E × PolarPoint → PolarPoint}
    (Jf : SmoothDirections (U ×ˢ univ) f)
    (Jg : SmoothDirections (U ×ˢ univ) g)
    {N K C : ℕ} {x : E} {Ω : Set PolarPoint}
    {p q : Seminorm ℝ E} {R M H t : ℝ}
    (hx : x ∈ U)
    (hf : N04PlaneSavedWordBounds Jf N K C x Ω p q R M H t)
    (hg : N04PlaneSavedWordBounds Jg N K C x Ω p q R M H t)
    (inverse : Bool)
    (Q : SmoothDirections (U ×ˢ univ) (fun z => if inverse then g z else f z)) :
    N04PlaneSavedWordBounds Q N K C x Ω p q R M H t := by
  cases inverse with
  | false => exact hf.congr hx Q (fun _ _ => rfl)
  | true => exact hg.congr hx Q (fun _ _ => rfl)

theorem n04PositiveGeometry_actualControlledTransport_sample_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (G : N04PositiveGeometryControlledFamily W X 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (F : ∀ i, N04PositiveGeometryFactorData G base ε i) :
    ∀ inverse : Bool, N04PositiveGeometryTransportSamplePrefix G inverse base ε := by
  classical
  let angleData := n04PositiveGeometry_sourceAngleTrace_sample_prefix W X hb hε hεW hεone hflow
  let radialData := n04PositiveGeometry_controlledCoefficient_sample_prefix
    G hb hε hεW hεone hGb hGε hflow
  let low : ℕ := max angleData.choose radialData.choose
  have hal : angleData.choose ≤ low := le_max_left _ _
  have hrl : radialData.choose ≤ low := le_max_right _ _
  have hblow : base ≤ low := angleData.choose_spec.1.trans hal
  let U := sectorNeighborhood W.S base ε ε
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp := sectorPairGrading_monotone W.S
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let RH := heightData.choose
  let src (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :=
    n04PositiveGeometry_source_some W X i side
  let m (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) : ℕ :=
    (src i side).choose
  have hm (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) :
      (X.src i side).val = some (m i side) := (src i side).choose_spec
  let Jψ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (j : Fin 5) :=
    n04PositiveGeometry_sourceAngleTrace_joint hb hε hεW hεone hflow i side
      (m i side) (hm i side) (hctx (m i side) (!side)) j (by omega)
  let JA (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
      SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ =>
          G.toN04PositiveGeometryControlData.angularCoefficients
            (liftSectorParameter W.S W.C z.1) i z.2) :=
    smoothDirectionsScalarPi (hU.prod isOpen_univ)
      (fun side => smoothDirectionsScalarPi (hU.prod isOpen_univ) (Jψ i side))
  let JR (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
      SmoothDirections (U ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ => fun side (j : Fin 4) =>
          G.toN04PositiveGeometryControlData.coefficients
            (liftSectorParameter W.S W.C z.1) i side (j + 1) z.2) :=
    smoothDirectionsScalarPi (hU.prod isOpen_univ)
      (fun side => smoothDirectionsScalarPi (hU.prod isOpen_univ) ((F i).coefficients side))
  intro inverse
  refine ⟨low, hblow, fun K => ?_⟩
  let asd := angleData.choose_spec.2 K
  let rsd := radialData.choose_spec.2 K
  let c : ℕ := max asd.choose rsd.choose
  let shift : ℕ := c + 1
  have hac : asd.choose ≤ c := le_max_left _ _
  have hrc : rsd.choose ≤ c := le_max_right _ _
  refine ⟨shift, fun s => ?_⟩
  let sa : ℕ := s + (shift - asd.choose) * K
  let sr : ℕ := s + (shift - rsd.choose) * K
  have has : s + K ≤ sa := by
    have h := Nat.mul_le_mul_right K (show 1 ≤ shift - asd.choose by dsimp only [shift]; omega)
    dsimp only [sa]
    omega
  have hrs : s + K ≤ sr := by
    have h := Nat.mul_le_mul_right K (show 1 ≤ shift - rsd.choose by dsimp only [shift]; omega)
    dsimp only [sr]
    omega
  have hea : sa + asd.choose * K = s + shift * K := by
    dsimp only [sa]
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel (by dsimp only [shift]; omega)]
  have her : sr + rsd.choose * K = s + shift * K := by
    dsimp only [sr]
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel (by dsimp only [shift]; omega)]
  let ad := asd.choose_spec sa
  let rd := rsd.choose_spec sr
  let A : ℝ := max ad.choose rd.choose
  have hA : 1 ≤ A := ad.choose_spec.1.trans (le_max_left _ _)
  let outputData := n04PositiveGeometry_controlledTransports_saved_prefix
    G (K + s + 1) A RH hA
  let B := outputData.choose
  refine ⟨B, outputData.choose_spec.1, ?_⟩
  intro i Q x hx hxlow y hy R hR hxR j hj hjN w hw v hpure hbox
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let high : ℕ := low + s + shift * K + 1
  let P := fun z => p low z ≤ 1 ∧ p high z ≤ R
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHR : H ≤ RH := (heightData.choose_spec.2 i).2
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hM : 0 ≤ A * E ^ A := mul_nonneg (zero_le_one.trans hA)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hcost {a : ℝ} (ha : a ≤ A) : a * E ^ a ≤ A * E ^ A :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hha : angleData.choose + sa + asd.choose * K + 1 ≤ high :=
    transport_high_order_le hal hea
  have hhr : radialData.choose + sr + rsd.choose * K + 1 ≤ high :=
    transport_high_order_le hrl her
  have hangle (θ : ℝ) : N04BoundaryWordBounds (JA i) K (s + K) 1 x θ P
      (A * E ^ A) H t c := by
    apply N04BoundaryWordBounds.scalarPi hU _ hM hH (zero_le_one.trans ht)
    intro side
    apply N04BoundaryWordBounds.scalarPi hU _ hM hH (zero_le_one.trans ht)
    intro k
    have raw := ad.choose_spec.2 i side (m i side) (hm i side) (hctx (m i side) (!side))
      k (by omega) (Jψ i side k) x hx ((hp hal x).trans hxlow) θ R hR
      ((hp hha x).trans hxR)
    exact raw.mono_budget le_rfl has
      (fun z hz => ⟨(hp hal z).trans hz.1, (hp hha z).trans hz.2⟩)
      hM hH ht (hcost (le_max_left _ _))
      (congrArg (fun q : ℕ => R ^ (1 / ((q : ℝ) + 1))) hea) hac
  have hradial (θ : ℝ) : N04BoundaryWordBounds (JR i) K (s + K) 1 x θ P
      (A * E ^ A) H t c := by
    apply N04BoundaryWordBounds.scalarPi hU _ hM hH (zero_le_one.trans ht)
    intro side
    apply N04BoundaryWordBounds.scalarPi hU _ hM hH (zero_le_one.trans ht)
    intro k
    have raw := rd.choose_spec.2 i side (m i side) (hm i side) (hctx (m i side) (!side))
      (k + 1) (by omega) (by omega) ((F i).coefficients side k)
      x hx ((hp hrl x).trans hxlow) θ R hR ((hp hhr x).trans hxR)
    exact raw.mono_budget le_rfl hrs
      (fun z hz => ⟨(hp hrl z).trans hz.1, (hp hhr z).trans hz.2⟩)
      hM hH ht (hcost (le_max_right _ _))
      (congrArg (fun q : ℕ => R ^ (1 / ((q : ℝ) + 1))) her) hrc
  have hout := outputData.choose_spec.2 base ε hGb hGε i (F i) (JA i) (JR i)
    (p low) (p high) R H t (zero_le_one.trans hR) hH hHR ht K s c le_rfl x hx hangle hradial
  have hactual : N04PlaneSavedWordBounds Q (K + s + 1) K shift x
      (Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ)
      (p low) (p high) R (B * E ^ B) H t :=
    transportSavedWords_boolChoice (F i).transport (F i).inverseTransport
      hx hout.1 hout.2 inverse Q
  exact hactual y ⟨⟨hy.1.1.le, hy.1.2.le⟩, mem_univ _⟩ j hj hjN w hw v hpure hbox

end ContinuousFlexibility.Analysis
