import ContinuousFlexibility.Analysis.N06TurningRootDensity
import ContinuousFlexibility.Analysis.N06BoundaryRadialOrientation

/-!
# The actual positive boundary normal row

The original order-zero N04 estimate bounds the divided coefficients on
each entire open canonical piece. Their cubic factor therefore vanishes
along the true forward chart at either canonical endpoint. Continuity of
the actual physical principal density, obtained from the N03 germs on the
closed positive piece, identifies its normal row with the reference row.

The interior principal-density identity is stated explicitly for the true
forward chart. It is the operator-identification interface, not a boundary
row assumption. No value of the totalized canonical coefficients or inverse
chart at an endpoint enters the result.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- A bounded divided coefficient is killed by a cubic factor tending
to zero. No continuity of that divided coefficient is needed. -/
theorem n06_tendsto_cube_mul_of_bounded
    {ι : Type*} {l : Filter ι} {d f : ι → ℝ} {Q : ℝ}
    (hd : Tendsto d l (𝓝 0)) (hf : ∀ᶠ q in l, |f q| ≤ Q) :
    Tendsto (fun q => d q ^ 3 * f q) l (𝓝 0) := by
  have hmajor : Tendsto (fun q => |d q| ^ 3 * Q) l (𝓝 0) := by
    simpa only [abs_zero, zero_pow (by decide : 3 ≠ 0), zero_mul] using
      (hd.abs.pow 3).mul_const Q
  apply squeeze_zero_norm' ?_ hmajor
  filter_upwards [hf] with q hq
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left hq (pow_nonneg (abs_nonneg _) _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- The actual divided coefficients are bounded on the whole open piece
by the original N04 estimate. This is a fixed-piece statement and makes
no claim of a new uniform material constant. -/
theorem n06_actual_dividedCoefficients_bounded
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ p ∈ canonicalOpen S K m,
      |(K.dividedDifference z m).a p| ≤ Q ∧
        |(K.dividedDifference z m).b p| ≤ Q ∧
        |(K.dividedDifference z m).c p| ≤ Q := by
  obtain ⟨B, _, hB⟩ := h04.2.2.1 0
  let Q := B * T.E0 (T.sample (K.cell m)) ^ B *
    (1 + stateGrading S loss (z.1 - C.referenceState) + |z.2|)
  refine ⟨|Q|, abs_nonneg Q, fun p hp => ?_⟩
  have hb := hB z hz m p hp 0 0 (by norm_num)
  simp only [mixedDerivative, iteratedDeriv_zero, Nat.zero_add] at hb
  have hsum : |K.potential z m p| + |(K.dividedDifference z m).a p| +
      |(K.dividedDifference z m).b p| + |(K.dividedDifference z m).c p| ≤ Q := hb
  have ha : |(K.dividedDifference z m).a p| ≤ Q := by
    linarith only [hsum, abs_nonneg (K.potential z m p),
      abs_nonneg ((K.dividedDifference z m).b p), abs_nonneg ((K.dividedDifference z m).c p)]
  have hb' : |(K.dividedDifference z m).b p| ≤ Q := by
    linarith only [hsum, abs_nonneg (K.potential z m p),
      abs_nonneg ((K.dividedDifference z m).a p), abs_nonneg ((K.dividedDifference z m).c p)]
  have hc : |(K.dividedDifference z m).c p| ≤ Q := by
    linarith only [hsum, abs_nonneg (K.potential z m p),
      abs_nonneg ((K.dividedDifference z m).a p), abs_nonneg ((K.dividedDifference z m).b p)]
  exact ⟨ha.trans (le_abs_self Q), hb'.trans (le_abs_self Q), hc.trans (le_abs_self Q)⟩

/-- A true positive endpoint has the reference normal row. The limit
uses the actual forward chart, original cubic bound and original N03
physical germs. The explicit interior identity is the one recovered from
the N04 operator on polynomial probes. -/
theorem n06_positive_boundary_normalDensity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) {a : ℝ → ℝ} (ha : Continuous a)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hprincipal : ∀ q ∈ physicalPieceOpen S K z m,
      (K.coefficients z m).a (K.chart z m q) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a q ∧
      (K.coefficients z m).b (K.chart z m q) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b q)
    (canonicalUpper : Bool) {x : PolarPoint}
    (hx : x ∈ physicalPieceClosed S K z m)
    (hp : x ∈ annularOpen D)
    (hboundary : (K.chart z m x).1 = n06Endpoint (K.left m) (K.right m) canonicalUpper) :
    (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a x =
        a (n06Endpoint (K.left m) (K.right m) canonicalUpper) ∧
      (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b x = 0 := by
  let P := coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)
  let d (q : PolarPoint) := ((K.chart z m q).1 - K.left m) *
    (K.right m - (K.chart z m q).1)
  have hΩ := n06_positivePhysicalPiece_eq_reference h04.1 hz hs m hm
  have hxrad : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) := by
    have hx' := hx
    rw [n06_physicalPieceClosed_eq_reference_rectangle h04.1 m hΩ] at hx'
    exact hx'.1
  have hreg := n06_correctedCoefficients_contDiffAt_of_nonneg hT hS h01 h03 hz hs hp
    (n06_positivePiece_closed_slope_nonneg h01 h04 m hm hxrad)
  have hclosed := (h04.1.boundary z hz hs m).2.2.2.2.1 x hx
  have hcont : ContinuousAt P.a x ∧ ContinuousAt P.b x :=
    n06_coordinatePrincipalDensity_normal_continuousAt
      hreg.1.continuousAt hreg.2.1.continuousAt hreg.2.2.continuousAt
      hclosed.1 hclosed.2.1.continuousAt hclosed.2.2.1
  have hmap := (h04.1.charts z hz hs m).1
  haveI : NeBot (𝓝[physicalPieceOpen S K z m] x) :=
    mem_closure_iff_nhdsWithin_neBot.mp hx
  have hzero : d x = 0 := by
    dsimp only [d]
    rw [hboundary]
    cases canonicalUpper <;> simp [n06Endpoint]
  have hd : Tendsto d (𝓝[physicalPieceOpen S K z m] x) (𝓝 0) := by
    have hdy : ContinuousAt (fun q => (K.chart z m q).1) x := hclosed.1.continuousAt.fst
    have hc : ContinuousAt d x :=
      (hdy.sub continuousAt_const).mul (continuousAt_const.sub hdy)
    simpa only [hzero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨Q, _, hbound⟩ := n06_actual_dividedCoefficients_bounded h04 hz m
  have hboundA : ∀ᶠ q in 𝓝[physicalPieceOpen S K z m] x,
      |(K.dividedDifference z m).a (K.chart z m q)| ≤ Q := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hbound _ (hmap hq)).1
  have hboundB : ∀ᶠ q in 𝓝[physicalPieceOpen S K z m] x,
      |(K.dividedDifference z m).b (K.chart z m q)| ≤ Q := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hbound _ (hmap hq)).2.1
  have hprodA := n06_tendsto_cube_mul_of_bounded hd hboundA
  have hprodB := n06_tendsto_cube_mul_of_bounded hd hboundB
  have hrow : ∀ᶠ q in 𝓝[physicalPieceOpen S K z m] x,
      P.a q - a (K.chart z m q).1 = d q ^ 3 * (K.dividedDifference z m).a (K.chart z m q) ∧
      P.b q = d q ^ 3 * (K.dividedDifference z m).b (K.chart z m q) := by
    have hcubic := h04.2.1.2.2.2.2
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hqC := hmap hq
    have he := hcubic z hz hs m hm (K.chart z m q) hqC
    rw [(hprincipal q hq).1, (hprincipal q hq).2, hea hqC, heb hqC, sub_zero] at he
    exact ⟨he.1, he.2.1⟩
  have hdiff : Tendsto (fun q => P.a q - a (K.chart z m q).1)
      (𝓝[physicalPieceOpen S K z m] x) (𝓝 0) :=
    hprodA.congr' (hrow.mono (fun _ hq => hq.1.symm))
  have hbzero : Tendsto P.b (𝓝[physicalPieceOpen S K z m] x) (𝓝 0) :=
    hprodB.congr' (hrow.mono (fun _ hq => hq.2.symm))
  have haF : ContinuousAt (fun q => a (K.chart z m q).1) x :=
    ContinuousAt.comp (f := fun q : PolarPoint => (K.chart z m q).1) (x := x)
      ha.continuousAt hclosed.1.continuousAt.fst
  have heqa : P.a x - a (K.chart z m x).1 = 0 :=
    tendsto_nhds_unique ((hcont.1.sub haF).tendsto.mono_left nhdsWithin_le_nhds) hdiff
  have heqb : P.b x = 0 :=
    tendsto_nhds_unique (hcont.2.tendsto.mono_left nhdsWithin_le_nhds) hbzero
  rw [hboundary] at heqa
  exact ⟨sub_eq_zero.mp heqa, heqb⟩

/-- The actual boundary density in the existing root cancellation
theorem is therefore the positive weighted Wronskian. This does not
evaluate a recorded canonical coefficient at the endpoint. -/
theorem n06_positive_root_boundaryDensity
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = true) {a : ℝ → ℝ} (ha : Continuous a)
    (hea : EqOn (K.coefficients (C.referenceState, 0) m).a
      (fun p => a p.1) (canonicalOpen S K m))
    (heb : EqOn (K.coefficients (C.referenceState, 0) m).b
      (fun _ => 0) (canonicalOpen S K m))
    (hprincipal : ∀ q ∈ physicalPieceOpen S K z m,
      (K.coefficients z m).a (K.chart z m q) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).a q ∧
      (K.coefficients z m).b (K.chart z m q) =
        (coordinatePrincipalDensity (L.coefficients z) (K.chart z m) (K.height z m)).b q)
    (canonicalUpper : Bool) {r σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r
      (n06Endpoint (K.left m) (K.right m) canonicalUpper) σ β H ρ κ Hr)
    (hx : ∀ θ : ℝ, (r, θ) ∈ physicalPieceClosed S K z m)
    (hp : r ∈ Ioo D.a D.b) (θ : ℝ) (Q Qr Qt W : PolarPoint → ℝ) :
    n06RootBoundaryDensity (L.coefficients z) (K.chart z m) (K.height z m)
      Q Qr Qt W (r, θ) (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) =
      a (n06Endpoint (K.left m) (K.right m) canonicalUpper) *
        (Q (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) *
          radialPartial W (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) -
        W (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ) *
          Qr (n06Endpoint (K.left m) (K.right m) canonicalUpper, β θ)) := by
  have hboundary : (K.chart z m (r, θ)).1 =
      n06Endpoint (K.left m) (K.right m) canonicalUpper :=
    congrArg Prod.fst (J.chart_value θ)
  have hrow := n06_positive_boundary_normalDensity hT hS h01 h03 h04 hz hs hm ha hea heb
    hprincipal canonicalUpper (hx θ) ⟨hp, mem_univ _⟩ hboundary
  simp only [n06RootBoundaryDensity, hrow.1, hrow.2, zero_mul, add_zero]

end ContinuousFlexibility.Statements
