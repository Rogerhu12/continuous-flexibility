import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeight
import ContinuousFlexibility.Analysis.N04RealizationBoundaryTaylorDirections
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition
import ContinuousFlexibility.Analysis.N01cAngularJetTowers

/-!
# Genuine joint towers of the stored positive height and reciprocal

The finite raw source-height traces determine their actual logarithmic
traces by the ordinary partition formula. The existing Taylor polynomial,
fixed cutoffs and exponential then construct the stored height on the
whole state-spatial product. The constant logarithmic coefficient is
retained, without normalizing the source height to one.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

def n04PositiveGeometry_logBoundaryTrace_jointDirections
    {U : Set V} (hU : IsOpen U) (c : ℝ) (n : ℕ) (f : V → PolarPoint → ℝ)
    (hf : ∀ x ∈ U, ∀ θ, ContDiffAt ℝ ∞ (f x) (c, θ))
    (hpos : ∀ x ∈ U, ∀ θ, 0 < f x (c, θ))
    (J : ∀ j : ℕ, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (f y.1) c j y.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (fun p => Real.log (f y.1 p)) c n y.2) := by
  classical
  let index : (π : OrderedFinpartition n) → Fin π.length → Fin (n + 1) :=
    fun π i => ⟨π.partSize i, Nat.lt_succ_of_le (π.partSize_le i)⟩
  let Ω : Set (Fin (n + 1) → ℝ) := {v | 0 < v 0}
  let F : (Fin (n + 1) → ℝ) → ℝ := fun v =>
    ∑ π : OrderedFinpartition n,
      iteratedDeriv π.length Real.log (v 0) * ∏ i, v (index π i)
  have hΩ : IsOpen Ω := isOpen_Ioi.preimage (continuous_apply 0)
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    fun t ht => (Real.contDiffAt_log.mpr ht.ne').contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F Ω := by
    apply ContDiffOn.sum
    intro π _
    have houter : ContDiffOn ℝ ∞
        (fun v : Fin (n + 1) → ℝ => iteratedDeriv π.length Real.log (v 0)) Ω :=
      (contDiffOn_iteratedDeriv_open isOpen_Ioi hlog π.length).comp
        (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).contDiffOn (fun _ hy => hy)
    exact houter.mul (contDiffOn_prod (fun i _ =>
      (contDiff_apply ℝ ℝ (index π i)).contDiffOn))
  let JT := smoothDirections_scalarTuple (hU.prod isOpen_univ)
    (fun j : Fin (n + 1) => J j.val (Nat.le_of_lt_succ j.isLt))
  have hmap : MapsTo (fun y : V × ℝ => fun j : Fin (n + 1) =>
      radialBoundaryJet (f y.1) c j.val y.2) (U ×ˢ univ) Ω := by
    intro y hy
    change 0 < radialBoundaryJet (f y.1) c 0 y.2
    simpa only [radialBoundaryJet, iteratedDeriv_zero] using hpos y.1 hy.1 y.2
  exact (JT.comp_contDiff hΩ hF hmap).congr (fun y hy => by
    simpa only [F, index, Fin.val_zero, radialBoundaryJet, iteratedDeriv_zero] using
      (n04Realization_log_radialBoundaryJet (hf y.1 hy.1 y.2) (hpos y.1 hy.1 y.2) n).symm)

def n04PositiveGeometry_endpointTaylorCorrection_jointDirections
    {U : Set V} (hU : IsOpen U) (n : ℕ) (l r δ : ℝ)
    (A : V → Bool → ℕ → ℝ → ℝ)
    (J : ∀ side, ∀ j : ℕ, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => A y.1 side j y.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun y : V × PolarPoint => endpointTaylorCorrection n l r δ (A y.1) y.2) := by
  let L : (V × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ V PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun y : V × PolarPoint => y.2.1) :=
    (smoothDirectionsLinearOn L (hU.prod isOpen_univ)).congr (fun y _ => by
      simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd'])
  let JC (side : Bool) := JR.comp_contDiff isOpen_univ
    (contDiff_positiveEndpointCutoff (if side then r else l) δ).contDiffOn
    (fun _ _ => mem_univ _)
  let JP (side : Bool) := n04Realization_boundaryTaylor_jointDirections hU n
    (if side then r else l) (fun x => A x side)
    (fun j => J side j.val (Nat.le_of_lt_succ j.isLt))
  exact smoothDirectionsAdd ((JC false).mul (JP false)) ((JC true).mul (JP true))

/-- Both reciprocal choices come from the same genuine finite source
trace tower; only ordinary scalar kernels are used after those traces. -/
def n04PositiveGeometry_positiveHeightTaylor_jointDirections
    {U : Set V} (hU : IsOpen U) (n : ℕ) (l r δ : ℝ)
    (h : V → Bool → PolarPoint → ℝ)
    (hroot : ∀ x ∈ U, ∀ side θ,
      ContDiffAt ℝ ∞ (h x side) (if side then r else l, θ))
    (hpos : ∀ x ∈ U, ∀ side θ, 0 < h x side (if side then r else l, θ))
    (J : ∀ side, ∀ j : ℕ, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (h y.1 side) (if side then r else l) j y.2))
    (inv : Bool) :
    SmoothDirections (U ×ˢ univ) (fun y : V × PolarPoint => if inv then
      (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y.1) y.2)⁻¹
      else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h y.1) y.2) := by
  let A : V → Bool → ℕ → ℝ → ℝ :=
    fun x => positiveHeightTaylorData l r (fun _ => 1) (h x)
  let JA (side : Bool) (j : ℕ) (hj : j ≤ n) : SmoothDirections (U ×ˢ univ)
      (fun y : V × ℝ => A y.1 side j y.2) :=
    (n04PositiveGeometry_logBoundaryTrace_jointDirections hU (if side then r else l) j
      (fun x => h x side) (fun x hx => hroot x hx side) (fun x hx => hpos x hx side)
      (fun a ha => J side a (ha.trans hj))).congr (fun y _ => by
        simp only [A, positiveHeightTaylorData, boundaryHeightLogRatio, div_one])
  let JT := n04PositiveGeometry_endpointTaylorCorrection_jointDirections hU n l r δ A JA
  have houter : ContDiff ℝ ∞ (fun t : ℝ => if inv then Real.exp (-t) else Real.exp t) := by
    cases inv
    · exact Real.contDiff_exp
    · exact Real.contDiff_exp.comp contDiff_neg
  exact (JT.comp_contDiff isOpen_univ houter.contDiffOn
    (fun _ _ => mem_univ _)).congr (fun y _ => by
      cases inv <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        positiveHeightTaylorInterpolation, one_mul, Real.exp_neg, A])

/-- The stored control-family height itself, jointly in its original
parameter and spatial variables. Its existing mixed and material bounds
can be used unchanged with this tower. -/
def n04PositiveGeometry_controlledHeight_jointDirections
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    {U : Set V} (hU : IsOpen U) (state : V → AnnularState W.S × ℝ)
    (hstate : ∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hsector : ∀ x ∈ U, stateSector W.S (state x).1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JH : ∀ side, ∀ j : ℕ, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (n04PositiveSourceHeight (X.src i side)
        (W.A X.e₀) (state y.1)) (n04PositiveEndpoint i side) j y.2)) (inv : Bool) :
    SmoothDirections (U ×ˢ univ) (fun y : V × PolarPoint => if inv then
      (G.toN04PositiveGeometryControlData.Q (state y.1) i y.2)⁻¹
      else G.toN04PositiveGeometryControlData.Q (state y.1) i y.2) := by
  have hroot (x : V) (hx : x ∈ U) (side : Bool) (θ : ℝ) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source W.hT W.hS W.through03 W.field
      X.e₀ (X.src i side) (stateNeighborhood_mono W.S W.C G.base_le G.radius_le (hstate x hx))
      (hsector x hx)).height_root θ
  exact n04PositiveGeometry_positiveHeightTaylor_jointDirections hU n
    (n04PositiveLeft i) (n04PositiveRight i) (G.δ i)
    (fun x side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state x))
    (fun x hx side θ => (hroot x hx side θ).1)
    (fun x hx side θ => (hroot x hx side θ).2) JH inv

/-- The same raw joint towers supply the already established mixed-jet
and quantitative interface, with no replacement of its constants. -/
def n04PositiveGeometry_controlledHeight_jointRaw_mixedJetRegularity
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    {U : Set V} (hU : IsOpen U) (state : V → AnnularState W.S × ℝ)
    (hstate : ∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hsector : ∀ x ∈ U, stateSector W.S (state x).1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JH : ∀ side, ∀ j : ℕ, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (n04PositiveSourceHeight (X.src i side)
        (W.A X.e₀) (state y.1)) (n04PositiveEndpoint i side) j y.2)) (inv : Bool) :
    MixedJetRegularity U univ (fun x q => if inv then
      (G.toN04PositiveGeometryControlData.Q (state x) i q)⁻¹
      else G.toN04PositiveGeometryControlData.Q (state x) i q) :=
  n04PositiveGeometry_controlledHeight_mixedJetRegularity G hU state hstate hsector i
    (fun side j hj b θ => smoothDirections_angularStateSlice (JH side j hj) b θ) inv

end ContinuousFlexibility.Analysis
