import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightTraceJets
import ContinuousFlexibility.Analysis.N04RealizationFixedSpatialProduct
import ContinuousFlexibility.Analysis.CanonicalFixedPositiveFamily

/-!
# The actual finite positive height and its reciprocal parameter towers

The existing Taylor polynomial, its fixed endpoint cutoffs and the
exponential are applied to the retained root traces. Both reciprocal
choices use one scalar kernel. No final height tower, quantitative
height estimate or order-dependent neighborhood is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

def n04Realization_boundaryTaylorPolynomial_mixedJetRegularity
    {U : Set X} (hU : IsOpen U) (n : ℕ) (c : ℝ)
    (A : X → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ j, j ≤ n → ContDiff ℝ ∞ (A x j))
    (J : ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b (A x j) θ)) :
    MixedJetRegularity U univ (fun x => boundaryTaylorPolynomial n c (A x)) := by
  let w : ℕ → PolarPoint → ℝ := fun j q => (q.1 - c) ^ j / (j.factorial : ℝ)
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) :=
    ((contDiff_fst.sub contDiff_const).pow j).div_const _
  let F : Fin (n + 1) → X → PolarPoint → ℝ :=
    fun j x q => w j.val q * A x j.val q.2
  let RF : ∀ j, MixedJetRegularity U univ (F j) := fun j =>
    (n04Realization_mixedJetRegularity_fixedSpatial hU (hw j.val).contDiffOn).mul
      (n04Realization_angularField_mixedJetRegularity hU
        (fun x hx => hA x hx j.val (Nat.le_of_lt_succ j.isLt))
        (J j.val (Nat.le_of_lt_succ j.isLt))) hU isOpen_univ
  let RS := MixedJetRegularity.finiteComp RF hU isOpen_univ isOpen_univ
    (G := fun y : Fin (n + 1) → ℝ => ∑ j, y j)
    (ContDiffOn.sum (fun j _ => (contDiff_apply ℝ ℝ j).contDiffOn))
    (fun _ _ _ _ => mem_univ _)
  refine RS.congr isOpen_univ ?_ ?_
  · exact fun x hx => (contDiff_boundaryTaylorPolynomial (hA x hx) c).contDiffOn
  · intro x hx q _hq
    change (∑ j : Fin (n + 1), w j.val q * A x j.val q.2) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => w j q * A x j q.2)]
    unfold boundaryTaylorPolynomial
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    ring

def n04Realization_endpointTaylorCorrection_mixedJetRegularity
    {U : Set X} (hU : IsOpen U) (n : ℕ) (l r δ : ℝ)
    (A : X → Bool → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ side j, j ≤ n → ContDiff ℝ ∞ (A x side j))
    (J : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b (A x side j) θ)) :
    MixedJetRegularity U univ (fun x => endpointTaylorCorrection n l r δ (A x)) := by
  let RP (side : Bool) := n04Realization_boundaryTaylorPolynomial_mixedJetRegularity
    hU n (if side then r else l) (fun x => A x side)
    (fun x hx => hA x hx side) (J side)
  let RC (side : Bool) : MixedJetRegularity U univ
      (fun _ q => positiveEndpointCutoff (if side then r else l) δ q.1) :=
    n04Realization_mixedJetRegularity_fixedSpatial hU
    (((contDiff_positiveEndpointCutoff (if side then r else l) δ).comp
      contDiff_fst).contDiffOn)
  exact ((RC false).mul (RP false) hU isOpen_univ).add
    ((RC true).mul (RP true) hU isOpen_univ) hU isOpen_univ

/-- Both the actual interpolated height and its reciprocal are formed
from the same finite raw source-height traces on the original domain. -/
def n04Realization_positiveHeightTaylor_mixedJetRegularity
    {U : Set X} (hU : IsOpen U) (n : ℕ) (l r δ : ℝ)
    (h : X → Bool → PolarPoint → ℝ)
    (hroot : ∀ x ∈ U, ∀ side θ,
      ContDiffAt ℝ ∞ (h x side) (if side then r else l, θ))
    (hpos : ∀ x ∈ U, ∀ side θ, 0 < h x side (if side then r else l, θ))
    (J : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b
        (radialBoundaryJet (h x side) (if side then r else l) j) θ))
    (inv : Bool) :
    MixedJetRegularity U univ (fun x q => if inv then
      (positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h x) q)⁻¹
      else positiveHeightTaylorInterpolation n l r δ (fun _ => 1) (h x) q) := by
  let A : X → Bool → ℕ → ℝ → ℝ :=
    fun x => positiveHeightTaylorData l r (fun _ => 1) (h x)
  have hA (x : X) (hx : x ∈ U) (side : Bool) (j : ℕ) (_hj : j ≤ n) :
      ContDiff ℝ ∞ (A x side j) :=
    contDiff_positiveHeightTaylorData contDiff_const (fun _ => zero_lt_one)
      (hroot x hx) (hpos x hx) side j
  have hlog (x : X) (side : Bool) : boundaryHeightLogRatio (fun _ => 1) (h x side) =
      (fun p => Real.log (h x side p)) := by
    funext p
    simp only [boundaryHeightLogRatio, div_one]
  let JA (side : Bool) (j : ℕ) (hj : j ≤ n) (b : ℕ) (θ : ℝ) :
      SmoothDirections U (fun x => iteratedDeriv b (A x side j) θ) :=
    (n04Realization_logBoundaryTrace_parameterTower hU (if side then r else l) j
      (fun x hx => hroot x hx side) (fun x hx => hpos x hx side)
      (fun d hd => J side d (hd.trans hj)) b θ).congr (fun _ _ => by
        simp only [A, positiveHeightTaylorData, hlog])
  let RT := n04Realization_endpointTaylorCorrection_mixedJetRegularity hU n l r δ A hA JA
  have hg : ContDiff ℝ ∞
      (fun t : ℝ => if inv then Real.exp (-t) else Real.exp t) := by
    cases inv
    · exact Real.contDiff_exp
    · exact Real.contDiff_exp.comp contDiff_neg
  have RG := RT.scalarComp hU isOpen_univ isOpen_univ hg.contDiffOn
    (fun _ _ _ _ => mem_univ _)
  simpa only [positiveHeightTaylorInterpolation, one_mul, Real.exp_neg, A] using RG

/-- Degree three is the exact stored positive height in the retained
family. The actual root geometry supplies every qualitative premise;
only its genuine raw axis towers remain as inputs. -/
def n04Realization_actualFixedPositiveHeight_mixedJetRegularity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    {U : Set X} (hU : IsOpen U) (z : X → AnnularState S × ℝ)
    (hz : ∀ x ∈ U, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x ∈ U, stateSector S (z x).1)
    (src : ∀ i : N04PositiveComponent D.a D.b (deriv D.w),
      ∀ side, N04PositiveEndpointSource C i side)
    (δ : N04PositiveComponent D.a D.b (deriv D.w) → ℝ)
    (i : N04PositiveComponent D.a D.b (deriv D.w))
    (J : ∀ side, ∀ j : ℕ, j ≤ 3 → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b
        (radialBoundaryJet (n04PositiveSourceHeight (src i side)
          (n04bActualTypedAtlas hT hS hN hfield e) (z x))
          (n04PositiveEndpoint i side) j) θ)) (inv : Bool) :
    MixedJetRegularity U univ (fun x q => if inv then
      (n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e) src 3 δ (z x) i q)⁻¹
      else n04FixedPositiveHeight (n04bActualTypedAtlas hT hS hN hfield e) src 3 δ (z x) i q) := by
  have hroot (x : X) (hx : x ∈ U) (side : Bool) (θ : ℝ) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      hT hS hN hfield e (src i side) (hz x hx) (hs x hx)).height_root θ
  exact n04Realization_positiveHeightTaylor_mixedJetRegularity hU 3
    (n04PositiveLeft i) (n04PositiveRight i) (δ i)
    (fun x side => n04PositiveSourceHeight (src i side)
      (n04bActualTypedAtlas hT hS hN hfield e) (z x))
    (fun x hx side θ => (hroot x hx side θ).1)
    (fun x hx side θ => (hroot x hx side θ).2) J inv

end ContinuousFlexibility.Analysis
