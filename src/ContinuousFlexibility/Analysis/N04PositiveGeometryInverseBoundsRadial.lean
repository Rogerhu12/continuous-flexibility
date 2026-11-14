module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsFinite
public import ContinuousFlexibility.Analysis.N04RealizationEndpointFiberDirections
public import ContinuousFlexibility.Analysis.N01cFiniteAffineJets

/-!
# The actual positive radial inverse on the original state space

Only the finitely many positive radial endpoint jets are free coefficients.
The zeroth endpoint values are the fixed physical radii.  Strict margins
for the first jet and the finite upper envelope define an open coefficient
domain, with the same displayed collar widths used by the forward factory.

The finite coefficient kernel is exactly `endpointFiberInterpolation`.
Its forward lower bound supplies the hypotheses of the ordinary scalar
implicit function theorem.  Composing its actual inverse with the endpoint
coefficient tower then gives the entire moving radial inverse tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- Positive-order endpoint coefficients; index `j` stores derivative
order `j + 1`.  Endpoint values are not free coordinates. -/
abbrev N04PositiveRadialCoefficients (n : ℕ) := Bool → Fin (n + 1) → ℝ

def n04PositiveGeometry_radialCoefficientField (n : ℕ) (l r : ℝ)
    (a : N04PositiveRadialCoefficients n) (side : Bool) : ℕ → ℝ → ℝ
  | 0, _ => if side then r else l
  | j + 1, _ => if hj : j < n + 1 then a side ⟨j, hj⟩ else 0

theorem n04PositiveGeometry_radialCoefficientField_zero
    (n : ℕ) (l r : ℝ) (a : N04PositiveRadialCoefficients n) (side : Bool) (θ : ℝ) :
    n04PositiveGeometry_radialCoefficientField n l r a side 0 θ =
      if side then r else l := rfl

theorem n04PositiveGeometry_radialCoefficientField_succ
    (n : ℕ) (l r : ℝ) (a : N04PositiveRadialCoefficients n) (side : Bool)
    (j : Fin (n + 1)) (θ : ℝ) :
    n04PositiveGeometry_radialCoefficientField n l r a side (j + 1) θ = a side j := by
  simp only [n04PositiveGeometry_radialCoefficientField, dif_pos j.isLt]

/-- Strict finite margins on the actual positive radial jets. -/
def n04PositiveGeometry_radialCoefficientDomain (n : ℕ) (κ M : ℝ) :
    Set (N04PositiveRadialCoefficients n) :=
  {a | ∀ side, κ < a side 0 ∧ ∀ j, |a side j| < M}

theorem n04PositiveGeometry_radialCoefficientDomain_isOpen
    (n : ℕ) (κ M : ℝ) : IsOpen (n04PositiveGeometry_radialCoefficientDomain n κ M) := by
  have hc (side : Bool) (j : Fin (n + 1)) :
      Continuous (fun a : N04PositiveRadialCoefficients n => a side j) :=
    (continuous_apply j).comp (continuous_apply side)
  have he : n04PositiveGeometry_radialCoefficientDomain n κ M =
      ⋂ side : Bool,
        ({a : N04PositiveRadialCoefficients n | κ < a side 0} ∩
          ⋂ j : Fin (n + 1), {a | |a side j| < M}) := by
    ext a
    simp only [n04PositiveGeometry_radialCoefficientDomain, mem_setOf_eq,
      mem_iInter, mem_inter_iff]
  rw [he]
  exact isOpen_iInter_of_finite fun side =>
    (isOpen_lt continuous_const (hc side 0)).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt (hc side j).abs continuous_const)

/-- The finite coefficient kernel is the literal two-collar radial
interpolation, with the same fixed middle interval and collar widths. -/
def n04PositiveGeometry_radialKernel (n : ℕ) (l r c d : ℝ) (η : Bool → ℝ)
    (p : N04PositiveRadialCoefficients n × ℝ) : ℝ :=
  endpointFiberInterpolation n l r c d η
    (n04PositiveGeometry_radialCoefficientField n l r p.1) (p.2, 0)

private theorem radialCoefficient_contDiff
    (n : ℕ) (l r : ℝ) (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : N04PositiveRadialCoefficients n × ℝ =>
      n04PositiveGeometry_radialCoefficientField n l r p.1 side j p.2) := by
  cases j with
  | zero => exact contDiff_const
  | succ j =>
      by_cases hj : j < n + 1
      · simp only [n04PositiveGeometry_radialCoefficientField, dif_pos hj]
        exact ((contDiff_apply ℝ ℝ (⟨j, hj⟩ : Fin (n + 1))).comp
          (contDiff_apply ℝ (Fin (n + 1) → ℝ) side)).comp contDiff_fst
      · simpa only [n04PositiveGeometry_radialCoefficientField, dif_neg hj] using
          (contDiff_const : ContDiff ℝ ∞
            (fun _ : N04PositiveRadialCoefficients n × ℝ => (0 : ℝ)))

private def radialCoefficient_directions
    (n : ℕ) (l r : ℝ) (side : Bool) (j : Fin (n + 2)) :
    SmoothDirections ((univ : Set (N04PositiveRadialCoefficients n)) ×ˢ univ)
      (fun p : N04PositiveRadialCoefficients n × ℝ =>
        n04PositiveGeometry_radialCoefficientField n l r p.1 side j p.2) :=
  smoothDirectionsOfContDiffOn (isOpen_univ.prod isOpen_univ)
    (radialCoefficient_contDiff n l r side j).contDiffOn

private theorem radialCoefficient_fixed_contDiff
    (n : ℕ) (l r : ℝ) (a : N04PositiveRadialCoefficients n)
    (side : Bool) (j : ℕ) :
    ContDiff ℝ ∞ (n04PositiveGeometry_radialCoefficientField n l r a side j) := by
  cases j <;> exact contDiff_const

private theorem endpointFiber_joint_contDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (n : ℕ) (l r c d : ℝ) (hcd : c < d)
    (η : Bool → ℝ) (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l))
    (A : P → Bool → ℕ → ℝ → ℝ)
    (hA : ∀ a side j, j ≤ n + 1 → ContDiff ℝ ∞ (A a side j))
    (J : ∀ side (j : Fin (n + 2)), SmoothDirections
      ((univ : Set P) ×ˢ univ) (fun p : P × ℝ => A p.1 side j p.2)) :
    ContDiff ℝ ∞ (fun p : P × PolarPoint =>
      endpointFiberInterpolation n l r c d η (A p.1) p.2) := by
  have h : ContDiffOn ℝ ∞ (fun p : P × PolarPoint =>
      endpointFiberInterpolation n l r c d η (A p.1) p.2) (univ ×ˢ univ) :=
    smoothDirections_contDiffOn_finiteDimensional
      (n04Realization_endpointFiberInterpolation_jointDirections isOpen_univ n l r c d
        hcd η hη hgap A (fun a _ => hA a) J)
  exact contDiffOn_univ.mp (by simpa only [univ_prod_univ] using h)

private theorem contDiff_polar_slice_zero
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P × PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : P × ℝ => f (p.1, (p.2, 0))) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

theorem n04PositiveGeometry_radialKernel_contDiff
    (n : ℕ) (l r c d : ℝ) (hcd : c < d)
    (η : Bool → ℝ) (hη : ∀ side, 0 < η side)
    (hgap : ∀ side, 2 * η side <
      (if side then r else c) - (if side then d else l)) :
    ContDiff ℝ ∞ (n04PositiveGeometry_radialKernel n l r c d η) := by
  have h := endpointFiber_joint_contDiff n l r c d hcd η hη hgap
    (n04PositiveGeometry_radialCoefficientField n l r)
    (fun a side j _ => radialCoefficient_fixed_contDiff n l r a side j)
    (radialCoefficient_directions n l r)
  exact contDiff_polar_slice_zero h

private theorem endpointFiberInterpolation_congr_slice
    {n : ℕ} (l r c d : ℝ) (η : Bool → ℝ)
    (A B : Bool → ℕ → ℝ → ℝ)
    (hA : ∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (A side j))
    (hB : ∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (B side j))
    (x θ α : ℝ) (hAB : ∀ side j, j ≤ n + 1 → A side j θ = B side j α) :
    endpointFiberInterpolation n l r c d η A (x, θ) =
      endpointFiberInterpolation n l r c d η B (x, α) := by
  have he (side : Bool) :
      endpointFiberCollar n l r c d η A side (x, θ) =
        endpointFiberCollar n l r c d η B side (x, α) := by
    let a : ℝ := if side then d else l
    let b : ℝ := if side then r else c
    have hcoeff : (fun j : Fin (n + 2) => A side j θ) =
        (fun j : Fin (n + 2) => B side j α) := by
      funext j
      exact hAB side j (by omega)
    exact (n04Realization_positiveCollarKernel_eq a b (η side) a (b - a)
      side (A side) (hA side) x θ).trans
      ((congrArg (fun a => n04Realization_positiveCollarKernel n
        (if side then d else l) (if side then r else c) (η side)
        (if side then d else l) ((if side then r else c) - (if side then d else l))
        side (a, x)) hcoeff).trans
        (n04Realization_positiveCollarKernel_eq a b (η side) a (b - a)
          side (B side) (hB side) x α).symm)
  simp only [endpointFiberInterpolation, twoEndpointFiberCoordinate, radialGermGlue]
  split_ifs <;> first | exact he false | exact he true | rfl

/-- The forward radial map equals the finite kernel of precisely its own
positive endpoint jets at the same angle. -/
theorem n04PositiveGeometry_radialKernel_eq
    {n : ℕ} (l r c d : ℝ) (η : Bool → ℝ) (A : Bool → ℕ → ℝ → ℝ)
    (hA : ∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (A side j))
    (hzero : ∀ side θ, A side 0 θ = if side then r else l)
    (x θ : ℝ) :
    endpointFiberInterpolation n l r c d η A (x, θ) =
      n04PositiveGeometry_radialKernel n l r c d η
        ((fun side j => A side (j + 1) θ), x) := by
  apply endpointFiberInterpolation_congr_slice l r c d η A
    (n04PositiveGeometry_radialCoefficientField n l r
      (fun side j => A side (j + 1) θ)) hA
  · intro side j _
    cases j <;> exact contDiff_const
  · intro side j hj
    cases j with
    | zero => exact hzero side θ
    | succ j =>
        have hj' : j < n + 1 := by omega
        simp only [n04PositiveGeometry_radialCoefficientField, dif_pos hj']

/-- The forward factory is valid on the full open coefficient domain.
In particular its one positive slope bound is independent of the free
coefficient vector and of the inverse evaluation point. -/
theorem n04PositiveGeometry_radialKernel_geometry
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M) :
    let η := endpointFiberWidths n l r c d κ M
    let B := endpointFiberLower n l r c d κ M
    (∀ side, 0 < η side) ∧
      (∀ side, 2 * η side <
        (if side then r else c) - (if side then d else l)) ∧
      0 < B ∧
      ∀ a ∈ n04PositiveGeometry_radialCoefficientDomain n κ M, ∀ x,
        B ≤ deriv (fun t => n04PositiveGeometry_radialKernel n l r c d η (a, t)) x := by
  let V := n04PositiveGeometry_radialCoefficientDomain n κ M
  let A : V → Bool → ℕ → ℝ → ℝ := fun a =>
    n04PositiveGeometry_radialCoefficientField n l r a.1
  have hA (a : V) (side : Bool) (j : ℕ) (_hj : j ≤ n + 1) :
      ContDiff ℝ ∞ (A a side j) := by
    cases j <;> exact contDiff_const
  have hzero (a : V) (side : Bool) (θ : ℝ) :
      A a side 0 θ = if side then r else l := rfl
  have hfirst (a : V) (side : Bool) (θ : ℝ) : κ ≤ A a side 1 θ := by
    have ha : κ < a.1 side 0 := (a.2 side).1
    have hfin : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
    change κ ≤ if hj : 0 < n + 1 then a.1 side ⟨0, hj⟩ else 0
    rw [dif_pos (Nat.succ_pos n), hfin]
    exact ha.le
  have hbound (a : V) (side : Bool) (j : ℕ) (hj : 1 ≤ j)
      (hjn : j ≤ n + 1) (θ : ℝ) : |A a side j θ| ≤ M := by
    cases j with
    | zero => omega
    | succ j =>
        have hj' : j < n + 1 := by omega
        simpa only [A, n04PositiveGeometry_radialCoefficientField, dif_pos hj'] using
          ((a.2 side).2 ⟨j, hj'⟩).le
  have hperiod (a : V) (side : Bool) (j : ℕ) (_hj : j ≤ n + 1) :
      Function.Periodic (A a side j) Real.pi := by
    intro θ
    cases j <;> rfl
  have heven (a : V) (side : Bool) (j : ℕ) (_hj : j ≤ n + 1) (θ : ℝ) :
      A a side j (-θ) = A a side j θ := by
    cases j <;> rfl
  have h := endpointFiberInterpolation_family hlc hcd hdr hκ hM
    hA hzero hfirst hbound hperiod heven
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro a ha x
  exact (h.2.2.2 ⟨a, ha⟩).2.1 x 0

theorem n04PositiveGeometry_radialKernel_inverse_contDiffOn
    (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M) :
    ContDiffOn ℝ ∞
      (fun q : N04PositiveRadialCoefficients n × ℝ =>
        Function.invFun (fun t => n04PositiveGeometry_radialKernel n l r c d
          (endpointFiberWidths n l r c d κ M) (q.1, t)) q.2)
      (n04PositiveGeometry_radialCoefficientDomain n κ M ×ˢ univ) := by
  have h := n04PositiveGeometry_radialKernel_geometry n hlc hcd hdr hκ hM
  apply n04PositiveGeometry_scalarInverse_contDiffOn
    (n04PositiveGeometry_radialCoefficientDomain_isOpen n κ M)
    (n04PositiveGeometry_radialKernel_contDiff n l r c d hcd
      (endpointFiberWidths n l r c d κ M) h.1 h.2.1).contDiffOn
  · intro a ha x
    exact h.2.2.1.trans_le (h.2.2.2 a ha x)
  · intro a ha
    exact (bijective_of_deriv_lower_bound h.2.2.1 (h.2.2.2 a ha)).2

section OriginalState

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}

/-- All state and spatial orders of the actual radial inverse, on the
original parameter neighborhood.  Its input consists only of the forward
endpoint towers and the strict margins used to select the same widths. -/
def n04PositiveGeometry_endpointRadialInverseDirections
    (hU : IsOpen U) (n : ℕ) {l r c d κ M : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (A : E → Bool → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ side j, j ≤ n + 1 → ContDiff ℝ ∞ (A x side j))
    (hzero : ∀ x ∈ U, ∀ side θ, A x side 0 θ = if side then r else l)
    (J : ∀ side (j : Fin (n + 1)), SmoothDirections (U ×ˢ univ)
      (fun p : E × ℝ => A p.1 side (j + 1) p.2))
    (hfirst : ∀ x ∈ U, ∀ side θ, κ < A x side 1 θ)
    (hbound : ∀ x ∈ U, ∀ side (j : Fin (n + 1)) θ, |A x side (j + 1) θ| < M) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => positiveFiberRadialInverse
        (endpointFiberInterpolation n l r c d (endpointFiberWidths n l r c d κ M)
          (A p.1)) p.2) := by
  let C : E × ℝ → N04PositiveRadialCoefficients n :=
    fun p side j => A p.1 side (j + 1) p.2
  let JC : SmoothDirections (U ×ˢ univ) C :=
    smoothDirectionsScalarPi (hU.prod isOpen_univ)
      (fun side => smoothDirectionsScalarPi (hU.prod isOpen_univ) (J side))
  let L : (E × PolarPoint) →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hL (p : E × PolarPoint) : L p = (p.1, p.2.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  let JL : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => C (p.1, p.2.2)) :=
    (JC.compLinear L (hU.prod isOpen_univ)
      (fun p hp => by rw [hL]; exact ⟨hp.1, mem_univ _⟩)).congrOn
      (fun p _ => congrArg C (hL p))
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let JR : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.1) :=
    (smoothDirectionsLinearOn R (hU.prod isOpen_univ)).congrOn (fun p _ => by
      simp only [R, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])
  let K := smoothDirectionsUniformProd JL JR
  have hmap : MapsTo (fun p : E × PolarPoint => (C (p.1, p.2.2), p.2.1))
      (U ×ˢ univ) (n04PositiveGeometry_radialCoefficientDomain n κ M ×ˢ univ) := by
    intro p hp
    refine ⟨?_, mem_univ _⟩
    intro side
    exact ⟨hfirst p.1 hp.1 side p.2.2, fun j => hbound p.1 hp.1 side j p.2.2⟩
  let KI := smoothDirections_contDiff_comp K
    ((n04PositiveGeometry_radialCoefficientDomain_isOpen n κ M).prod isOpen_univ)
    (n04PositiveGeometry_radialKernel_inverse_contDiffOn n hlc hcd hdr hκ hM) hmap
  apply KI.congrOn
  intro p hp
  have hs : (fun t => endpointFiberInterpolation n l r c d
      (endpointFiberWidths n l r c d κ M) (A p.1) (t, p.2.2)) =
      (fun t => n04PositiveGeometry_radialKernel n l r c d
        (endpointFiberWidths n l r c d κ M) (C (p.1, p.2.2), t)) := by
    funext t
    exact n04PositiveGeometry_radialKernel_eq l r c d
      (endpointFiberWidths n l r c d κ M) (A p.1) (hA p.1 hp.1)
      (hzero p.1 hp.1) t p.2.2
  exact congrArg (fun f : ℝ → ℝ => Function.invFun f p.2.1) hs.symm

/-- The actual angular inverse is evaluated at the moving radial inverse.
The state coordinate is retained unchanged, so this composition takes
place on the original locally convex state space. -/
def n04PositiveGeometry_fiberChartInverseDirections [LocallyConvexSpace ℝ E]
    {φ Y : E → PolarPoint → ℝ}
    (JR : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => positiveFiberRadialInverse (Y p.1) p.2))
    (JA : SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => parameterizedCircleInverse (φ p.1) p.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun p : E × PolarPoint => positiveFiberChartInverse (φ p.1) (Y p.1) p.2) := by
  let L : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let Jθ : SmoothDirections (U ×ˢ univ) (fun p : E × PolarPoint => p.2.2) :=
    (smoothDirectionsLinearOn L JR.open_domain).congrOn (fun p _ => by
      simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'])
  let Jx := smoothDirectionsLinearOn (ContinuousLinearMap.fst ℝ E PolarPoint) JR.open_domain
  let JG := smoothDirectionsUniformProd Jx (smoothDirectionsUniformProd JR Jθ)
  let JC := smoothDirections_realCompTVS JG JA
    (fun p hp => ⟨hp.1, mem_univ _⟩)
  exact smoothDirectionsUniformProd JR JC

end OriginalState

end ContinuousFlexibility.Analysis
