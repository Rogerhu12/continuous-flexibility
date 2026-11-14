import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryAngularPullback
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceForwardSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometrySourceBoundaryTraces
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsCoefficientFormula
import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsMixedFormula

/-!
# The stored coefficients from the actual source at its forward label

The original angular inverse and finite radial representative satisfy
the required jet identities. Thus the finite pullback estimate applies
to the literal coefficients of the retained controlled family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem angularInverseLinear_eq_root (a b : ℝ) :
    n04PositiveGeometry_angularInverseLinear a b =
      n04PositiveGeometry_rootInverseLinear 1 1 a b := by
  apply ContinuousLinearMap.ext
  intro v
  rw [n04PositiveGeometry_angularInverseLinear_apply,
    n04PositiveGeometry_rootInverseLinear_apply]
  apply Prod.ext <;> simp only [one_mul, mul_one] <;> ring

private theorem radial_snd_eq_firstJet
    {f : PolarPoint → PolarPoint} {q : PolarPoint} (hf : ContDiffAt ℝ ∞ f q) :
    radialPartial (fun p => (f p).2) q =
      (iteratedFDeriv ℝ 1 f q (fun _ => (1, 0))).2 := by
  have h := congrArg (fun A : PolarPoint [×1]→L[ℝ] ℝ => A (fun _ => (1, 0)))
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).iteratedFDeriv_comp_left hf
      (by simp : (1 : ℕ∞ω) ≤ ∞))
  change iteratedFDeriv ℝ 1 (fun p => (f p).2) q (fun _ => (1, 0)) =
    (iteratedFDeriv ℝ 1 f q (fun _ => (1, 0))).2 at h
  simpa only [iteratedFDeriv_one_apply, radialPartial] using h

private theorem angularGraph_jet_of_snd
    {φ : PolarPoint → ℝ} {p : PolarPoint} {k : ℕ}
    (hφ : ContDiffAt ℝ ∞ φ p) (hk : 2 ≤ k)
    (S : PolarPoint [×k]→L[ℝ] PolarPoint)
    (hS : iteratedFDeriv ℝ k φ p =
      (ContinuousLinearMap.snd ℝ ℝ ℝ).compContinuousMultilinearMap S) :
    iteratedFDeriv ℝ k (n04PositiveGeometry_angularGraph φ) p =
      n04PositiveGeometry_angleOutputProjection.compContinuousMultilinearMap S := by
  apply ContinuousMultilinearMap.ext
  intro v
  have he := n04PositiveGeometry_fiberLift_jet hφ hk v
  exact he.trans (congrArg (fun a : ℝ => ((0 : ℝ), a))
    (congrArg (fun A : PolarPoint [×k]→L[ℝ] ℝ => A v) hS))

theorem n04PositiveGeometry_controlledCoefficient_word_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W}
    (G : N04PositiveGeometryControlledFamily W X 3)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hεW : ε ≤ W.ε)
    (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (N j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ, 1 ≤ degree ∧
    ∀ i side m, (X.src i side).val = some m →
    ∀ JS : ∀ n, 1 ≤ n → n ≤ 4 → SmoothDirections
      (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (n04PositiveGeometry_sourceForwardJet W X i side m n),
    ∀ Jb : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ =>
        deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2),
    ∀ Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun y : (StateDirections W.S × ℝ) × ℝ =>
        G.toN04PositiveGeometryControlData.coefficients
          (liftSectorParameter W.S W.C y.1) i side j y.2),
    ∀ K s d, K + s + d ≤ N → ∀ x ∈ sectorNeighborhood W.S base ε ε, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → H ≤ M → 1 ≤ t → ∀ shift,
    (∀ n hn hn4, N04BoundaryWordBounds (JS n hn hn4) K s d x θ P M H t shift) →
    N04BoundaryWordBounds Jb K s d x θ P M H t shift →
    N04BoundaryWordBounds Q K s d x θ P (C * M ^ degree) H t shift := by
  let data := n04PositiveGeometry_boundaryAngularPullback_word_bound
    (E := StateDirections W.S × ℝ) N j hj hj4 L hL
  refine ⟨data.choose, data.choose_spec.1, data.choose_spec.2.choose,
    data.choose_spec.2.choose_spec.1, ?_⟩
  intro i side m hm JS Jb Q K s d hN x hx θ P M H t hM hH hHL hHM ht shift hS hb'
  let U := sectorNeighborhood W.S base ε ε
  let φ := fun y : (StateDirections W.S × ℝ) × ℝ =>
    G.toN04PositiveGeometryControlData.angle (liftSectorParameter W.S W.C y.1) i
  let f := fun y => n04PositiveGeometry_angularGraph (φ y)
  let g := fun y => n04PositiveGeometry_angularGraphInverse (φ y)
  let ξ := fun y : (StateDirections W.S × ℝ) × ℝ =>
    G.toN04PositiveGeometryControlData.radialRepresentative
      (liftSectorParameter W.S W.C y.1) i side
  let q := fun y : (StateDirections W.S × ℝ) × ℝ => (n04PositiveEndpoint i side, y.2)
  let β := fun y : (StateDirections W.S × ℝ) × ℝ =>
    n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side) y.2
  let b := fun y : (StateDirections W.S × ℝ) × ℝ =>
    deriv (n01RootLabel W.S W.C (liftSectorParameter W.S W.C y.1) m (!side)) y.2
  let S := n04PositiveGeometry_sourceForwardJet W X i side m
  have hzG (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :=
    stateNeighborhood_mono W.S W.C hGb hGε
      (liftSectorParameter_mem_stateNeighborhood (C := W.C) hy.1 le_rfl)
  have hs (y : (StateDirections W.S × ℝ) × ℝ) :=
    W.through03.1.1.2.2.1.liftSectorParameter_sector y.1
  have hφ (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiff ℝ ∞ (φ y) :=
    n04PositiveGeometry_controlled_angle_contDiff G (hzG y hy) (hs y) i
  have hpositive (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) (p : PolarPoint) :
      0 < deriv (fun η => φ y (p.1, η)) p.2 :=
    n04PositiveGeometry_controlled_angle_positive G (hzG y hy) (hs y) i p.1 p.2
  have hperiod (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) (r θ : ℝ) :
      φ y (r, θ + Real.pi) = φ y (r, θ) + Real.pi :=
    n04PositiveGeometry_controlled_angle_period G (hzG y hy) (hs y) i r θ
  have hf (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (f y) (g y (q y)) :=
    (n04PositiveGeometry_angularGraph_contDiff (hφ y hy)).contDiffAt
  have hg (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (g y) (q y) :=
    (n04PositiveGeometry_angularGraphInverse_contDiff Real.pi_ne_zero
      (hφ y hy) (hpositive y hy) (hperiod y hy)).contDiffAt
  have hξ (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) : ContDiffAt ℝ ∞ (ξ y) (g y (q y)) :=
    (n04PositiveGeometry_controlled_radialRepresentative_contDiff G (hzG y hy) (hs y) i side).contDiffAt
  have hpoint (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      g y (q y) = (n04PositiveEndpoint i side, β y) :=
    Prod.ext rfl (n04PositiveGeometry_controlled_angle_inverse_boundary
      G (hzG y hy) (hs y) i side m hm y.2)
  have hsource (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :=
    n04PositiveGeometry_source_root_smooth (X := X) hb hεW i side
      (y.1, β y) ⟨hy.1, mem_univ _⟩
  have hleft (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      (n04PositiveGeometry_rootInverseLinear 1 1 ((S 1 y (fun _ => (1, 0))).2) (b y)).comp
        (fderiv ℝ (f y) (g y (q y))) = ContinuousLinearMap.id ℝ PolarPoint := by
    have hd := n04PositiveGeometry_controlled_angle_inverse_differential
      G (hzG y hy) (hs y) i side m hm y.2
    have hr : radialPartial (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
        (liftSectorParameter W.S W.C y.1) p).2) (n04PositiveEndpoint i side, β y) =
        (S 1 y (fun _ => (1, 0))).2 := radial_snd_eq_firstJet (hsource y hy)
    have he : fderiv ℝ (g y) (q y) =
        n04PositiveGeometry_rootInverseLinear 1 1 ((S 1 y (fun _ => (1, 0))).2) (b y) :=
      hd.trans ((congrArg (fun a => n04PositiveGeometry_angularInverseLinear a (b y)) hr).trans
        (angularInverseLinear_eq_root _ _))
    exact (congrArg (fun A : PolarPoint →L[ℝ] PolarPoint =>
      A.comp (fderiv ℝ (f y) (g y (q y)))) he.symm).trans
      (n04PositiveGeometry_angularGraphInverse_fderiv_left Real.pi_ne_zero
        (hφ y hy) (hpositive y hy) (hperiod y hy) (q y))
  have hangle (k : ℕ) (hk : k ≤ 4) (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      iteratedFDeriv ℝ k (φ y) (g y (q y)) =
        (ContinuousLinearMap.snd ℝ ℝ ℝ).compContinuousMultilinearMap (S k y) := by
    calc
      _ = iteratedFDeriv ℝ k (φ y) (n04PositiveEndpoint i side, β y) :=
        congrArg (iteratedFDeriv ℝ k (φ y)) (hpoint y hy)
      _ = iteratedFDeriv ℝ k (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
          (liftSectorParameter W.S W.C y.1) p).2) (n04PositiveEndpoint i side, β y) :=
        n04PositiveGeometry_controlled_angle_boundary_jets G (hzG y hy) (hs y) i side k hk (β y)
      _ = _ := (ContinuousLinearMap.snd ℝ ℝ ℝ).iteratedFDeriv_comp_left
        (hsource y hy) (by simp : (k : ℕ∞ω) ≤ ∞)
  have hF (k : ℕ) (hk : 2 ≤ k) (hk4 : k ≤ 4) (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      iteratedFDeriv ℝ k (f y) (g y (q y)) =
        n04PositiveGeometry_angleOutputProjection.compContinuousMultilinearMap (S k y) :=
    angularGraph_jet_of_snd (hφ y hy).contDiffAt hk (S k y) (hangle k hk4 y hy)
  have hX (k : ℕ) (_hk : 1 ≤ k) (hk4 : k ≤ 4) (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      iteratedFDeriv ℝ k (ξ y) (g y (q y)) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).compContinuousMultilinearMap (S k y) := by
    calc
      _ = iteratedFDeriv ℝ k (ξ y) (n04PositiveEndpoint i side, β y) :=
        congrArg (iteratedFDeriv ℝ k (ξ y)) (hpoint y hy)
      _ = iteratedFDeriv ℝ k (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀)
          (liftSectorParameter W.S W.C y.1) p).1) (n04PositiveEndpoint i side, β y) :=
        n04PositiveGeometry_controlled_radialRepresentative_boundary_jets
          G (hzG y hy) (hs y) i side k hk4 (β y)
      _ = _ := (ContinuousLinearMap.fst ℝ ℝ ℝ).iteratedFDeriv_comp_left
        (hsource y hy) (by simp : (k : ℕ∞ω) ≤ ∞)
  have hcoef (y) (hy : y ∈ U ×ˢ (univ : Set ℝ)) :
      G.toN04PositiveGeometryControlData.coefficients (liftSectorParameter W.S W.C y.1)
        i side j y.2 = iteratedFDeriv ℝ j (ξ y ∘ g y) (q y) (fun _ => (1, 0)) := by
    have he := congrArg (fun a : ℕ → ℝ → ℝ => a j y.2)
      (G.toN04PositiveGeometryControlData.coefficients_eq_angularPullback
        (liftSectorParameter W.S W.C y.1) i side)
    exact he.trans (n06_radialBoundaryJet_eq_frechet j ((hξ y hy).comp (q y) (hg y hy)))
  let QD := Q.congr hcoef
  have hbound := data.choose_spec.2.choose_spec.2 (sectorNeighborhood_isOpen W.S base ε ε)
    f g ξ q b S hf hg hξ
    (fun y hy => Filter.Eventually.of_forall (fun p =>
      n04PositiveGeometry_angularGraph_right_inverse Real.pi_ne_zero (hφ y hy) (hperiod y hy) p))
    hleft hF hX JS Jb QD K s d hN x hx θ P M H t hM hH hHL hHM ht shift hS hb'
  exact hbound.congr hx (fun y hy => (hcoef y hy).symm)

end ContinuousFlexibility.Analysis
