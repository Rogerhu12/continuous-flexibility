module

public import ContinuousFlexibility.Analysis.AngularFrequency
public import ContinuousFlexibility.Analysis.AngularSpectralDecomposition

/-!
# Coordinates of a general angular resolvent

The coordinate isometry is obtained from the proved full spectral
decomposition. In these coordinates the original resolvent is exactly
the reciprocal-frequency multiplier. Thus the Hilbert-sum model used by
the commutator estimates describes the given operator, not just an
unrelated diagonal operator on an auxiliary space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- Bounded-resolvent data for a nonnegative self-adjoint angular
frequency with integer spectrum. The corresponding maximal unbounded
operator has domain `operator.range` and sends `operator x` to
`x - operator x`. -/
structure AngularResolventData (𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] where
  operator : H →L[𝕜] H
  selfAdjoint : IsSelfAdjoint operator
  injective : Function.Injective operator
  spectrum_subset : spectrum ℝ operator ⊆ angularReciprocalSpectrum

theorem angularResolventEigenvalue_le_one (n : ℕ) : angularResolventEigenvalue n ≤ 1 := by
  have h := angularResolventEigenvalue_strictAnti.antitone (Nat.zero_le n)
  simpa only [angularResolventEigenvalue, Nat.cast_zero, zero_add, div_one] using h

private theorem angularResolventEigenvalue_bounded :
    ∃ C : ℝ, ∀ n, |angularResolventEigenvalue n| ≤ C := by
  refine ⟨1, fun n => ?_⟩
  rw [abs_of_pos (angularResolventEigenvalue_pos n)]
  exact angularResolventEigenvalue_le_one n

/-- The bounded reciprocal-frequency multiplier. -/
def angularResolventDiagonal (B : H →L[𝕜] H) :
    lp (fun n => angularResolventEigenspace B n) 2 →L[𝕜]
      lp (fun n => angularResolventEigenspace B n) 2 :=
  angularBoundedDiagonal angularResolventEigenvalue angularResolventEigenvalue_bounded

@[simp] theorem angularResolventDiagonal_apply (B : H →L[𝕜] H)
    (v : lp (fun n => angularResolventEigenspace B n) 2) (n : ℕ) :
    angularResolventDiagonal B v n = (angularResolventEigenvalue n : 𝕜) • v n :=
  angularBoundedDiagonal_apply _ _ _ _

/-- The canonical coordinate isometry associated with the full eigenspace decomposition. -/
def angularResolventCoordinates (B : H →L[𝕜] H)
    (h : IsHilbertSum 𝕜 (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ)) :
    H ≃ₗᵢ[𝕜] lp (fun n => angularResolventEigenspace B n) 2 :=
  h.linearIsometryEquiv

theorem angularResolventCoordinates_symm_diagonal (B : H →L[𝕜] H)
    (h : IsHilbertSum 𝕜 (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ))
    (v : lp (fun n => angularResolventEigenspace B n) 2) :
    B ((angularResolventCoordinates B h).symm v) =
      (angularResolventCoordinates B h).symm (angularResolventDiagonal B v) := by
  have hsum := h.hasSum_linearIsometryEquiv_symm v
  have hmap := hsum.map B B.continuous
  have hdiag := h.hasSum_linearIsometryEquiv_symm (angularResolventDiagonal B v)
  have hterm : (fun n => B ((v n : angularResolventEigenspace B n) : H)) =
      (fun n => ((angularResolventDiagonal B v n : angularResolventEigenspace B n) : H)) := by
    funext n
    have hn := (mem_angularResolventEigenspace B n (v n)).mp (v n).property
    simpa only [angularResolventDiagonal_apply, SetLike.val_smul] using hn
  have hmap' : HasSum
      (fun n => B ((v n : angularResolventEigenspace B n) : H))
      (B ((angularResolventCoordinates B h).symm v)) := by
    simpa only [angularResolventCoordinates, Submodule.coe_subtypeₗᵢ,
      Submodule.subtype_apply, Function.comp_def] using hmap
  rw [hterm] at hmap'
  exact hmap'.unique hdiag

/-- The spectral coordinates intertwine the given bounded resolvent and
the diagonal reciprocal-frequency operator. -/
theorem angularResolventCoordinates_operator (B : H →L[𝕜] H)
    (h : IsHilbertSum 𝕜 (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ)) (x : H) :
    angularResolventCoordinates B h (B x) =
      angularResolventDiagonal B (angularResolventCoordinates B h x) := by
  have heq := angularResolventCoordinates_symm_diagonal B h (angularResolventCoordinates B h x)
  rw [LinearIsometryEquiv.symm_apply_apply] at heq
  have hmap := congrArg (angularResolventCoordinates B h) heq
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hmap

theorem angularResolventCoordinates_operator_apply (B : H →L[𝕜] H)
    (h : IsHilbertSum 𝕜 (fun n => angularResolventEigenspace B n)
      (fun n => (angularResolventEigenspace B n).subtypeₗᵢ)) (x : H) (n : ℕ) :
    angularResolventCoordinates B h (B x) n =
      (angularResolventEigenvalue n : 𝕜) • angularResolventCoordinates B h x n := by
  rw [angularResolventCoordinates_operator, angularResolventDiagonal_apply]

end ContinuousFlexibility.Analysis
