module

public import ContinuousFlexibility.Analysis.N04bConstructedRootDensity
public import ContinuousFlexibility.Analysis.N04bCanonicalCut

/-!
# Transmission for the constructed inverse and physical root height

The physical height is pulled through the actual root inverse using the
travel chart's right-inverse identity. This holds on a full neighborhood
of the positive cut radius, including both sides of that radius.

The existing root-height transmission calculation then applies to the
actual constructor fields. No transmission or operator identity is an
input. The physical cut remains X(T/2, θ).
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The travel density is the physical density evaluated at the actual
travel inverse. -/
def n04bRootTravelDensity (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    (X : PolarPoint → PolarPoint) (q : PolarPoint) : ℝ :=
  A.a (X q) * v (X q)

/-- The inverse identity also holds beyond the middle cut, which is
needed for the full derivative germ at its positive root radius. -/
theorem n04bRootStripChart_inverse_of_nonneg
    (T : ℝ) (side : Bool) {p : PolarPoint} (hp : 0 ≤ p.1) :
    n04bRootStripChart T side (n04bRootStripInverse T side p) = p := by
  apply Prod.ext
  · change n04bRootCoordinate (n04bTravelOrientation T side
      (n04bTravelOrientation T side (n04bRootTravel p.1))) = p.1
    rw [n04bTravelOrientation_involutive, n04b_rootCoordinate_rootTravel hp]
  · rfl

theorem n04bRootStripInverse_at_cut
    {T : ℝ} (hT : 0 < T) (side : Bool) (θ : ℝ) :
    n04bRootStripInverse T side (n04bRootCutRadius T, θ) = (T / 2, θ) := by
  rw [n04bRootStripInverse_eq_signedTravel]
  simp only [n04bSignedTravel, n04b_rootTravel_cut hT,
    sub_self, mul_zero, add_zero]

theorem n04b_continuousAt_rootStripInverse
    {T : ℝ} {side : Bool} {p : PolarPoint} (hp : 0 < p.1) :
    ContinuousAt (n04bRootStripInverse T side) p := by
  have ht : ContinuousAt (fun q : PolarPoint => n04bRootTravel q.1) p :=
    (n04b_hasDerivAt_rootTravel hp).continuousAt.comp continuousAt_fst
  have hs : ContinuousAt
      (fun q : PolarPoint => n04bTravelOrientation T side (n04bRootTravel q.1)) p :=
    (n04b_hasDerivAt_travelOrientation T side _).continuousAt.comp ht
  exact hs.prodMk continuousAt_snd

theorem n04b_tendsto_rootStripInverse_cut
    {T : ℝ} (hT : 0 < T) (side : Bool) (θ : ℝ) :
    Tendsto (n04bRootStripInverse T side)
      (𝓝 (n04bRootCutRadius T, θ)) (𝓝 (T / 2, θ)) := by
  simpa only [n04bRootStripInverse_at_cut hT side θ] using
    (n04b_continuousAt_rootStripInverse (T := T) (side := side)
      (p := (n04bRootCutRadius T, θ)) (n04bRootCutRadius_pos hT)).tendsto

theorem n04b_tendsto_rootPhysicalInverse_cut
    {X : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T) (side : Bool) (θ : ℝ)
    (hX : ContinuousAt X (T / 2, θ)) :
    Tendsto (n04bRootPhysicalInverse X T side)
      (𝓝 (n04bRootCutRadius T, θ)) (𝓝 (X (T / 2, θ))) := by
  exact hX.tendsto.comp (n04b_tendsto_rootStripInverse_cut hT side θ)

/-- The physical formula for the constructed height becomes exactly the
travel height when evaluated on the genuine inverse. -/
theorem n04bRootPhysicalHeight_at_inverse
    (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    (F X : PolarPoint → PolarPoint) (T : ℝ) (side : Bool)
    {p : PolarPoint} (hp : 0 ≤ p.1)
    (hFX : F (X (n04bRootStripInverse T side p)) = n04bRootStripInverse T side p) :
    n04bRootPhysicalHeight A v F T side (n04bRootPhysicalInverse X T side p) =
      n04bRootHeightInTravel T (if side then -1 else 1)
        (n04bRootTravelDensity A v X) p := by
  have hchart :
      n04bRootPhysicalChart F T side (n04bRootPhysicalInverse X T side p) = p := by
    change n04bRootStripChart T side (F (X (n04bRootStripInverse T side p))) = p
    rw [hFX]
    exact n04bRootStripChart_inverse_of_nonneg T side hp
  unfold n04bRootPhysicalHeight
  rw [hchart, n04bRootPhysicalInverse_eq_signedTravel]
  rfl

/-- The actual travel right-inverse identity supplies the height identity
on a neighborhood of the cut, not merely at the cut point. -/
theorem n04bRootPhysicalHeight_inverse_germ
    (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    {F X : PolarPoint → PolarPoint} {T : ℝ}
    (hT : 0 < T) (side : Bool) (θ : ℝ)
    (hFX : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), F (X q) = q) :
    (fun p => n04bRootPhysicalHeight A v F T side
      (n04bRootPhysicalInverse X T side p)) =ᶠ[𝓝 (n04bRootCutRadius T, θ)]
      n04bRootHeightInTravel T (if side then -1 else 1)
        (n04bRootTravelDensity A v X) := by
  have hmiddle : (T / 2, θ) ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) :=
    ⟨⟨half_pos hT, half_lt_self hT⟩, mem_univ θ⟩
  have hm := (n04b_tendsto_rootStripInverse_cut hT side θ).eventually
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hmiddle)
  have hp : ∀ᶠ p : PolarPoint in 𝓝 (n04bRootCutRadius T, θ), 0 < p.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (n04bRootCutRadius_pos hT)
  filter_upwards [hm, hp] with p hm hp
  exact n04bRootPhysicalHeight_at_inverse A v F X T side hp.le (hFX _ hm)

/-- Constructor identities for the actual inverse and physical height
imply both trace and normal transmission for every smooth physical test.
The physical density is only required to be differentiable at the actual
moving cut point. -/
theorem n04b_canonicalHeight_constructedRoot_cut
    {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (piece : Bool → ℕ)
    (A : SymmetricCoefficients) (v : PolarPoint → ℝ)
    {F X : PolarPoint → PolarPoint} {T : ℝ} (hT : 0 < T) (θ : ℝ)
    (hFX : ∀ q ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ), F (X q) = q)
    (hX : DifferentiableAt ℝ X (T / 2, θ))
    (ha : DifferentiableAt ℝ A.a (X (T / 2, θ)))
    (hv : DifferentiableAt ℝ v (X (T / 2, θ)))
    (ha0 : 0 < A.a (X (T / 2, θ))) (hv0 : 0 < v (X (T / 2, θ)))
    (hInverse : ∀ side : Bool,
      K.inverseChart z (piece side) =ᶠ[𝓝 (n04bRootCutRadius T, θ)]
        n04bRootPhysicalInverse X T side)
    (hHeight : ∀ side : Bool,
      K.height z (piece side) =ᶠ[𝓝 (X (T / 2, θ))]
        n04bRootPhysicalHeight A v F T side)
    (u : PolarPoint → ℝ) (hu : ContDiff ℝ ∞ u) :
    canonicalHeight S K z (piece true) u (n04bRootCutRadius T, θ) =
        canonicalHeight S K z (piece false) u (n04bRootCutRadius T, θ) ∧
      radialPartial (canonicalHeight S K z (piece true) u) (n04bRootCutRadius T, θ) =
        -radialPartial (canonicalHeight S K z (piece false) u) (n04bRootCutRadius T, θ) -
          canonicalHeight S K z (piece false) u (n04bRootCutRadius T, θ) /
            (2 * n04bRootCutRadius T) := by
  have hDensity : DifferentiableAt ℝ (n04bRootTravelDensity A v X) (T / 2, θ) :=
    (ha.comp (T / 2, θ) hX).mul (hv.comp (T / 2, θ) hX)
  have hi (side : Bool) :
      ∀ᶠ p in 𝓝 (n04bRootCutRadius T, θ),
        K.inverseChart z (piece side) p =
          X (n04bSignedTravel T (if side then -1 else 1) n04bRootTravel p) := by
    filter_upwards [hInverse side] with p hp
    exact hp.trans (congrFun (n04bRootPhysicalInverse_eq_signedTravel X T side) p)
  have hh (side : Bool) :
      ∀ᶠ p in 𝓝 (n04bRootCutRadius T, θ),
        K.height z (piece side) (K.inverseChart z (piece side) p) =
          n04bRootHeightInTravel T (if side then -1 else 1)
            (n04bRootTravelDensity A v X) p := by
    have hphysical :=
      (n04b_tendsto_rootPhysicalInverse_cut hT side θ hX.continuousAt).eventually
        (hHeight side)
    filter_upwards [hInverse side, hphysical,
      n04bRootPhysicalHeight_inverse_germ A v hT side θ hFX] with p hi hp ht
    rw [hi]
    exact hp.trans ht
  exact n04b_canonicalHeight_root_cut K z piece hT θ X
    (n04bRootTravelDensity A v X) hX hDensity (mul_pos ha0 hv0) hi hh u hu

end ContinuousFlexibility.Analysis
