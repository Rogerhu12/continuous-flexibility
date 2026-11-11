import ContinuousFlexibility.Analysis.N07bHeightBound
import ContinuousFlexibility.Analysis.N07bNormalizedSourceChain

/-!
# The actual canonical unknown from the primitive middle factor

The middle initial field is the normalized reciprocal height. Its zeroth
material jet gives the actual unknown density at the retained exponent
3/4. At a fixed admissible state its polynomial state factor is a finite
constant. One `E0` estimate supplies one material-envelope power before
squaring. Every nonnegative target loss improves the sampled factor.

No neighborhood restriction or unknown-space membership is assumed. The
last theorem invokes the proved physical energy and atlas summation bridge
to construct the actual prescribed canonical Hilbert sequence.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The exact reciprocal-height density is the square of its normalized
middle factor, times the improving sampled-envelope factor. This algebraic
identity holds at every real exponent; the primitive contract below retains
the particular exponent 3/4. -/
theorem n07b_heightDensity_eq_normalized_height
    {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (β loss : ℝ) (m : ℕ) (x : PolarPoint)
    (hx : 0 < T.H x.1) (hm : 0 < T.H (T.sample (K.cell m)))
    (hΩ : 0 ≤ T.ell x.1 * |planeJacobian (K.chart z m) x|) :
    (n07bCanonicalSourceFactor T K β (-loss) m)⁻¹ ^ 2 *
        T.ell x.1 * |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 *
          T.H x.1 ^ (2 * β) =
      (T.M (T.sample (K.cell m)) ^ loss)⁻¹ ^ 2 *
        (canonicalMaterialNormalizer T K z m β x * (K.height z m x)⁻¹) ^ 2 := by
  have hN : canonicalMaterialNormalizer T K z m β x =
      Real.sqrt (T.ell x.1 * |planeJacobian (K.chart z m) x|) *
        (T.H (T.sample (K.cell m)) ^ β)⁻¹ * T.H x.1 ^ β :=
    n07bSourceNormalizer_eq_product T K z m β x hx hm
  have hHpow : T.H x.1 ^ (2 * β) = (T.H x.1 ^ β) ^ 2 := by
    rw [show (2 : ℝ) * β = β * 2 by ring, Real.rpow_mul hx.le, Real.rpow_two]
  simp only [n07bCanonicalSourceFactor, neg_neg, hN, hHpow,
    div_eq_mul_inv, mul_inv_rev, mul_pow, ← inv_pow, Real.sq_sqrt hΩ]
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- At each admissible state, the actual primitive middle field gives the
unknown density bound with one material order and every nonnegative loss.
The state-dependent constant is chosen before the piece and physical point. -/
theorem n07b_heightDensity_of_primitive_geometry
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (loss : ℝ) (hloss : 0 ≤ loss) :
    ∃ A : ℝ, 0 ≤ A ∧
      N07bHeightDensityBound T K z (3 / 4 : ℝ) (3 / 4 : ℝ) (-loss) 1 A := by
  obtain ⟨r, d, C₀, E, hC₀, _, hjet⟩ := hgeom.materialJets 0
  obtain ⟨CE, hCE, hE⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 E
  let Q : ℝ := 1 + stateGrading S r (z.1 - C.referenceState) + |z.2|
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (abs_nonneg _)
  let B : ℝ := C₀ * CE * Q ^ d
  refine ⟨B ^ 2, sq_nonneg B, ?_⟩
  intro m x hx
  have hxcore : x.1 ∈ Ioo D.a D.b := ((hK.domains z hz hs m).2.2.1 hx).1
  have hpos := hT.2.1 x.1 hxcore
  have hsample := spaces_trace_sample_mem hD hT (K.cell m)
  have hsamplepos := hT.2.1 (T.sample (K.cell m)) hsample
  have hradius : T.radius (T.rho x.1) = x.1 :=
    hT.2.2.2.2.2.2.2.2.1 x.1 hxcore
  have hy : (T.radius (T.rho x.1), x.2) ∈ physicalPieceOpen S K z m := by
    simpa only [hradius, Prod.eta] using hx
  have hzero := hjet z hz hs m (T.rho x.1, x.2) hy
    (Sum.inr (Sum.inl (1 : Fin 3))) 0 le_rfl
  simp only [norm_iteratedFDeriv_zero, hradius, Prod.eta, Real.norm_eq_abs] at hzero
  change |canonicalMaterialNormalizer T K z m (3 / 4 : ℝ) x *
      (K.height z m x)⁻¹| ≤ C₀ * T.E0 x.1 ^ E * Q ^ d at hzero
  have hmiddle : |canonicalMaterialNormalizer T K z m (3 / 4 : ℝ) x *
      (K.height z m x)⁻¹| ≤ B * T.M x.1 := by
    calc
      _ ≤ C₀ * T.E0 x.1 ^ E * Q ^ d := hzero
      _ ≤ C₀ * (CE * T.M x.1) * Q ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE x.1 hxcore) hC₀.le)
          (pow_nonneg hQ d)
      _ = B * T.M x.1 := by dsimp [B]; ring
  have hmiddleSq :
      (canonicalMaterialNormalizer T K z m (3 / 4 : ℝ) x *
        (K.height z m x)⁻¹) ^ 2 ≤ B ^ 2 * T.M x.1 ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hmiddle 2
    simpa only [sq_abs, mul_pow] using h
  have hsamplePower : 1 ≤ T.M (T.sample (K.cell m)) ^ loss :=
    Real.one_le_rpow hsamplepos.2.2.2 hloss
  have hsampleInv : (T.M (T.sample (K.cell m)) ^ loss)⁻¹ ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀
      (inv_nonneg.mpr (zero_le_one.trans hsamplePower))
      (inv_le_one_of_one_le₀ hsamplePower) 2
    simpa only [one_pow] using h
  change (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) (-loss) m)⁻¹ ^ 2 *
      T.ell x.1 * |planeJacobian (K.chart z m) x| / K.height z m x ^ 2 *
        T.H x.1 ^ (2 * (3 / 4 : ℝ)) ≤ B ^ 2 * T.M x.1 ^ 2
  rw [n07b_heightDensity_eq_normalized_height T K z (3 / 4 : ℝ) loss m x
    hpos.2.1 hsamplepos.2.1 (mul_nonneg hpos.1.le (abs_nonneg _))]
  calc
    _ ≤ 1 * (canonicalMaterialNormalizer T K z m (3 / 4 : ℝ) x *
        (K.height z m x)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right hsampleInv (sq_nonneg _)
    _ ≤ B ^ 2 * T.M x.1 ^ 2 := by simpa only [one_mul] using hmiddleSq

/-- The proved primitive density estimate constructs the genuine selected
height sequence. Its actual canonical representative is retained at each
piece, and no membership certificate is supplied as an input. -/
theorem n07b_exists_canonicalHeightSequence_of_primitive_geometry
    {V : VolumeModelData S K}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε)
    (loss : ℝ) (hloss : 0 ≤ loss) {u : PolarPoint → ℝ}
    (hu : HeightMember D T (3 / 4 : ℝ) u) :
    ∃ U : CanonicalL2Sequence S K,
      VolumeMember S K V (3 / 4 : ℝ) (-loss) 0 (fun m => U m) ∧
      ∀ m, (U m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m u := by
  obtain ⟨A, hA, hbound⟩ :=
    n07b_heightDensity_of_primitive_geometry hD hT hK hz hs hgeom loss hloss
  exact n07b_exists_canonicalHeightSequence_of_geometric_bound
    (V := V) (β := (3 / 4 : ℝ)) (γ := (3 / 4 : ℝ))
    hK hz hs hD hT hV (by norm_num) (by norm_num) hu (-loss) 1 hA hbound

end ContinuousFlexibility.Analysis
