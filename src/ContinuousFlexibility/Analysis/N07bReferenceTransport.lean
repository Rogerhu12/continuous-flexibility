import ContinuousFlexibility.Analysis.N07bReferencePullback
import ContinuousFlexibility.Radial.R11bPhysicalPairing

/-!
# A regular reference representative from actual geometric transition maps

The maps `τ` and `q` are geometric data independent of the physical field.
Their agreement with the actual charts gives the exact canonical identities.
Their finite regularity gives the corresponding finite regularity of the
reference representative. No existence of these geometric maps is asserted.

The representative agrees a.e. with the already defined raw reference
pullback, including on the full physical angular period. Consequently the
normalization row is preserved without an extra row or integrability premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The reference field produced by the geometric coordinate and height
transitions, retaining the same physical left constant. -/
def n07bReferenceTransport (S : PhysicalSpacesData)
    (τ : PolarPoint → PolarPoint) (q : PolarPoint → ℝ)
    (a : ℝ) (η : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  a * S.chiLeft p.1 + q p * (η (τ p) - a * S.chiLeft (τ p).1)

/-- Finite regularity is preserved at the same order. In particular, C3
geometric transition maps give a C3 interior reference representative. -/
theorem n07bReferenceTransport_contDiffOn
    {D : ReferenceData} {S : PhysicalSpacesData} {n : ℕ∞ω}
    {τ : PolarPoint → PolarPoint} {q η : PolarPoint → ℝ}
    (hτ : ContDiffOn ℝ n τ (annularOpen D))
    (hq : ContDiffOn ℝ n q (annularOpen D))
    (hmap : MapsTo τ (annularOpen D) (annularOpen D))
    (hη : ContDiffOn ℝ n η (annularOpen D))
    (hχ : ContDiff ℝ n S.chiLeft) (a : ℝ) :
    ContDiffOn ℝ n (n07bReferenceTransport S τ q a η) (annularOpen D) := by
  have hleft : ContDiff ℝ n (fun p : PolarPoint => a * S.chiLeft p.1) :=
    contDiff_const.mul (hχ.comp contDiff_fst)
  have hrem : ContDiffOn ℝ n (fun p : PolarPoint => η p - a * S.chiLeft p.1)
      (annularOpen D) := hη.sub hleft.contDiffOn
  have hcomp : ContDiffOn ℝ n
      (fun p : PolarPoint => η (τ p) - a * S.chiLeft (τ p).1) (annularOpen D) :=
    hrem.comp hτ hmap
  exact hleft.contDiffOn.add (hq.mul hcomp)

/-- Global geometric equivariance gives the actual global field period.
The piecewise chart identities alone do not constrain values outside the atlas. -/
theorem n07bReferenceTransport_periodic
    {S : PhysicalSpacesData} {τ : PolarPoint → PolarPoint} {q η : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p + (0, Real.pi)) = τ p + (0, Real.pi))
    (hq : Function.Periodic q (0, Real.pi))
    (hη : Function.Periodic η (0, Real.pi)) (a : ℝ) :
    Function.Periodic (n07bReferenceTransport S τ q a η) (0, Real.pi) := by
  intro p
  simp only [n07bReferenceTransport, hτ, hq, hη, Prod.fst_add, add_zero]

/-- Global geometric reflection gives the actual even field. -/
theorem n07bReferenceTransport_even
    {S : PhysicalSpacesData} {τ : PolarPoint → PolarPoint} {q η : PolarPoint → ℝ}
    (hτ : ∀ p, τ (p.1, -p.2) = ((τ p).1, -(τ p).2))
    (hq : ∀ r θ, q (r, -θ) = q (r, θ))
    (hη : ∀ r θ, η (r, -θ) = η (r, θ)) (a : ℝ) :
    ∀ r θ, n07bReferenceTransport S τ q a η (r, -θ) =
      n07bReferenceTransport S τ q a η (r, θ) := by
  intro r θ
  simp only [n07bReferenceTransport, hτ (r, θ), hq, hη]

/-- The iterated physical row depends only on the full physical a.e. class.
This uses a.e. sections, so no Fubini or integrability premise is needed. -/
theorem n07b_referenceRow_congr_ae {D : ReferenceData} (hab : D.a ≤ D.b)
    {f g : PolarPoint → ℝ} (hfg : f =ᵐ[radialPhysicalMeasure D] g) :
    referenceRow D f = referenceRow D g := by
  have hrow (u : PolarPoint → ℝ) : referenceRow D u =
      ∫ r in D.a..D.b, radialAngularMean (fun θ =>
        referenceColumn D r * (u (r, θ) * Radial.cosineMode 2 θ)) := by
    have heq : (fun r => referenceColumn D r * referenceMode u 2 r) =
        (fun r => radialAngularMean (fun θ =>
          referenceColumn D r * (u (r, θ) * Radial.cosineMode 2 θ))) := by
      funext r
      unfold referenceMode radialAngularMean
      rw [intervalIntegral.integral_const_mul]
      ring
    exact congrArg (fun v : ℝ → ℝ => ∫ r in D.a..D.b, v r) heq
  rw [hrow f, hrow g]
  apply Radial.r11b_iteratedAngularMean_congr_ae hab
    (f := fun p : PolarPoint => referenceColumn D p.1 * (f p * Radial.cosineMode 2 p.2))
    (g := fun p : PolarPoint => referenceColumn D p.1 * (g p * Radial.cosineMode 2 p.2))
  filter_upwards [hfg] with p hp
  change referenceColumn D p.1 * (f p * Radial.cosineMode 2 p.2) =
    referenceColumn D p.1 * (g p * Radial.cosineMode 2 p.2)
  rw [hp]

section ActualAtlas

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {τ : PolarPoint → PolarPoint} {q : PolarPoint → ℝ}
  (hτpiece : ∀ m, ∀ p ∈ physicalPieceOpen S K m,
    τ p = K.inverseChart z m (K.chart (C.referenceState, 0) m p))
  (hqpiece : ∀ m, ∀ p ∈ physicalPieceOpen S K m,
    q p = K.height (C.referenceState, 0) m p / K.height z m (τ p))

include hτpiece hqpiece

/-- The representative is the actual reference piece pullback at every
point of that piece, independently of all regularity questions. -/
theorem n07bReferenceTransport_on_piece (a : ℝ) (η : PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n07bReferenceTransport S τ q a η p =
      n07bReferencePiecePullback C K z m a η p := by
  simp only [n07bReferenceTransport, n07bReferencePiecePullback, canonicalHeight,
    hqpiece m p hp, hτpiece m p hp]
  ring

/-- Agreement with the existing raw reference pullback on each actual
open piece. The two definitions may assign different boundary values. -/
theorem n07bReferenceTransport_eq_pullback_on_piece
    (hK : N04PartA D S C K base ε) (a : ℝ) (η : PolarPoint → ℝ)
    {m : ℕ} {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    n07bReferenceTransport S τ q a η p = n07bReferencePullback C K z a η p :=
  (n07bReferenceTransport_on_piece hτpiece hqpiece a η hp).trans
    (n07bReferencePullback_on_piece hK z a η hp).symm

/-- The current and reference canonical heights agree pointwise, with the
same subtracted left constant. -/
theorem n07bReferenceTransport_canonicalHeight
    (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsectorRef : stateSector S C.referenceState)
    (a : ℝ) (η : PolarPoint → ℝ) (m : ℕ)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K (C.referenceState, 0) m
      (fun x => n07bReferenceTransport S τ q a η x - a * S.chiLeft x.1) p =
        canonicalHeight S K z m (fun x => η x - a * S.chiLeft x.1) p := by
  have hcharts := hK.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hsectorRef m
  have hx := hcharts.2.1 hp
  calc
    _ = canonicalHeight S K (C.referenceState, 0) m
        (fun x => n07bReferencePullback C K z a η x - a * S.chiLeft x.1) p := by
      dsimp only [canonicalHeight]
      rw [n07bReferenceTransport_eq_pullback_on_piece hτpiece hqpiece hK a η hx]
    _ = _ := n07bReferencePullback_canonicalHeight hK href hsectorRef z a η m hp

/-- The same identities give the actual canonical a.e. representatives. -/
theorem n07bReferenceTransport_canonicalHeight_ae
    (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsectorRef : stateSector S C.referenceState)
    (a : ℝ) (η : PolarPoint → ℝ) (m : ℕ) :
    canonicalHeight S K (C.referenceState, 0) m
      (fun x => n07bReferenceTransport S τ q a η x - a * S.chiLeft x.1)
      =ᵐ[canonicalMeasure S K m]
        canonicalHeight S K z m (fun x => η x - a * S.chiLeft x.1) := by
  have hm : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hm] with p hp
  exact n07bReferenceTransport_canonicalHeight hτpiece hqpiece hK href hsectorRef a η m
    (show p ∈ canonicalOpen S K m from ⟨hp.1, mem_univ _⟩)

/-- The actual radial exceptional set is null on the full physical strip.
Thus boundary choices do not change the reference representative's a.e. class. -/
theorem n07bReferenceTransport_ae_eq_pullback
    (hK : N04PartA D S C K base ε) (a : ℝ) (η : PolarPoint → ℝ) :
    n07bReferenceTransport S τ q a η =ᵐ[radialPhysicalMeasure D]
      n07bReferencePullback C K z a η := by
  obtain ⟨E, hE, hcover⟩ := hK.2.2.2.2.2.2.1
  have hr : ∀ᵐ r : ℝ ∂volume, r ∉ E := by
    apply ae_iff.mpr
    simpa only [not_not, setOf_mem_eq] using hE
  have houtside : ∀ᵐ p : PolarPoint ∂volume, p.1 ∉ E := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hr
  change ∀ᵐ p ∂volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) (2 * Real.pi)),
    n07bReferenceTransport S τ q a η p = n07bReferencePullback C K z a η p
  apply (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioc)).mpr
  filter_upwards [houtside] with p hpE hpstrip
  obtain ⟨m, hm, _⟩ := hcover p.1 ⟨hpstrip.1, hpE⟩
  exact n07bReferenceTransport_eq_pullback_on_piece hτpiece hqpiece hK a η
    (show p ∈ physicalPieceOpen S K m from ⟨hm, mem_univ _⟩)

/-- The physical row is retained by the geometric representative. Its proof
uses the frozen normalization region and the actual a.e. atlas cover. -/
theorem n07bReferenceTransport_referenceRow
    (hK : N04PartA D S C K base ε) (hab : D.a ≤ D.b)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (a : ℝ) (η : PolarPoint → ℝ) :
    referenceRow D (n07bReferenceTransport S τ q a η) = referenceRow D η :=
  (n07b_referenceRow_congr_ae hab
    (n07bReferenceTransport_ae_eq_pullback hτpiece hqpiece hK a η)).trans
      (n07bReferencePullback_referenceRow hK hz hsector a η)

end ActualAtlas

end ContinuousFlexibility.Analysis
