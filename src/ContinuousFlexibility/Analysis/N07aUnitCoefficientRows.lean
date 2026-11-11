import ContinuousFlexibility.Analysis.N07aCircleBlockBounds
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Statements.N07aCanonicalGeometry

/-!
# Actual unit-coordinate coefficient rows

Spatial jets on the open unit strip restrict to smooth periodic circle
rows. The prescribed current-minus-reference geometric jets therefore
give the actual Fourier coefficient bounds used in the block proof.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

def n07aUnitJetRow (f : PolarPoint → ℝ) (i j : ℕ) (x θ : ℝ) : ℝ :=
  mixedDerivative i j f (x, θ)

theorem n07aUnitJetRow_contDiff {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (i j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (n07aUnitJetRow f i j x) := by
  apply contDiffOn_univ.mp
  exact (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf i j).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hx, mem_univ _⟩)

theorem n07aUnitJetRow_periodic {f : PolarPoint → ℝ}
    (hp : ∀ p ∈ unitStrip, f (p + (0, Real.pi)) = f p)
    (i j : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Function.Periodic (n07aUnitJetRow f i j x) Real.pi := by
  intro θ
  have he : (fun r => iteratedDeriv j (fun t => f (r, t)) (θ + Real.pi)) =ᶠ[𝓝 x]
      fun r => iteratedDeriv j (fun t => f (r, t)) θ := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with r hr
    have hpr : Function.Periodic (fun t => f (r, t)) Real.pi := by
      intro t
      simpa only [Prod.mk_add_mk, add_zero] using hp (r, t) ⟨hr, mem_univ _⟩
    exact circleFourier_periodic_iteratedDeriv hpr j θ
  exact he.iteratedDeriv_eq i

theorem n07aUnitJetRow_iteratedDeriv {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f unitStrip) (i j k : ℕ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (θ : ℝ) :
    iteratedDeriv k (n07aUnitJetRow f i j x) θ = mixedDerivative i (k + j) f (x, θ) := by
  change mixedDerivative 0 k (mixedDerivative i j f) (x, θ) = _
  simpa only [Nat.zero_add] using n07a_mixedDerivative_mixedDerivative_on
    (isOpen_Ioo.prod isOpen_univ) hf 0 k i j ⟨hx, mem_univ _⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

def n07aUnitDifferenceAtom (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : Parameter S) (m : ℕ) (a : Atom) (p : PolarPoint) : ℝ :=
  atom D T S C L K (liftSectorParameter S C z) m a p -
    atom D T S C L K (C.referenceState, 0) m a p

theorem n07aUnitDifferenceAtom_contDiff
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (a : Atom) :
    ContDiffOn ℝ ∞ (n07aUnitDifferenceAtom D T S C L K z m a) unitStrip :=
  (hcur.1 z hz m a).1.sub (href.1 m a).1

theorem n07aUnitDifferenceAtom_periodic
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ) (a : Atom) :
    ∀ p ∈ unitStrip,
      n07aUnitDifferenceAtom D T S C L K z m a (p + (0, Real.pi)) =
        n07aUnitDifferenceAtom D T S C L K z m a p := by
  intro p hp
  exact congrArg₂ (· - ·) ((hcur.1 z hz m a).2 p hp) ((href.1 m a).2 p hp)

theorem n07aUnitDifferenceAtom_jet (z : Parameter S) (m : ℕ) (a : Atom)
    (i j : ℕ) (p : unitStrip) :
    mixedDerivative i j (n07aUnitDifferenceAtom D T S C L K z m a) p.val =
      differenceJets D T S C L K z a m i j p := rfl

end ContinuousFlexibility.Analysis
