import ContinuousFlexibility.Analysis.N05CanonicalRadialJetChoice
import ContinuousFlexibility.Analysis.N05CanonicalAngularJetChoice
import ContinuousFlexibility.Analysis.N05CanonicalRadialPairing
import ContinuousFlexibility.Analysis.N05ReferenceAngularWeakClosure

/-!
# Commuting the actual weak normal and angular jets

Only the genuine smooth test derivatives are commuted. The physical
identities use the full-period radial test class, and the canonical
identities use the original compact canonical tests. Consequently the
fixed derivative selections agree whenever both actual derivative pairs
have been constructed; no regularity of a global piecewise multiplier is
assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Radial
open scoped ContDiff

theorem n05_radialTest_angularJet {D : ReferenceData} {φ : PolarPoint → ℝ}
    (hφ : RadialTest D φ) (j : ℕ) : RadialTest D (mixedDerivative 0 j φ) := by
  induction j with
  | zero =>
    have hzero : mixedDerivative 0 0 φ = φ := by
      funext p
      simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
    simpa only [hzero] using hφ
  | succ j ih =>
    rw [← angularPartial_mixedDerivative hφ.1 0 j]
    exact r11b_radialTest_angularPartial ih

theorem n05_radialPartial_angularJet_commute {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    mixedDerivative 0 j (radialPartial φ) = radialPartial (mixedDerivative 0 j φ) := by
  funext p
  exact (mixedDerivative_radialPartial isOpen_univ hφ.contDiffOn 0 j (mem_univ p)).trans
    (congrFun (radialPartial_mixedDerivative hφ 0 j) p).symm

theorem n05_mixedDerivative_radial_angular_commute {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : ℕ) :
    mixedDerivative 0 j (mixedDerivative 1 0 φ) =
      mixedDerivative 1 0 (mixedDerivative 0 j φ) := by
  have hr : radialPartial φ = mixedDerivative 1 0 φ :=
    funext (fun p => radialPartial_eq_mixedDerivative_on isOpen_univ hφ.contDiffOn (mem_univ p))
  have hrj : radialPartial (mixedDerivative 0 j φ) =
      mixedDerivative 1 0 (mixedDerivative 0 j φ) :=
    funext (fun p => radialPartial_eq_mixedDerivative_on isOpen_univ
      (contDiff_mixedDerivative hφ 0 j).contDiffOn (mem_univ p))
  rw [← hr, ← hrj]
  exact n05_radialPartial_angularJet_commute hφ j

/-- The same physical normal derivative commutes with every actual weak
angular jet. The input identities already justify every pairing. -/
theorem n05_weakNormalDerivative_angularJet {D : ReferenceData}
    {u ur uj urj : PolarPoint → ℝ} {j : ℕ}
    (hr : WeakNormalDerivative D u ur)
    (hθ : n05_weakReferenceAngularJet D u uj j)
    (hrθ : n05_weakReferenceAngularJet D ur urj j) :
    WeakNormalDerivative D uj urj := by
  intro φ hφ
  rw [hθ _ (r11b_radialTest_radialPartial hφ),
    n05_radialPartial_angularJet_commute hφ.1 j,
    hr _ (n05_radialTest_angularJet hφ j), hrθ φ hφ]
  ring

/-- A radial derivative of the angular jet is the angular jet of the
radial derivative, in precisely the frozen canonical test identity. -/
theorem n05WeakCanonicalRadialDerivative_angularJet {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {u ur uj urj : CanonicalL2 S K m} {j : ℕ}
    (hr : n05WeakCanonicalRadialDerivative S K m u ur)
    (hθ : WeakCanonicalAngularDerivative S K m u uj j)
    (hrj : n05WeakCanonicalRadialDerivative S K m uj urj) :
    WeakCanonicalAngularDerivative S K m ur urj j := by
  intro φ hφ
  have hrad : CanonicalTest S K m (mixedDerivative 1 0 φ) := by
    have he : radialPartial φ = mixedDerivative 1 0 φ :=
      funext (fun p => radialPartial_eq_mixedDerivative_on isOpen_univ
        hφ.1.contDiffOn (mem_univ p))
    simpa only [he] using n05CanonicalTest_radial hφ
  rw [hrj φ hφ, hθ _ hrad, n05_mixedDerivative_radial_angular_commute hφ.1 j,
    hr _ (n05CanonicalTest_angular hφ j)]
  ring

/-- This identity concerns the single fixed selections, only on genuine
square-summable derivative pairs. -/
theorem n05CanonicalRadialJetSequence_angular_commute {S : PhysicalSpacesData}
    {K : CanonicalData S} {u ur uj urj : CanonicalL2Sequence S K} {j : ℕ}
    (hr : ∀ m, n05WeakCanonicalRadialDerivative S K m (u m) (ur m))
    (hθ : ∀ m, WeakCanonicalAngularDerivative S K m (u m) (uj m) j)
    (hrj : ∀ m, n05WeakCanonicalRadialDerivative S K m (uj m) (urj m)) :
    n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K u) j =
      n05CanonicalRadialJetSequence S K (n05CanonicalAngularJetSequence S K u j) := by
  rw [n05CanonicalRadialJetSequence_eq_of_weak hr,
    n05CanonicalAngularJetSequence_eq_of_weak hθ,
    n05CanonicalRadialJetSequence_eq_of_weak hrj]
  exact n05CanonicalAngularJetSequence_eq_of_weak (fun m =>
    n05WeakCanonicalRadialDerivative_angularJet (hr m) (hθ m) (hrj m))

end ContinuousFlexibility.Statements
