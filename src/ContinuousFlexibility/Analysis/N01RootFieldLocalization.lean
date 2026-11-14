module

public import ContinuousFlexibility.Analysis.N01RootFieldFDerivBounds
public import ContinuousFlexibility.Analysis.RootFieldLocalization

/-!
# Actual globally smooth periodic root fields on the common N01 strip

The localization is fixed before the state. It preserves the actual
fields and every ordinary jet in the physical quarter-strip, while
providing genuine global smoothness and angular periodicity for Picard
existence outside the parameter box used in the estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def localizedRootDrift (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (r σ : ℝ) {R : ℝ} (hR : 0 < R)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  rootFieldLocalization
    (orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ) hR

def localizedRootSpeed (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (g : ℝ → ℝ) (r σ : ℝ) {R : ℝ} (hR : 0 < R)
    (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  rootFieldLocalization
    (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1) (stateHeight D S C z) r σ) hR

theorem periodic_stateHeight_of_physicalSpaces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) : Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  have hh := (hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1
  have hperiod := hh.2.2.1
  intro q
  simp only [stateHeight, stateU, heightPairField, Prod.fst_add, add_zero, hperiod q]

theorem periodic_localizedRootFields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (r σ : ℝ) {R : ℝ} (hR : 0 < R) (z : AnnularState S × ℝ) :
    (∀ x, Function.Periodic (fun θ => localizedRootDrift D S C r σ hR z (x, θ)) Real.pi) ∧
      (∀ x, Function.Periodic (fun θ => localizedRootSpeed D S C g r σ hR z (x, θ)) Real.pi) := by
  have hperiod := periodic_factoredCharacteristicField D.w g (stateProfile D S C z.1)
    (r := r) (σ := σ) (periodic_stateHeight_of_physicalSpaces hS C z)
  exact ⟨rootFieldLocalization_periodic hR hperiod.2,
    rootFieldLocalization_periodic hR hperiod.1⟩

theorem contDiff_localizedRootFields_of_n01
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {r σ R : ℝ} (hR : 0 < R)
    {z : AnnularState S × ℝ}
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ R) :
    ContDiff ℝ ∞ (localizedRootDrift D S C r σ hR z) ∧
      ContDiff ℝ ∞ (localizedRootSpeed D S C g r σ hR z) := by
  obtain ⟨_, hD⟩ := hN.1.1
  have hwref : ContDiff ℝ ∞ D.w := hD.1.2.2.1.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hZ := contDiff_stateHeight_of_n01 hS hT hN z
  have hregular (q : PolarPoint) (hq : q ∈ Ioo (-R) R ×ˢ (univ : Set ℝ)) :
      ContDiffAt ℝ ∞ (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) q ∧
      ContDiffAt ℝ ∞ (orientedCharacteristicDrift (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) q := by
    have hpouter : q ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
      refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith [hq.1.1, hq.1.2]
    obtain ⟨hrq, hwq, hgq, hDq, hQq, _, _⟩ := hstrip q hpouter
    exact contDiffAt_factoredCharacteristicField hwref hg hw hZ hrq hwq hgq hDq hQq
  exact ⟨contDiff_rootFieldLocalization hR (fun q hq => (hregular q hq).2.contDiffWithinAt),
    contDiff_rootFieldLocalization hR (fun q hq => (hregular q hq).1.contDiffWithinAt)⟩

theorem iteratedFDeriv_localizedRootFields_eq
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (r σ : ℝ) {R : ℝ} (hR : 0 < R)
    (z : AnnularState S × ℝ) (n : ℕ) {q : PolarPoint} (hq : |q.1| ≤ R / 4) :
    iteratedFDeriv ℝ n (localizedRootDrift D S C r σ hR z) q =
        iteratedFDeriv ℝ n
          (orientedCharacteristicDrift (stateProfile D S C z.1) (stateHeight D S C z) r σ) q ∧
      iteratedFDeriv ℝ n (localizedRootSpeed D S C g r σ hR z) q =
        iteratedFDeriv ℝ n
          (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
            (stateHeight D S C z) r σ) q :=
  ⟨iteratedFDeriv_rootFieldLocalization_eq hR n hq,
    iteratedFDeriv_rootFieldLocalization_eq hR n hq⟩

end ContinuousFlexibility.Analysis
