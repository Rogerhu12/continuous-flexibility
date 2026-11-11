import ContinuousFlexibility.Radial.CentralBorderLocality
import ContinuousFlexibility.Radial.ReferenceTrueBorder

/-!
# A central border fixed before choosing the connected reference

The cap is fixed in model coordinates, between sqrt(A)+1 and sqrt(A)+2,
and both the central profile scale and kernel amplitude equal one.  Its
normalized metric control, physical column and model inverse constants
therefore precede every later choice of the retained central window.
Installing this same control preserves the physical column globally.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

def fixedCentralCapLeft : ℝ := centralRadius (sqrt centralOscillatorA + 1)
def fixedCentralCapRight : ℝ := centralRadius (sqrt centralOscillatorA + 2)

theorem fixedCentralCap_order :
    0 < fixedCentralCapLeft ∧
      centralRadius (sqrt centralOscillatorA) < fixedCentralCapLeft ∧
      fixedCentralCapLeft < fixedCentralCapRight := by
  unfold fixedCentralCapLeft fixedCentralCapRight
  exact ⟨centralRadius_pos _,
    strictMono_centralRadius (by linarith),
    strictMono_centralRadius (by linarith)⟩

/-- The genuine radial metric-variation column of the fixed central model. -/
def fixedCentralColumn (χ : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialJacobi 4 (fun t => centralRadialProfile 1 t * χ t) centralKernelHeight r

structure FixedCentralBorder where
  chi : ℝ → ℝ
  chi_smooth : ContDiff ℝ ∞ chi
  chi_compact : HasCompactSupport chi
  chi_support : tsupport chi ⊆ Ioo fixedCentralCapLeft fixedCentralCapRight
  chi_nonzero : ∃ r, chi r ≠ 0
  column_smooth : ContDiff ℝ ∞ (fixedCentralColumn chi)
  column_compact : HasCompactSupport (fixedCentralColumn chi)
  column_support : tsupport (fixedCentralColumn chi) ⊆
    Ioo fixedCentralCapLeft fixedCentralCapRight
  column_pairing : (∫ r : ℝ, fixedCentralColumn chi r * centralKernelHeight r) = 1

/-- Construct the normalized control using only the fixed central model. -/
theorem exists_fixedCentralBorder : Nonempty FixedCentralBorder := by
  have hl : 0 < fixedCentralCapLeft := fixedCentralCap_order.1
  have hlh : fixedCentralCapLeft < fixedCentralCapRight := fixedCentralCap_order.2.2
  have hwlocal (r : ℝ) (hr : 0 < r) :
      ContDiffAt ℝ ∞ (centralRadialProfile 1) r := by
    have h := contDiffAt_centralRadialProfile 1 (centralModelCoordinate r)
    rwa [centralRadius_modelCoordinate hr] at h
  have hφlocal (r : ℝ) (hr : 0 < r) : ContDiffAt ℝ ∞ centralKernelHeight r := by
    have h := contDiffAt_centralKernelHeight (centralModelCoordinate r)
    rwa [centralRadius_modelCoordinate hr] at h
  obtain ⟨w, hw, hwmodel⟩ := exists_contDiff_eqOn_positive_interval hl hlh hwlocal
  obtain ⟨φ, hφ, hφmodel⟩ := exists_contDiff_eqOn_positive_interval hl hlh hφlocal
  obtain ⟨χ, hχs, hχc, hχcap, hχne, _, hgs, hgc, hgcap, hpair, _⟩ :=
    exists_central_true_border hw hφ (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≠ 0) hl hlh
      (by linarith : fixedCentralCapRight < fixedCentralCapRight + 1)
      fixedCentralCap_order.2.1.le hwmodel
      (by simpa only [one_mul] using hφmodel)
  let g : ℝ → ℝ := fun r => radialJacobi 4 (fun t => w t * χ t) φ r
  have hcol : g = fixedCentralColumn χ :=
    radialJacobi_border_congr_on_support isOpen_Ioo hχcap hwmodel hφmodel
  change ContDiff ℝ ∞ g at hgs
  change HasCompactSupport g at hgc
  change tsupport g ⊆ Ioo fixedCentralCapLeft fixedCentralCapRight at hgcap
  have hpair' : (∫ r : ℝ, fixedCentralColumn χ r * centralKernelHeight r) = 1 := by
    calc
      _ = ∫ r : ℝ, g r * φ r := by
        apply integral_congr_ae
        exact Eventually.of_forall fun r => by
          change fixedCentralColumn χ r * centralKernelHeight r = g r * φ r
          rw [← congrFun hcol r]
          by_cases hr : r ∈ Ioo fixedCentralCapLeft fixedCentralCapRight
          · rw [hφmodel hr]
          · have hz : g r = 0 :=
              (notMem_tsupport_iff_eventuallyEq.mp
                (show r ∉ tsupport g from fun ht => hr (hgcap ht))).eq_of_nhds
            rw [hz, zero_mul, zero_mul]
      _ = 1 := hpair
  exact ⟨⟨χ, hχs, hχc, hχcap, hχne,
    hcol ▸ hgs, hcol ▸ hgc, hcol ▸ hgcap, hpair'⟩⟩

namespace FixedCentralBorder

/-- The later connected construction does not change the already fixed column. -/
theorem reference_column (B : FixedCentralBorder) {D : ReferenceData}
    (hw : EqOn D.w (centralRadialProfile 1)
      (Ioo fixedCentralCapLeft fixedCentralCapRight))
    (hφ : EqOn D.phi centralKernelHeight
      (Ioo fixedCentralCapLeft fixedCentralCapRight)) :
    referenceColumn (referenceWithTrueBorderControls D B.chi) = fixedCentralColumn B.chi := by
  rw [referenceWithTrueBorderControls_column]
  exact radialJacobi_border_congr_on_support isOpen_Ioo B.chi_support hw hφ

/-- Install the same preselected control in any reference retaining the fixed
model cap.  The normalized pairing is the genuine annular dr pairing. -/
theorem install (B : FixedCentralBorder) {D : ReferenceData}
    (hal : D.a < fixedCentralCapLeft) (hhb : fixedCentralCapRight < D.b)
    (hw : EqOn D.w (centralRadialProfile 1)
      (Ioo fixedCentralCapLeft fixedCentralCapRight))
    (hφ : EqOn D.phi centralKernelHeight
      (Ioo fixedCentralCapLeft fixedCentralCapRight)) :
    RadialTrueBorder (referenceWithTrueBorderControls D B.chi) ∧
      referenceColumn (referenceWithTrueBorderControls D B.chi) =
        fixedCentralColumn B.chi := by
  have hcol := B.reference_column hw hφ
  have hsupp : Function.support (fun r => fixedCentralColumn B.chi r * D.phi r) ⊆
      Ioc D.a D.b := by
    intro r hr
    have hgne : fixedCentralColumn B.chi r ≠ 0 := by
      intro hz
      exact hr (by change fixedCentralColumn B.chi r * D.phi r = 0; rw [hz, zero_mul])
    have hi := B.column_support (subset_tsupport (fixedCentralColumn B.chi) hgne)
    exact ⟨hal.trans hi.1, hi.2.le.trans hhb.le⟩
  have hproduct : (fun r => fixedCentralColumn B.chi r * D.phi r) =
      (fun r => fixedCentralColumn B.chi r * centralKernelHeight r) := by
    funext r
    by_cases hr : r ∈ Ioo fixedCentralCapLeft fixedCentralCapRight
    · rw [hφ hr]
    · have hz : fixedCentralColumn B.chi r = 0 := by
        by_contra hne
        exact hr (B.column_support (subset_tsupport (fixedCentralColumn B.chi) hne))
      rw [hz, zero_mul, zero_mul]
  have hpair : (∫ r in D.a..D.b,
      referenceColumn (referenceWithTrueBorderControls D B.chi) r * D.phi r) = 1 := by
    rw [hcol, intervalIntegral.integral_eq_integral_of_support_subset hsupp, hproduct]
    exact B.column_pairing
  have hab : D.a < D.b := hal.trans (fixedCentralCap_order.2.2.trans hhb)
  refine ⟨⟨B.chi_smooth, B.chi_compact, ?_, hpair,
    contDiff_referenceLeftCutoff D.a D.b,
    referenceLeftCutoff_endpoint_germs hab⟩, hcol⟩
  intro r hr
  have hi := B.chi_support (subset_tsupport B.chi hr)
  refine ⟨⟨hal.trans hi.1, hi.2.trans hhb⟩, ?_⟩
  change 0 < deriv D.w r
  rw [hw.deriv isOpen_Ioo hi]
  exact (central_right_cap_signs (by norm_num : (0 : ℝ) < 1)
    (fixedCentralCap_order.2.1.trans hi.1)).1

end FixedCentralBorder
end ContinuousFlexibility.Radial
