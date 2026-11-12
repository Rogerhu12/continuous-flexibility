import ContinuousFlexibility.Analysis.N07aAngularCutoff
import ContinuousFlexibility.Analysis.N07aAngularIntervalRestriction

/-!
# Actual compact inner radial intervals and their cutoff tests

Only the radial interval of the original canonical data is replaced.
The resulting canonical measure is exactly the physical half-period
measure on that interval. A real smooth bump supplies the compact test
equal to one on any prescribed strictly smaller closed interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n07aRadialIntervalData {S : PhysicalSpacesData} (K : CanonicalData S) (a b : ℝ) :
    CanonicalData S := { K with left := fun _ => a, right := fun _ => b }

variable {S : PhysicalSpacesData} {K : CanonicalData S}

theorem n07a_innerInterval_cutoff {a l r b : ℝ}
    (hal : a < l) (hlr : l < r) (hrb : r < b) :
    ∃ ξ : ℝ → ℝ,
      CanonicalTest S (n07aRadialIntervalData K a b) 0 (fun p => ξ p.1) ∧
      ∀ x ∈ Icc l r, ξ x = 1 := by
  let c := (l + r) / 2
  let d := (r - l) / 2
  let e := min (c - a) (b - c)
  have hd : 0 < d := by dsimp only [d]; linarith
  have hde : d < e := by
    apply lt_min
    · dsimp only [c, d]; linarith
    · dsimp only [c, d]; linarith
  let χ : ContDiffBump c :=
    { rIn := d
      rOut := (d + e) / 2
      rIn_pos := hd
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport χ ⊆ Ioo a b := by
    rw [χ.tsupport_eq]
    intro x hx
    have hx' := Metric.mem_closedBall.mp hx
    rw [Real.dist_eq, abs_le] at hx'
    have heL : e ≤ c - a := min_le_left _ _
    have heR : e ≤ b - c := min_le_right _ _
    change -((d + e) / 2) ≤ x - c ∧ x - c ≤ (d + e) / 2 at hx'
    constructor <;> linarith
  refine ⟨χ, ⟨χ.contDiff.comp contDiff_fst, ?_, tsupport χ,
    χ.hasCompactSupport, hsupport, ?_⟩, ?_⟩
  · intro p
    simp only [Prod.fst_add, add_zero]
  · intro x hx θ
    exact image_eq_zero_of_notMem_tsupport hx
  · intro x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -d ≤ x - c ∧ x - c ≤ d
    dsimp only [c, d]
    constructor <;> linarith [hx.1, hx.2]

theorem n07a_radialInterval_measure_mono {a b l r : ℝ}
    (h : Ioo l r ⊆ Ioo a b) :
    canonicalMeasure S (n07aRadialIntervalData K l r) 0 ≤
      canonicalMeasure S (n07aRadialIntervalData K a b) 0 :=
  Measure.restrict_mono_set _ (Set.prod_mono h Subset.rfl)

end ContinuousFlexibility.Analysis
