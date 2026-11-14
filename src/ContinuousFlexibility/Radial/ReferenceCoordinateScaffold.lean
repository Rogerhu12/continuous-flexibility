module

public import ContinuousFlexibility.Radial.ReferenceCoordinate

/-!
# Transport of actual trace intervals

The widths are divided by the forward Lipschitz constant.  The resulting
closed intervals remain inside their actual pulled-back cells, and the
open intervals remain pairwise disjoint.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

theorem radialTraceScaffold_coordinateReference {D : ReferenceData}
    (e : ℝ ≃o ℝ) {L : ℝ} (hL : 0 < L)
    (hforward : ∀ x y : ℝ, |e x - e y| ≤ L * |x - y|)
    (hD : RadialTraceScaffold D) :
    RadialTraceScaffold (coordinateReference D e) := by
  rcases hD with ⟨centers, widths, K, hK, hcell, hdisj⟩
  let K' : ℝ := L * K + K + 1
  have hLK : 0 < L * K := mul_pos hL hK
  have hK' : 0 < K' := by dsimp only [K']; linarith
  have hKK' : K ≤ K' := by dsimp only [K']; linarith
  have hLKK' : L * K ≤ K' := by dsimp only [K']; linarith
  have hinside (m : ℕ) {r : ℝ}
      (hr : r ∈ Ioo (e.symm (centers m) - widths m / L)
        (e.symm (centers m) + widths m / L)) :
      e r ∈ Ioo (centers m - widths m) (centers m + widths m) := by
    have habs : |r - e.symm (centers m)| < widths m / L :=
      abs_lt.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hbound : |e r - centers m| < widths m := by
      calc
        _ ≤ L * |r - e.symm (centers m)| := by
          simpa only [e.apply_symm_apply] using hforward r (e.symm (centers m))
        _ < L * (widths m / L) := mul_lt_mul_of_pos_left habs hL
        _ = widths m := by field_simp [hL.ne']
    have hb := abs_lt.mp hbound
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  refine ⟨fun m => e.symm (centers m), fun m => widths m / L,
    K', hK', ?_, ?_⟩
  · intro m
    obtain ⟨hcenter, hwidth, hbound, hsub⟩ := hcell m
    refine ⟨?_, div_pos hwidth hL, ?_, ?_⟩
    · change e (e.symm (centers m)) ∈ D.cells m
      simpa only [e.apply_symm_apply] using hcenter
    · have hE : 1 ≤ radialE (D.cellIndex m) :=
        one_le_exp_iff.mpr (radialQ_nonneg _)
      have hp : radialE (D.cellIndex m) ^ (-K') ≤
          radialE (D.cellIndex m) ^ (-K) :=
        Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg hKK')
      calc
        _ ≤ (L * K)⁻¹ * radialE (D.cellIndex m) ^ (-K) :=
          mul_le_mul (inv_anti₀ hLK hLKK') hp
            (Real.rpow_nonneg (zero_le_one.trans hE) _)
            (inv_nonneg.mpr hLK.le)
        _ = (K⁻¹ * radialE (D.cellIndex m) ^ (-K)) / L := by
          simp only [mul_inv_rev, div_eq_mul_inv]
          ring
        _ ≤ widths m / L := div_le_div_of_nonneg_right hbound hL.le
    · intro r hr
      have habs : |r - e.symm (centers m)| ≤ widths m / L :=
        abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hbound' : |e r - centers m| ≤ widths m := by
        calc
          _ ≤ L * |r - e.symm (centers m)| := by
            simpa only [e.apply_symm_apply] using hforward r (e.symm (centers m))
          _ ≤ L * (widths m / L) := mul_le_mul_of_nonneg_left habs hL.le
          _ = widths m := by field_simp [hL.ne']
      have hb := abs_le.mp hbound'
      exact hsub ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · intro m n hmn
    apply Set.disjoint_left.mpr
    intro r hrm hrn
    exact Set.disjoint_left.mp (hdisj hmn) (hinside m hrm) (hinside n hrn)

end ContinuousFlexibility.Radial
