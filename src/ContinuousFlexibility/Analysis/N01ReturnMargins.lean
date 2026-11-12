import ContinuousFlexibility.Statements.Nonlinear

/-!
# Return margins of the actual N01 negative components

The endpoints in `NonlinearGeometryData` delimit actual negative radial
components, and their stored travel angles are the corresponding optical
integrals.  Consequently the radial reference supplies nonresonance and
small-divisor bounds for each of these angles.

The quantitative conclusion retains the actual containing radial cell as a
witness.  It does not identify that witness with `C.cell m`, or infer an
estimate in the circle grading sampled at `m`.  That further comparison is
a separate obligation in constructing the weighted circle inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The control intervals satisfy the exact radial definition of a negative
component, including both endpoint root conditions. -/
theorem controlGeometry_negativeRadialComponent
    (h : controlGeometryConditions D S C) (m : ℕ) :
    NegativeRadialComponent D (C.left m) (C.right m) := by
  rcases h with ⟨hinterval, hroots, _, hnegative, _, _, _, _, _⟩
  obtain ⟨hal, hlr, hrb⟩ := hinterval m
  obtain ⟨hl, hr, _, _⟩ := hroots m
  exact ⟨hal, hlr, hrb, hl, hr, hnegative m⟩

/-- The stored travel angle is the optical integral, with exactly the same
normalization as `RadialReturnMargins`. -/
theorem controlGeometry_travel_eq_radialTravel
    (h : controlGeometryConditions D S C) (m : ℕ) :
    C.travel m = radialTravel D (C.left m) (C.right m) := by
  rcases h with ⟨_, _, _, _, _, _, _, htravel, _⟩
  exact htravel m

/-- Transfer the reference margins to the control intervals.  The common
power is uniform, but its argument is the actual containing radial cell. -/
theorem controlGeometry_returnMargins
    (hD : IsRadialReference D) (h : controlGeometryConditions D S C) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ,
      QuadraticIrrational (C.travel m / Real.pi) ∧
      ∃ j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∃ c : ℝ, 0 < c ∧ c⁻¹ ≤ radialE (D.cellIndex j) ^ B ∧
          ∀ k : ℕ, 1 ≤ k → c / k ≤ |Real.sin (k * C.travel m)| := by
  obtain ⟨B, hB, hmargins⟩ := hD.2.2.1.2
  refine ⟨B, hB, fun m => ?_⟩
  have hm := hmargins (C.left m) (C.right m)
    (controlGeometry_negativeRadialComponent h m)
  rw [← controlGeometry_travel_eq_radialTravel h m] at hm
  exact hm

/-- Each negative interval of an N01 witness is an actual radial component. -/
theorem n01Properties_negativeRadialComponent
    (h : N01Properties D T S C base loss ε) (m : ℕ) :
    NegativeRadialComponent D (C.left m) (C.right m) :=
  controlGeometry_negativeRadialComponent h.2.2.2.1 m

/-- An N01 witness inherits the reference margins with an explicit actual
radial-cell witness for every control interval. -/
theorem n01Properties_returnMargins
    (h : N01Properties D T S C base loss ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ,
      QuadraticIrrational (C.travel m / Real.pi) ∧
      ∃ j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∃ c : ℝ, 0 < c ∧ c⁻¹ ≤ radialE (D.cellIndex j) ^ B ∧
          ∀ k : ℕ, 1 ≤ k → c / k ≤ |Real.sin (k * C.travel m)| :=
  controlGeometry_returnMargins h.1 h.2.2.2.1

/-- Every stored travel angle divided by pi is quadratic irrational. -/
theorem n01Properties_travel_quadraticIrrational
    (h : N01Properties D T S C base loss ε) (m : ℕ) :
    QuadraticIrrational (C.travel m / Real.pi) := by
  obtain ⟨_, _, hmargins⟩ := n01Properties_returnMargins h
  exact (hmargins m).1

/-- Every positive-frequency multiplier of the return operator is nonzero.
This statement is pointwise in the component and in the frequency. -/
theorem n01Properties_sin_travel_ne_zero
    (h : N01Properties D T S C base loss ε) (m k : ℕ) (hk : 1 ≤ k) :
    Real.sin (k * C.travel m) ≠ 0 := by
  obtain ⟨_, _, hmargins⟩ := n01Properties_returnMargins h
  obtain ⟨_, _, c, hc, _, hsmall⟩ := (hmargins m).2
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  exact abs_pos.mp (lt_of_lt_of_le (div_pos hc hkpos) (hsmall k hk))

/-- In particular the even positive frequencies used by the pi-periodic
circle space have nonzero return multipliers. -/
theorem n01Properties_sin_even_travel_ne_zero
    (h : N01Properties D T S C base loss ε) (m k : ℕ) (hk : 1 ≤ k) :
    Real.sin ((2 * k : ℕ) * C.travel m) ≠ 0 :=
  n01Properties_sin_travel_ne_zero h m (2 * k) (by omega)

end ContinuousFlexibility.Analysis
