import ContinuousFlexibility.Analysis.N07aAngularMaterialEmbedding

/-!
# Material regularity of the already constructed relative inverse

N06 supplies the genuine identity `u = F - R u`.  A weighted realization
of `R u` therefore gives a weighted realization of this same `u` by
subtraction.  The final estimate combines one high angular norm with a
single high state factor.  The relative gain is an input proved from the
actual coefficients in the companion analytic modules, not a new premise
of N07a or a replacement for that analytic step.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {L : ReturnCorrectionData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b} {P : RelativeInverseData S K V b B}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

local instance n07aMaterialLiftLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _

local instance n07aMaterialLiftLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

theorem n07aAngularRelativeInverse_eq_sub
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    P.inverse z F = F - P.relative z (P.inverse z F) :=
  eq_sub_iff_add_eq.mpr ((h06.2 z hz hsector).2.2.2.2.1 F).2

/-- The weighted representative is obtained by subtraction in the actual graph. -/
theorem n07aAngularRelativeInverse_materialLift_of_gain
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) {γ t : ℝ} {s : ℕ}
    (Fts Rts : V.level γ t s)
    (hF : V.forget γ t s Fts = V.forget (3 / 4 : ℝ) 0 b F)
    (hR : V.forget γ t s Rts =
      V.forget (3 / 4 : ℝ) 0 b (P.relative z (P.inverse z F))) :
    ∃ Uts : V.level γ t s,
      V.forget γ t s Uts = V.forget (3 / 4 : ℝ) 0 b (P.inverse z F) ∧
      ‖Uts‖ ≤ ‖Fts‖ + ‖Rts‖ := by
  refine ⟨Fts - Rts, ?_, norm_sub_le Fts Rts⟩
  rw [map_sub, hF, hR, ← map_sub]
  exact congrArg (V.forget (3 / 4 : ℝ) 0 b)
    (n07aAngularRelativeInverse_eq_sub h06 hz hsector F).symm

private theorem n07aAngularMaterialLift_numeric
    {X Y U R Z V a c k N : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (hZ : Z ≤ X + R) (hR : R ≤ a * U + c * N * V)
    (hU : U ≤ k * (X + N * Y)) (hV : V ≤ 2 * Y) :
    Z ≤ (1 + a * k + 2 * c) * (X + N * Y) := by
  calc
    Z ≤ X + (a * U + c * N * V) := hZ.trans (add_le_add le_rfl hR)
    _ ≤ X + (a * (k * (X + N * Y)) + c * N * (2 * Y)) :=
      add_le_add le_rfl
        (add_le_add (mul_le_mul_of_nonneg_left hU ha)
          (mul_le_mul_of_nonneg_left hV (mul_nonneg hc hN)))
    _ ≤ (1 + a * k + 2 * c) * (X + N * Y) := by
      nlinarith [mul_nonneg hc hX, mul_nonneg hN hY]

/-- The one-high estimate remains linear in the high state size after
substituting the angular resolvent estimate into the material gain. -/
theorem n07aAngularRelativeInverse_materialLift_bound
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) {t : ℝ} {s : ℕ}
    (Fts : V.level (3 / 4 : ℝ) t s)
    (hF : V.forget (3 / 4 : ℝ) t s Fts = V.forget (3 / 4 : ℝ) 0 b F)
    (U0s : V.level (3 / 4 : ℝ) 0 s)
    (hU : V.forget (3 / 4 : ℝ) 0 s U0s =
      V.forget (3 / 4 : ℝ) 0 b (P.inverse z F))
    {a c k N : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (hangular : ‖U0s‖ ≤ k * (‖Fts‖ + N * ‖F‖))
    (hgain : ∀ U : V.level (3 / 4 : ℝ) 0 s,
      V.forget (3 / 4 : ℝ) 0 s U = V.forget (3 / 4 : ℝ) 0 b (P.inverse z F) →
      ∃ Rts : V.level (3 / 4 : ℝ) t s,
        V.forget (3 / 4 : ℝ) t s Rts =
          V.forget (3 / 4 : ℝ) 0 b (P.relative z (P.inverse z F)) ∧
        ‖Rts‖ ≤ a * ‖U‖ + c * N * ‖P.inverse z F‖) :
    ∃ Uts : V.level (3 / 4 : ℝ) t s,
      V.forget (3 / 4 : ℝ) t s Uts = V.forget (3 / 4 : ℝ) 0 b (P.inverse z F) ∧
      ‖Uts‖ ≤ (1 + a * k + 2 * c) * (‖Fts‖ + N * ‖F‖) := by
  obtain ⟨Rts, hR, hRbound⟩ := hgain U0s hU
  obtain ⟨Uts, hUts, hnorm⟩ :=
    n07aAngularRelativeInverse_materialLift_of_gain h06 hz hsector F Fts Rts hF hR
  have hbase : ‖P.inverse z F‖ ≤ 2 * ‖F‖ :=
    ((P.inverse z).le_opNorm F).trans
      (mul_le_mul_of_nonneg_right (h06.2 z hz hsector).2.2.2.2.2 (norm_nonneg F))
  exact ⟨Uts, hUts, n07aAngularMaterialLift_numeric (norm_nonneg Fts) (norm_nonneg F)
    ha hc hN hnorm hRbound hangular hbase⟩

/-- Every realization of the same weighted source is equal, so the lift
agrees with all later weighted or smooth realizations of the inverse. -/
theorem n07aAngularMaterialLift_unique
    {T : MaterialData} (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} {U W : V.level γ t s}
    {f : CanonicalSequence S K}
    (hU : V.forget γ t s U = f) (hW : V.forget γ t s W = f) : U = W :=
  hV.2.2.1 γ t s (hU.trans hW.symm)

end ContinuousFlexibility.Statements
