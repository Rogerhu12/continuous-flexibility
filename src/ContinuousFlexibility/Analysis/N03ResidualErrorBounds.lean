import ContinuousFlexibility.Analysis.N03ErrorWeightedJets
import ContinuousFlexibility.Analysis.N02ResidualValueBounds

/-!
# The actual residual substituted into the N03 source error

The low residual grade is bounded on one fixed state ball. Its high grade
is linear in one high state grade. Substitution in the bilinear estimate
therefore preserves a fixed loss and one high factor. The two height-test
grades remain explicit; no localization in the residual or positive
material-height gain is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem residual_fiber_scalar_bound
    {x X r R h H l L t T : ℝ}
    (hx : 0 ≤ x) (hX : x ≤ X) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hh : 0 ≤ h) (hH : 0 ≤ H) (hl : 0 ≤ l) (ht : 0 ≤ t)
    (hrR : r ≤ R) (hhH : h ≤ H * (1 + X)) (hlL : l ≤ L) (htT : t ≤ T) :
    (1 + x) * (r * l) + (h * l + r * t) ≤
      (R + H) * (1 + X) * (L + T) := by
  have hX0 : 0 ≤ X := hx.trans hX
  have hL : 0 ≤ L := hl.trans hlL
  have hT : 0 ≤ T := ht.trans htT
  have hrL : r * l ≤ R * L := mul_le_mul hrR hlL hl hR
  have hhL : h * l ≤ (H * (1 + X)) * L :=
    mul_le_mul hhH hlL hl (mul_nonneg hH (by linarith))
  have hrT : r * t ≤ R * T := mul_le_mul hrR htT ht hR
  have hfirst : (1 + x) * (r * l) ≤ (1 + X) * (R * L) :=
    mul_le_mul (add_le_add (le_refl (1 : ℝ)) hX) hrL (mul_nonneg hr hl) (by linarith)
  have hR' : R ≤ (R + H) * (1 + X) := by
    calc
      R ≤ R + H := le_add_of_nonneg_right hH
      _ = (R + H) * 1 := by ring
      _ ≤ (R + H) * (1 + X) :=
        mul_le_mul_of_nonneg_left (by linarith) (add_nonneg hR hH)
  calc
    _ ≤ (1 + X) * (R * L) + ((H * (1 + X)) * L + R * T) :=
      add_le_add hfirst (add_le_add hhL hrT)
    _ = (R + H) * (1 + X) * L + R * T := by ring
    _ ≤ (R + H) * (1 + X) * L + (R + H) * (1 + X) * T :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hR' hT)
    _ = (R + H) * (1 + X) * (L + T) := by ring

private theorem weighted_error_after_residual_bound
    {Z E F P : Type*} {U : Set Z} {Ω : Set P}
    {p : ℕ → Z → ℝ} {q : ℕ → E → ℝ} {t : ℕ → F → ℝ}
    {f : Z → E} {J : ℕ → ℕ → Z → E → F → P → ℝ} {H M : P → ℝ}
    (hp : Monotone p) (ht : Monotone t)
    (hpn : ∀ n z, 0 ≤ p n z) (hqn : ∀ n e, 0 ≤ q n e)
    (htn : ∀ n v, 0 ≤ t n v)
    (hH : ∀ x ∈ Ω, 0 ≤ H x) (hM : ∀ x ∈ Ω, 0 ≤ M x)
    (hres : ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ U, p low z < δ →
        q s (f z) ≤ B * (1 + p (s + loss) z))
    (herr : ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ i j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, p low z < δ → ∀ e : E, ∀ v : F, ∀ x ∈ Ω,
          J i j z e v x ≤ B * H x * M x *
            ((1 + p (i + j + loss) z) * (q low e * t low v) +
              (q (i + j + loss) e * t low v + q low e * t (i + j + loss) v))) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ i j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, p low z < δ → ∀ v : F, ∀ x ∈ Ω,
          J i j z (f z) v x ≤ B * H x * M x * (1 + p (i + j + loss) z) *
            (t low v + t (i + j + loss) v) := by
  obtain ⟨lr, br, δr, hδr, hres⟩ := hres
  obtain ⟨le, be, δe, hδe, herr⟩ := herr
  obtain ⟨R, hR, hrbase⟩ := hres be
  let low := max br (be + lr)
  let δ := min δr (min δe 1)
  have hδ : 0 < δ := lt_min hδr (lt_min hδe (by norm_num))
  refine ⟨le + lr, low, δ, hδ, ?_⟩
  intro i j
  obtain ⟨B, hB, he⟩ := herr i j
  obtain ⟨Q, hQ, hrhigh⟩ := hres (i + j + le)
  refine ⟨B * (2 * R + Q), mul_nonneg hB (add_nonneg (by positivity) hQ), ?_⟩
  intro z hz hlow v x hx
  have hbr : p br z < δr :=
    ((hp (by dsimp only [low]; omega) z).trans_lt hlow).trans_le (min_le_left _ _)
  have hbe : p be z < δe :=
    ((hp (by dsimp only [low]; omega) z).trans_lt hlow).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hp1 : p (be + lr) z ≤ 1 :=
    ((hp (by dsimp only [low]; omega) z).trans hlow.le).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hrlo : q be (f z) ≤ 2 * R := by
    calc
      _ ≤ R * (1 + p (be + lr) z) := hrbase z hz hbr
      _ ≤ R * 2 := mul_le_mul_of_nonneg_left (by linarith) hR
      _ = 2 * R := by ring
  have hrhi : q (i + j + le) (f z) ≤ Q * (1 + p (i + j + (le + lr)) z) := by
    simpa only [Nat.add_assoc] using hrhigh z hz hbr
  have hnum := residual_fiber_scalar_bound
    (hpn (i + j + le) z) (hp (by omega : i + j + le ≤ i + j + (le + lr)) z)
    (hqn be (f z)) (show 0 ≤ 2 * R by positivity)
    (hqn (i + j + le) (f z)) hQ (htn be v) (htn (i + j + le) v)
    hrlo hrhi (ht ((Nat.le_add_right be lr).trans (le_max_right br (be + lr))) v)
    (ht (by omega : i + j + le ≤ i + j + (le + lr)) v)
  calc
    _ ≤ B * H x * M x *
        ((1 + p (i + j + le) z) * (q be (f z) * t be v) +
          (q (i + j + le) (f z) * t be v + q be (f z) * t (i + j + le) v)) :=
      he z hz hbe (f z) v x hx
    _ ≤ B * H x * M x *
        ((2 * R + Q) * (1 + p (i + j + (le + lr)) z) *
          (t low v + t (i + j + (le + lr)) v)) :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg (mul_nonneg hB (hH x hx)) (hM x hx))
    _ = (B * (2 * R + Q)) * H x * M x * (1 + p (i + j + (le + lr)) z) *
        (t low v + t (i + j + (le + lr)) v) := by ring

def N03ResidualErrorBoundAtOrder
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (R : ReturnEquationData S) (L : ReturnCorrectionData S)
    (base : ℕ) (ε : ℝ) (low : ℕ) (δ : ℝ) (loss a b : ℕ) (B : ℝ) : Prop :=
  ∀ v ∈ sectorNeighborhood S base ε ε,
    pairGrading (sectorGrading S) realGrading low v < δ →
    ∀ η : HeightPair S, ∀ x ∈ annularOpen D,
      |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode
        ((L.error (liftSectorParameter S C v) (R.residual (liftSectorParameter S C v)) η).val)) x| ≤
        B * T.H x.1 ^ (3 / 4 : ℝ) * T.M x.1 *
          (1 + pairGrading (sectorGrading S) realGrading (a + b + loss) v) *
          (heightPairGrading S low η + heightPairGrading S (a + b + loss) η)

theorem n03Error_actualResidual_mixed_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base : ℕ} {ε : ℝ} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hε : 0 < ε) (hN02 : N02Properties D T S C R base ε)
    (hN03 : N03Properties D T S C R L base ε) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      N03ResidualErrorBoundAtOrder D T S C R L base ε low δ loss a b B := by
  exact weighted_error_after_residual_bound
    (Z := StateDirections S × ℝ) (E := CircleSpace S) (F := HeightPair S) (P := PolarPoint)
    (U := sectorNeighborhood S base ε ε) (Ω := annularOpen D)
    (p := fun n v => pairGrading (sectorGrading S) realGrading n v)
    (q := fun n e => (S.circle (3 / 4 : ℝ)).grading n e)
    (t := fun n η => heightPairGrading S n η)
    (f := fun v => R.residual (liftSectorParameter S C v))
    (J := fun a b v e η x => |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode
      ((L.error (liftSectorParameter S C v) e η).val)) x|)
    (H := fun x => T.H x.1 ^ (3 / 4 : ℝ)) (M := fun x => T.M x.1)
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    (heightPairGrading_monotone S)
    (fun n v => apply_nonneg (pairGrading (sectorGrading S) realGrading n) v)
    (fun n e => apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) e)
    (fun n η => apply_nonneg (heightPairGrading S n) η)
    (fun x hx => (Real.rpow_pos_of_pos (hT.2.1 _ hx.1).2.1 _).le)
    (fun x hx => zero_le_one.trans (hT.2.1 _ hx.1).2.2.2)
    (n02Residual_allOrder_value_bound
      (D := D) (T := T) (S := S) (C := C) (R := R) (base := base) (ε := ε) hε hN02)
    (n03Error_mixedDerivative_weighted_bound
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (base := base) (ε := ε) hT hS hε hN03)

end ContinuousFlexibility.Analysis
