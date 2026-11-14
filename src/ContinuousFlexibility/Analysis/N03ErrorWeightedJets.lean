module

public import ContinuousFlexibility.Analysis.N03ErrorHomogeneousBounds
public import ContinuousFlexibility.Scalar.WeightedOrdinaryPointwise

/-!
# Actual spatial jets of the N03 source error

The physical Sobolev decoding theorem costs exactly two grading orders
and one material-envelope factor. Combining it with the actual ordered
fiber estimate preserves the residual factor and a common loss at all
spatial orders. Constants are chosen before the state, residual, test
and evaluation point. No bound for an effective coefficient is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem weighted_error_scalar_bound {x C H M q B V : ℝ}
    (hweight : 0 ≤ C * H * M) (hx : x ≤ C * H * M * q) (hq : q ≤ B * V) :
    x ≤ (C * B) * H * M * V := by
  calc
    x ≤ C * H * M * (B * V) :=
      hx.trans (mul_le_mul_of_nonneg_left hq hweight)
    _ = (C * B) * H * M * V := by ring

/-- Package the decoding estimate before specializing any projective
spaces. Only real-valued functions occur in this numerical argument. -/
private theorem weighted_mixed_bound_of_homogeneous
    {Z E F G V P : Type*} {U : Set Z} {Ω : Set P}
    {a : ℕ → Z → ℝ} {p : ℕ → E → ℝ} {q : ℕ → F → ℝ}
    {r : ℕ → G → ℝ} {s : ℕ → V → ℝ}
    {A : Z → E → F → G} {ι : G → V}
    {jet : ℕ → ℕ → V → P → ℝ} {H M : P → ℝ}
    (herror : ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ k : ℕ, low ≤ k → ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, a low z < δ → ∀ e : E, ∀ f : F,
          r k (A z e f) ≤ B *
            ((1 + a (k + loss) z) * (p low e * q low f) +
              (p (k + loss) e * q low f + p low e * q (k + loss) f)))
    (hgrade : ∀ n m : ℕ, n ≤ m → ∀ u : G, s n (ι u) ≤ r m u)
    (hdecode : ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : V, ∀ x ∈ Ω, jet i j u x ≤ C * H x * M x * s (i + j + 2) u)
    (hH : ∀ x ∈ Ω, 0 ≤ H x) (hM : ∀ x ∈ Ω, 0 ≤ M x) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ i j : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ z ∈ U, a low z < δ → ∀ e : E, ∀ f : F, ∀ x ∈ Ω,
          jet i j (ι (A z e f)) x ≤ B * H x * M x *
            ((1 + a (i + j + loss) z) * (p low e * q low f) +
              (p (i + j + loss) e * q low f + p low e * q (i + j + loss) f)) := by
  obtain ⟨loss, low, δ, hδ, herror⟩ := herror
  refine ⟨2 + low + loss, low, δ, hδ, ?_⟩
  intro i j
  obtain ⟨C, hC, hpoint⟩ := hdecode i j
  obtain ⟨B, hB, herror⟩ := herror (i + j + 2 + low) (by omega)
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro z hz hlow e f x hx
  have herr := herror z hz hlow e f
  have horder : i + j + 2 + low + loss = i + j + (2 + low + loss) := by omega
  rw [horder] at herr
  have hq := (hgrade (i + j + 2) (i + j + 2 + low) (by omega) (A z e f)).trans herr
  exact weighted_error_scalar_bound (mul_nonneg (mul_nonneg hC (hH x hx)) (hM x hx))
    (hpoint (ι (A z e f)) x hx) hq

/-- The decoded N03 error has genuine mixed spatial derivative bounds
with one common loss and one factor from each independent fiber. -/
theorem n03Error_mixedDerivative_weighted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hε : 0 < ε) (hN03 : N03Properties D T S C R L base ε) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ a b : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ v ∈ sectorNeighborhood S base ε ε,
          pairGrading (sectorGrading S) realGrading low v < δ →
          ∀ r : CircleSpace S, ∀ η : HeightPair S, ∀ p ∈ annularOpen D,
            |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode
                ((L.error (liftSectorParameter S C v) r η).val)) p| ≤
              B * T.H p.1 ^ (3 / 4 : ℝ) * T.M p.1 *
                ((1 + pairGrading (sectorGrading S) realGrading (a + b + loss) v) *
                    ((S.circle (3 / 4 : ℝ)).grading low r * heightPairGrading S low η) +
                  ((S.circle (3 / 4 : ℝ)).grading (a + b + loss) r *
                      heightPairGrading S low η +
                    (S.circle (3 / 4 : ℝ)).grading low r *
                      heightPairGrading S (a + b + loss) η)) := by
  exact weighted_mixed_bound_of_homogeneous
    (Z := StateDirections S × ℝ) (E := CircleSpace S) (F := HeightPair S)
    (G := S.Source) (V := (S.height (3 / 4 : ℝ)).Space) (P := PolarPoint)
    (U := sectorNeighborhood S base ε ε) (Ω := annularOpen D)
    (a := fun n v => pairGrading (sectorGrading S) realGrading n v)
    (p := fun n u => (S.circle (3 / 4 : ℝ)).grading n u)
    (q := fun n u => heightPairGrading S n u)
    (r := fun n u => S.sourceGrading n u)
    (s := fun n u => (S.height (3 / 4 : ℝ)).grading n u)
    (A := fun v r η => L.error (liftSectorParameter S C v) r η)
    (ι := fun u : S.Source => u.val)
    (jet := fun i j u x => |mixedDerivative i j ((S.height (3 / 4 : ℝ)).decode u) x|)
    (H := fun x => T.H x.1 ^ (3 / 4 : ℝ)) (M := fun x => T.M x.1)
    (n03Error_homogeneous_tame_bound
      (D := D) (T := T) (S := S) (C := C) (R := R) (L := L)
      (base := base) (ε := ε) hε hN03)
    (fun n m hnm u => gradedSeminorm_monotone
      (fun k => (S.height (3 / 4 : ℝ)).level k)
      (S.height (3 / 4 : ℝ)).bond hnm u.val)
    (fun i j => mixedDerivative_decode_le_weighted_grading
      (D := D) (T := T) (γ := (3 / 4 : ℝ)) (A := S.height (3 / 4 : ℝ))
      hT (hS.1 (3 / 4 : ℝ)) i j)
    (fun x hx => (Real.rpow_pos_of_pos (hT.2.1 _ hx.1).2.1 _).le)
    (fun x hx => zero_le_one.trans (hT.2.1 _ hx.1).2.2.2)

end ContinuousFlexibility.Analysis
