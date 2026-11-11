import ContinuousFlexibility.Radial.ProfileScalarSquares

/-!
# Algebra of scalar localized square series

All identities concern the actual representatives. Addition and
subtraction use only L2 membership of each localized term, which is enough
even before a global ordinary derivative has been reconstructed.
-/

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped BigOperators

namespace ContinuousFlexibility.Radial

theorem profileScalarCellSquare_congr_ae {D : ReferenceData} {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (radialCore D)] g) (m : ℕ) :
    profileScalarCellSquare D f m = profileScalarCellSquare D g m :=
  integral_congr_ae (hfg.mono fun r hr => by
    change (D.localizer m r * f r) ^ 2 = (D.localizer m r * g r) ^ 2
    rw [hr])

theorem profileScalarCellSquare_const_mul (D : ReferenceData)
    (c : ℝ) (f : ℝ → ℝ) (m : ℕ) :
    profileScalarCellSquare D (fun r => c * f r) m =
      c ^ 2 * profileScalarCellSquare D f m := by
  calc
    _ = ∫ r in radialCore D, c ^ 2 * (D.localizer m r * f r) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun r => by ring)
    _ = _ := integral_const_mul _ _

theorem profileScalarCellSquare_neg (D : ReferenceData) (f : ℝ → ℝ) (m : ℕ) :
    profileScalarCellSquare D (fun r => -f r) m = profileScalarCellSquare D f m := by
  simpa only [neg_one_mul, neg_one_sq, one_mul] using
    profileScalarCellSquare_const_mul D (-1) f m

theorem profileScalarCellSquare_add_le {D : ReferenceData} {f g : ℝ → ℝ} (m : ℕ)
    (hf : MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)))
    (hg : MemLp (fun r => D.localizer m r * g r) 2 (volume.restrict (radialCore D))) :
    profileScalarCellSquare D (fun r => f r + g r) m ≤
      2 * (profileScalarCellSquare D f m + profileScalarCellSquare D g m) := by
  have hfg : MemLp (fun r => D.localizer m r * (f r + g r)) 2
      (volume.restrict (radialCore D)) :=
    MemLp.ae_eq (Eventually.of_forall fun r => by
      change D.localizer m r * f r + D.localizer m r * g r =
        D.localizer m r * (f r + g r)
      ring) (hf.add hg)
  calc
    _ ≤ ∫ r in radialCore D,
        2 * ((D.localizer m r * f r) ^ 2 + (D.localizer m r * g r) ^ 2) := by
      apply integral_mono hfg.integrable_sq
        ((hf.integrable_sq.add hg.integrable_sq).const_mul 2)
      intro r
      change (D.localizer m r * (f r + g r)) ^ 2 ≤
        2 * ((D.localizer m r * f r) ^ 2 + (D.localizer m r * g r) ^ 2)
      nlinarith only [sq_nonneg (D.localizer m r * (f r - g r))]
    _ = _ := by
      rw [integral_const_mul, integral_add hf.integrable_sq hg.integrable_sq]
      rfl

theorem profileScalarCellSquare_sub_le {D : ReferenceData} {f g : ℝ → ℝ} (m : ℕ)
    (hf : MemLp (fun r => D.localizer m r * f r) 2 (volume.restrict (radialCore D)))
    (hg : MemLp (fun r => D.localizer m r * g r) 2 (volume.restrict (radialCore D))) :
    profileScalarCellSquare D (fun r => f r - g r) m ≤
      2 * (profileScalarCellSquare D f m + profileScalarCellSquare D g m) := by
  have hng : MemLp (fun r => D.localizer m r * (-g r)) 2
      (volume.restrict (radialCore D)) :=
    MemLp.ae_eq (Eventually.of_forall fun r => by
      change -(D.localizer m r * g r) = D.localizer m r * (-g r)
      ring) hg.neg
  simpa only [sub_eq_add_neg, profileScalarCellSquare_neg] using
    profileScalarCellSquare_add_le m hf hng

theorem profile_scalar_weighted_summable_congr_ae {D : ReferenceData}
    (w : ℕ → ℝ) {f g : ℝ → ℝ} (hfg : f =ᵐ[volume.restrict (radialCore D)] g) :
    Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m) ↔
      Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D g m) := by
  simp only [profileScalarCellSquare_congr_ae hfg]

theorem profile_scalar_weighted_tsum_congr_ae {D : ReferenceData}
    (w : ℕ → ℝ) {f g : ℝ → ℝ} (hfg : f =ᵐ[volume.restrict (radialCore D)] g) :
    (∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m) =
      ∑' m, w (D.cellIndex m) * profileScalarCellSquare D g m :=
  tsum_congr (fun m => congrArg (fun x => w (D.cellIndex m) * x)
    (profileScalarCellSquare_congr_ae hfg m))

theorem profile_scalar_weighted_const_mul
    {D : ReferenceData} (w : ℕ → ℝ) (c : ℝ) {f : ℝ → ℝ}
    (hs : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m)) :
    Summable (fun m => w (D.cellIndex m) *
      profileScalarCellSquare D (fun r => c * f r) m) ∧
      (∑' m, w (D.cellIndex m) * profileScalarCellSquare D (fun r => c * f r) m) =
        c ^ 2 * ∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m := by
  have he (m : ℕ) :
      w (D.cellIndex m) * profileScalarCellSquare D (fun r => c * f r) m =
        c ^ 2 * (w (D.cellIndex m) * profileScalarCellSquare D f m) := by
    rw [profileScalarCellSquare_const_mul]
    ring
  refine ⟨(hs.mul_left (c ^ 2)).congr (fun m => (he m).symm), ?_⟩
  calc
    _ = ∑' m, c ^ 2 * (w (D.cellIndex m) * profileScalarCellSquare D f m) :=
      tsum_congr he
    _ = _ := tsum_mul_left

private theorem profile_scalar_weighted_of_cell_le_two
    {D : ReferenceData} (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {f g v : ℝ → ℝ}
    (hbound : ∀ m, profileScalarCellSquare D v m ≤
      2 * (profileScalarCellSquare D f m + profileScalarCellSquare D g m))
    (hf : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m))
    (hg : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D g m)) :
    Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D v m) ∧
      (∑' m, w (D.cellIndex m) * profileScalarCellSquare D v m) ≤
        2 * ((∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m) +
          ∑' m, w (D.cellIndex m) * profileScalarCellSquare D g m) := by
  have hpt (m : ℕ) : w (D.cellIndex m) * profileScalarCellSquare D v m ≤
      2 * (w (D.cellIndex m) * profileScalarCellSquare D f m +
        w (D.cellIndex m) * profileScalarCellSquare D g m) := by
    calc
      _ ≤ w (D.cellIndex m) *
          (2 * (profileScalarCellSquare D f m + profileScalarCellSquare D g m)) :=
        mul_le_mul_of_nonneg_left (hbound m) (hw _)
      _ = _ := by ring
  have hs := (hf.add hg).mul_left 2
  have hv := Summable.of_nonneg_of_le
    (fun m => mul_nonneg (hw _) (profileScalarCellSquare_nonneg D v m)) hpt hs
  refine ⟨hv, (Summable.tsum_le_tsum hpt hv hs).trans_eq ?_⟩
  rw [tsum_mul_left, hf.tsum_add hg]

theorem profile_scalar_weighted_add
    {D : ReferenceData} (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {f g : ℝ → ℝ}
    (hflocal : ∀ m, MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D)))
    (hglocal : ∀ m, MemLp (fun r => D.localizer m r * g r) 2
      (volume.restrict (radialCore D)))
    (hf : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m))
    (hg : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D g m)) :
    Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D (fun r => f r + g r) m) ∧
      (∑' m, w (D.cellIndex m) * profileScalarCellSquare D (fun r => f r + g r) m) ≤
        2 * ((∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m) +
          ∑' m, w (D.cellIndex m) * profileScalarCellSquare D g m) :=
  profile_scalar_weighted_of_cell_le_two w hw
    (fun m => profileScalarCellSquare_add_le m (hflocal m) (hglocal m)) hf hg

theorem profile_scalar_weighted_sub
    {D : ReferenceData} (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) {f g : ℝ → ℝ}
    (hflocal : ∀ m, MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D)))
    (hglocal : ∀ m, MemLp (fun r => D.localizer m r * g r) 2
      (volume.restrict (radialCore D)))
    (hf : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m))
    (hg : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D g m)) :
    Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D (fun r => f r - g r) m) ∧
      (∑' m, w (D.cellIndex m) * profileScalarCellSquare D (fun r => f r - g r) m) ≤
        2 * ((∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m) +
          ∑' m, w (D.cellIndex m) * profileScalarCellSquare D g m) :=
  profile_scalar_weighted_of_cell_le_two w hw
    (fun m => profileScalarCellSquare_sub_le m (hflocal m) (hglocal m)) hf hg

end ContinuousFlexibility.Radial
