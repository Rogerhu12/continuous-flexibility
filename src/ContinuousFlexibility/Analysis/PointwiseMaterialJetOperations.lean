import ContinuousFlexibility.Analysis.PointwiseProductMaterialJets
import ContinuousFlexibility.Analysis.FlowJetLinearization

/-!
# Linear operations on actual pointwise material jets

These interfaces separate the numerical state grading from ordinary
finite-dimensional derivatives. In particular, taking an actual fixed
directional partial costs exactly one input order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def PointwiseMaterialJetBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (A : ℕ → ℝ)
    (z : E) (f : X → Y) (x : X) : Prop :=
  ∀ n : ℕ, ‖iteratedFDeriv ℝ n f x‖ ≤ A n * (1 + p (n + loss) z)

theorem PointwiseMaterialJetBound.mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {d e : ℕ} (hde : d ≤ e) {A B : ℕ → ℝ}
    (hA : ∀ n, 0 ≤ A n) (hAB : ∀ n, A n ≤ B n)
    {z : E} {f : X → Y} {x : X} (hf : PointwiseMaterialJetBound p d A z f x) :
    PointwiseMaterialJetBound p e B z f x := by
  intro n
  exact (hf n).trans (mul_le_mul (hAB n)
    (add_le_add (le_refl (1 : ℝ)) ((hp (Nat.add_le_add_left hde n)) z))
    (add_nonneg zero_le_one (apply_nonneg _ _)) ((hA n).trans (hAB n)))

theorem PointwiseMaterialJetBound.clm_comp
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ}
    {z : E} {f : X → Y} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (hbound : PointwiseMaterialJetBound p loss A z f x) (L : Y →L[ℝ] Z) :
    PointwiseMaterialJetBound p loss (fun n => ‖L‖ * A n) z (L ∘ f) x := by
  intro n
  exact (L.norm_iteratedFDeriv_comp_left hf (by simp : (n : ℕ∞ω) ≤ ∞)).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg L))

theorem PointwiseMaterialJetBound.contractive_clm_comp
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ}
    {z : E} {f : X → Y} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (hb : PointwiseMaterialJetBound p loss A z f x)
    (L : Y →L[ℝ] Z) (hL : ‖L‖ ≤ 1) :
    PointwiseMaterialJetBound p loss A z (L ∘ f) x := by
  intro n
  exact (L.norm_iteratedFDeriv_comp_left hf (by simp : (n : ℕ∞ω) ≤ ∞)).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hb n))

theorem PointwiseMaterialJetBound.sub
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A B : ℕ → ℝ}
    {z : E} {f g : X → Y} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hbf : PointwiseMaterialJetBound p loss A z f x)
    (hbg : PointwiseMaterialJetBound p loss B z g x) :
    PointwiseMaterialJetBound p loss (fun n => A n + B n) z (fun y => f y - g y) x := by
  have he : (fun y => f y - g y) = f - g := by funext y; rfl
  intro n
  rw [he, iteratedFDeriv_sub_apply
    (hf.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (n : ℕ∞ω) ≤ ∞))]
  exact (norm_sub_le _ _).trans ((add_le_add (hbf n) (hbg n)).trans_eq
    (by ring))

theorem PointwiseMaterialJetBound.const_mul
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ}
    {z : E} {f : X → ℝ} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hb : PointwiseMaterialJetBound p loss A z f x)
    (c : ℝ) :
    PointwiseMaterialJetBound p loss (fun n => |c| * A n) z (fun y => c * f y) x := by
  intro n
  change ‖iteratedFDeriv ℝ n (fun y => c • f y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    (hf.of_le (by simp : (n : ℕ∞ω) ≤ ∞)), norm_smul, Real.norm_eq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n) (abs_nonneg c)

theorem PointwiseMaterialJetBound.prodMk
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A B : ℕ → ℝ}
    {z : E} {f : X → Y} {g : X → Z} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (hbf : PointwiseMaterialJetBound p loss A z f x)
    (hbg : PointwiseMaterialJetBound p loss B z g x) :
    PointwiseMaterialJetBound p loss (fun n => max (A n) (B n)) z
      (fun y => (f y, g y)) x := by
  intro n
  rw [iteratedFDeriv_prodMk
    (hf.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (n : ℕ∞ω) ≤ ∞)) le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le
    ((hbf n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg zero_le_one (apply_nonneg _ _))))
    ((hbg n).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg zero_le_one (apply_nonneg _ _))))

theorem PointwiseMaterialJetBound.directionalPartial
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ}
    {z : E} {f : X → Y} {x : X}
    (hf : ContDiffAt ℝ ∞ f x) (hb : PointwiseMaterialJetBound p loss A z f x)
    (v : X) (hv : ‖v‖ ≤ 1) :
    PointwiseMaterialJetBound p (loss + 1) (fun n => A (n + 1)) z
      (fun y => fderiv ℝ f y v) x := by
  intro n
  have hd := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ f) (c := v) (x := x) (n := n)
    (hf.fderiv_right (m := ∞) (by simp)) (by simp)
  have hn : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
    rw [norm_iteratedFDeriv_fderiv] at hd
    exact hd.trans (mul_le_of_le_one_left (norm_nonneg _) hv)
  simpa only [show n + 1 + loss = n + (loss + 1) by omega] using
    hn.trans (hb (n + 1))

/-- A fixed linear coordinate has bounded jets at every point where its
value is bounded. No norm of the other coordinates enters this estimate. -/
theorem pointwiseMaterialJetBound_linear
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (p : ℕ → Seminorm ℝ E) (loss : ℕ) (z : E)
    (L : X →L[ℝ] Y) (x : X) {M : ℝ} (hM : 0 ≤ M)
    (hL : ‖L‖ ≤ M) (hx : ‖L x‖ ≤ M) :
    PointwiseMaterialJetBound p loss (fun _ => M) z (L : X → Y) x := by
  intro n
  have hb : ‖iteratedFDeriv ℝ n (L : X → Y) x‖ ≤ M := by
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hx
    | succ n => exact (flowJet_norm_iteratedFDeriv_clm_le L (Nat.succ_pos n) x).trans hL
  exact hb.trans (le_mul_of_one_le_right hM
    (le_add_of_nonneg_right (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
