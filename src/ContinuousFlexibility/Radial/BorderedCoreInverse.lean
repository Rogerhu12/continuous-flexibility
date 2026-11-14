module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Adjoint inversion on a bordered Hilbert space

The ordinary product retains its max norm. Its Hilbert pairing is used
explicitly, and the four block adjoints give a bounded adjoint for this
pairing. A bounded left inverse on a symmetric test core is the full
maximal inverse as soon as the maximal homogeneous kernel is zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def borderedPairing (u v : E × ℝ) : ℝ :=
  ⟪u.1, v.1⟫_ℝ + ⟪u.2, v.2⟫_ℝ

theorem borderedPairing_comm (u v : E × ℝ) :
    borderedPairing u v = borderedPairing v u := by
  simp only [borderedPairing, real_inner_comm]

@[simp] theorem borderedPairing_zero_left (u : E × ℝ) :
    borderedPairing 0 u = 0 := by
  simp [borderedPairing]

@[simp] theorem borderedPairing_zero_right (u : E × ℝ) :
    borderedPairing u 0 = 0 := by
  simp [borderedPairing]

theorem borderedPairing_sub_left (u v w : E × ℝ) :
    borderedPairing (u - v) w = borderedPairing u w - borderedPairing v w := by
  simp only [borderedPairing, Prod.fst_sub, Prod.snd_sub, inner_sub_left]
  ring

/-- The adjoint of the four blocks. No inner-product instance is put on
the max-norm product. -/
def borderedAdjoint (R : (E × ℝ) →L[ℝ] (E × ℝ)) :
    (E × ℝ) →L[ℝ] (E × ℝ) :=
  let P := ContinuousLinearMap.fst ℝ E ℝ
  let Q := ContinuousLinearMap.snd ℝ E ℝ
  let I := ContinuousLinearMap.inl ℝ E ℝ
  let J := ContinuousLinearMap.inr ℝ E ℝ
  (((P.comp R).comp I).adjoint.comp P +
      ((Q.comp R).comp I).adjoint.comp Q).prod
    (((P.comp R).comp J).adjoint.comp P +
      ((Q.comp R).comp J).adjoint.comp Q)

theorem borderedAdjoint_pairing_left
    (R : (E × ℝ) →L[ℝ] (E × ℝ)) (u v : E × ℝ) :
    borderedPairing (borderedAdjoint R u) v = borderedPairing u (R v) := by
  have hv : R (v.1, 0) + R (0, v.2) = R v := by
    rw [← map_add]
    congr 1
    ext <;> simp
  calc
    borderedPairing (borderedAdjoint R u) v =
        (⟪u.1, (R (v.1, 0)).1⟫_ℝ + ⟪u.2, (R (v.1, 0)).2⟫_ℝ) +
        (⟪u.1, (R (0, v.2)).1⟫_ℝ + ⟪u.2, (R (0, v.2)).2⟫_ℝ) := by
      simp only [borderedPairing, borderedAdjoint, ContinuousLinearMap.prod_apply,
        add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
    _ = borderedPairing u (R (v.1, 0) + R (0, v.2)) := by
      simp only [borderedPairing, Prod.fst_add, Prod.snd_add, inner_add_right]
      ring
    _ = borderedPairing u (R v) := congrArg (borderedPairing u) hv

theorem borderedAdjoint_pairing_right
    (R : (E × ℝ) →L[ℝ] (E × ℝ)) (u v : E × ℝ) :
    borderedPairing (R u) v = borderedPairing u (borderedAdjoint R v) := by
  rw [borderedPairing_comm (R u) v,
    ← borderedAdjoint_pairing_left R v u, borderedPairing_comm]

def BorderedCoreAdjoint
    (core : (E × ℝ) → (E × ℝ) → Prop) (u f : E × ℝ) : Prop :=
  ∀ v g, core v g → borderedPairing u g = borderedPairing f v

/-- A zero maximal kernel supplies uniqueness without a density assumption
being smuggled into the definition of the test core. -/
theorem BorderedCoreAdjoint.unique
    {core : (E × ℝ) → (E × ℝ) → Prop}
    (hkernel : ∀ u, BorderedCoreAdjoint core u 0 → u = 0)
    {u v f : E × ℝ} (hu : BorderedCoreAdjoint core u f)
    (hv : BorderedCoreAdjoint core v f) : u = v := by
  apply sub_eq_zero.mp
  apply hkernel
  intro x y hxy
  rw [borderedPairing_sub_left, hu x y hxy, hv x y hxy,
    sub_self, borderedPairing_zero_left]

/-- Core left inversion and maximal homogeneous uniqueness prove exact
inversion on the full weak graph. The argument also proves symmetry of
the bounded inverse, rather than assuming it for local inverse fields. -/
theorem bordered_inverse_of_core
    (core : (E × ℝ) → (E × ℝ) → Prop)
    (R : (E × ℝ) →L[ℝ] (E × ℝ))
    (hsymmetric : ∀ u f, core u f → BorderedCoreAdjoint core u f)
    (hkernel : ∀ u, BorderedCoreAdjoint core u 0 → u = 0)
    (hleft : ∀ u f, core u f → R f = u) :
    (∀ f, BorderedCoreAdjoint core (R f) f) ∧
      (∀ u f, BorderedCoreAdjoint core u f → R f = u) ∧
      borderedAdjoint R = R := by
  have hadjoint (f : E × ℝ) :
      BorderedCoreAdjoint core (borderedAdjoint R f) f := by
    intro u g hug
    rw [borderedAdjoint_pairing_left, hleft u g hug]
  have hadjoint_left (u f : E × ℝ) (huf : core u f) :
      borderedAdjoint R f = u :=
    BorderedCoreAdjoint.unique hkernel (hadjoint f) (hsymmetric u f huf)
  have heq (f : E × ℝ) : R f = borderedAdjoint R f := by
    apply sub_eq_zero.mp
    apply hkernel
    intro u g hug
    rw [borderedPairing_sub_left, borderedAdjoint_pairing_right,
      borderedAdjoint_pairing_left, hadjoint_left u g hug, hleft u g hug,
      sub_self, borderedPairing_zero_left]
  have hright (f : E × ℝ) : BorderedCoreAdjoint core (R f) f := by
    rw [heq f]
    exact hadjoint f
  refine ⟨hright, ?_, ?_⟩
  · intro u f huf
    exact BorderedCoreAdjoint.unique hkernel (hright f) huf
  · apply ContinuousLinearMap.ext
    intro f
    exact (heq f).symm

end ContinuousFlexibility.Radial
