import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators

/-!
# Some math lemmas

## Notations

This file defines the notation `ℝ>0` for positive real numbers `{c : ℝ // 0 < c}`.
-/

section Real

def PosReal := { c : ℝ // 0 < c }
notation "ℝ>0" => PosReal
namespace PosReal
instance : Coe ℝ>0 NNReal :=
  ⟨fun c ↦ ⟨c.val, by exact c.property.le⟩⟩
lemma ne_zero (c : ℝ>0) : c.val ≠ 0 := by simpa using ne_of_gt c.property
noncomputable instance : LinearOrder ℝ>0 := Subtype.linearOrder _
end PosReal

@[simp] lemma Real.max_mul_nonneg_zero {c x : ℝ} (hc : 0 ≤ c) : max (c * x) 0 = c * (max x 0) := by
  by_cases hx : x ≤ 0
  · simp [hx]; exact mul_nonpos_of_nonneg_of_nonpos hc hx
  · rw [not_le] at hx; simp [hx, hc]
    left; exact (max_eq_left hx.le).symm

end Real

namespace Finsupp
open Finset

variable {α : Type*} [DecidableEq α]
variable {R : Type*} [DecidableEq R] [Semiring R] [NoZeroSMulDivisors R R]
variable {f g : α →₀ R}

@[reducible] def sum_image (f : α →₀ R) := f.support.sum f
lemma extend_support_sum_iamge {s : Finset α}
  (s_extend_supp : f.support ⊆ s) : s.sum f = f.sum_image := by
  rw [←sum_sdiff s_extend_supp]
  simp only [sum_image]
  suffices (s \ f.support).sum f = 0 from by rw [this, zero_add]
  simp [Finset.sum_eq_zero, s_extend_supp]
lemma sum_image_add : (f + g).sum_image = f.sum_image + g.sum_image := by
  let s := f.support ∪ g.support
  have : (f + g).support ⊆ s := support_add           ; rw [←extend_support_sum_iamge this]
  have :       f.support ⊆ s := subset_union_left _ _ ; rw [←extend_support_sum_iamge this]
  have :       g.support ⊆ s := subset_union_right _ _; rw [←extend_support_sum_iamge this]
  exact Finset.sum_add_distrib
lemma sum_image_smul {c : R} : (c • f).sum_image = c • f.sum_image := by
  by_cases hc : c = 0
  · simp [hc, zero_smul]; rfl
  · have : (c • f).support = f.support := by simp [hc]
    simp only [sum_image, this, Finset.smul_sum]; rfl

lemma support_add_exact {supp : Finset α}
  (non_zero_on_supp   : ∀ x ∈ supp                          , f x + g x ≠ 0)
  (zero_on_sdiff_supp : ∀ x ∈ (f.support ∪ g.support) \ supp, f x + g x = 0) :
  (f + g).support = supp := by
  ext x; simp [mem_support_iff]
  constructor
  · contrapose!; intro hx_not_supp
    if hx_union : x ∈ (f.support ∪ g.support) then
      have : x ∈ (f.support ∪ g.support) \ supp := by
        simp only [mem_sdiff, hx_union, hx_not_supp]
        tauto
      exact zero_on_sdiff_supp _ this
    else
      rw [not_mem_union] at hx_union
      have zero_fx : f x = 0 := by simpa using hx_union.1
      have zero_gx : g x = 0 := by simpa using hx_union.2
      rw [zero_fx, zero_gx, zero_add]
  · exact non_zero_on_supp _

end Finsupp
