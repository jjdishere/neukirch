/-
GOAL: prove `ℤ⟦X⟧⧸(X-p) ≃ ℤ_[p]`

Two possible approaches:
1. Direcly prove the surj. and compute the ker.
2. by realising `ℤ⟦X⟧⧸(X-p)` as a proj lim.
-/

import LFS.Xadic

open PowerSeries PadicInt

noncomputable section

variable (p : ℕ) [Fact p.Prime]

section padic

variable {R : Type*} [NonAssocSemiring R] {f : (k : ℕ) → R →+* ZMod (p ^ k)}
variable  (f_compat : ∀(m n : ℕ) (mlen : m ≤ n), (ZMod.castHom (pow_dvd_pow p mlen) (ZMod (p ^ m))).comp (f n) = f m)

open Classical

/- The following proposition is incorrect (e.g., `R := ℤ`),
perhaps for we have to take limit in `R` -/
example (f_surj : ∀k : ℕ, Function.Surjective (f k)):
    Function.Surjective (lift f_compat) := sorry

end padic

namespace PSZ

section toZMod
-- The homomorphism `ℤ⟦X⟧ → ℤ ⧸ a ^ n` mapping `X` to `a`.
def toZModPow (a n : ℕ) : PowerSeries ℤ →+* ZMod (a ^ n) :=
  eval₂RingHom (Int.castRingHom (ZMod (a ^ n))) ⟨a, nat_mod_pow_nilp⟩

@[simp]
lemma aux2 {a n : ℕ} : (toZModPow a n) X = (a : ZMod (a ^ n)) := by
  simp only [toZModPow, eval₂RingHom, eval₂AddMonoidHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, eval₂_X]

theorem toZModPow_surj {a n : ℕ} [NeZero a]:
    Function.Surjective (toZModPow a n) :=
  fun b ↦ ⟨C _ (ZMod.val b),
    by simp only [ZMod.nat_cast_val, eq_intCast, ZMod.int_cast_cast, ZMod.ringHom_map_cast]⟩

theorem toZModPow_compat {a : ℕ}:
    ∀ (m n : ℕ) (mlen : m ≤ n),
      (ZMod.castHom (pow_dvd_pow a mlen) (ZMod (a ^ m))).comp (toZModPow a n) = (toZModPow a m) := by
  intro m n mlen
  refine (ringHom_ext_Z ?_ ?_).symm
  · simp only [aux2, RingHom.coe_comp, Function.comp_apply, map_natCast]
  · rw [aux2]; exact nat_mod_pow_nilp

def I (a : ℕ): Ideal ℤ⟦X⟧ := Ideal.span {(X : ℤ⟦X⟧) - a}
-- def PSZquot := ℤ⟦X⟧ ⧸ I p
-- #synth CommRing (ℤ⟦X⟧⧸ I p)
-- #synth CommRing (PSZquot p)

theorem toZModPow_I_zero_aux {a n : ℕ} :
    (toZModPow a n) ((X : ℤ⟦X⟧) - a) = 0 := by
  simp only [map_sub, aux2, map_natCast, sub_self]

theorem I_le_ker_toZMod_aux {a n : ℕ} :
    (X : ℤ⟦X⟧) - a ∈ RingHom.ker (toZModPow a n) :=
  toZModPow_I_zero_aux

theorem I_le_ker_toZModPow {a n : ℕ} :
    I a ≤ RingHom.ker (toZModPow a n) :=
  (Ideal.span_singleton_le_iff_mem (RingHom.ker (toZModPow a n))).mpr I_le_ker_toZMod_aux

theorem toZModPow_I_zero {a n : ℕ} {f : ℤ⟦X⟧} (h : f ∈ I a) :
    (toZModPow a n) f = 0 :=
  I_le_ker_toZModPow h

theorem toZModPow_I_zero' {a n : ℕ} :
    ∀f ∈ I a, (toZModPow a n) f = 0 :=
  I_le_ker_toZModPow


/- To simulate the construction of `W(𝔽_p) ≃ ℤ_p`,
we first construct the isom `ℤ⟦X⟧⧸(X-a, X^n)≃ℤ⧸a^n`.
-/
def kerToZModPow (a n : ℕ) : Ideal ℤ⟦X⟧ := Ideal.span {(X : ℤ⟦X⟧) - a, X ^ n}

instance instFintypeQuotKerToZModPow {a n : ℕ} :
    Fintype (ℤ⟦X⟧ ⧸ kerToZModPow a n) where
  elems := sorry
  complete := sorry

-- morphism bwtween quotients
def quotHom (a : ℕ) {m n : ℕ} (mlen : m ≤ n) :
    ℤ⟦X⟧ ⧸ kerToZModPow a n →+* ℤ⟦X⟧ ⧸ kerToZModPow a m where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

theorem quot_kerToZModPow_card {a n : ℕ} :
    Fintype.card (ℤ⟦X⟧ ⧸ kerToZModPow a n) = a ^ n := by
  sorry

instance instCharP {a n : ℕ} :
    CharP (ℤ⟦X⟧ ⧸ kerToZModPow a n) (a ^ n) where
  cast_eq_zero_iff' := sorry

def zmodEquivQuot (a n : ℕ) :
    ZMod (a ^ n) ≃+* ℤ⟦X⟧ ⧸ kerToZModPow a n :=
  ZMod.ringEquiv _ quot_kerToZModPow_card

theorem kerToZModPow_eq_ker {a n : ℕ} :
    RingHom.ker (toZModPow a n) = kerToZModPow a n := by
  ext f; constructor
  · sorry
  · sorry


-- The morphism `ℤ⟦X⟧ ⧸ (X - a) → ℤ ⧸ a ^ n` mapping `X` to `a` induced from `toZModPow`
def quotI_toZModPow (a n : ℕ) :
    ℤ⟦X⟧ ⧸ I a →+* ZMod (a ^ n) :=
  Ideal.Quotient.lift _ _ toZModPow_I_zero'

theorem quotI_toZModPow_surj {a n : ℕ} [NeZero a]:
    Function.Surjective (quotI_toZModPow a n) :=
  Ideal.Quotient.lift_surjective_of_surjective _ toZModPow_I_zero' toZModPow_surj

end toZMod

section toPadic

-- Define the canonical morphism `ℤ⟦X⟧ → ℤ_[p]` using the universal property of `ℤ_[p]`.
def toPadicInt : PowerSeries ℤ →+* ℤ_[p] :=
    lift toZModPow_compat

theorem toPadicInt_surj :
    Function.Surjective (toPadicInt p) := by
  intro b
  let f : ℤ⟦X⟧ := PowerSeries.mk fun
    | .zero => 0
    | .succ n => (appr b (n + 1) - appr b n) / p ^ n
  /-
  goal: `f.toPadicInt p = b`
  the coeff of `f` forms a p adic expansion of `b`
  BUT, due to the def of `Nat.div` this def unlikely works......
  -/
  sorry

theorem ker_toPadicInt :
    RingHom.ker (toPadicInt p) = Ideal.span {(X : ℤ⟦X⟧) - p} := by
  ext f; constructor
  · intro h
    sorry
  · intro h
    apply ext_of_toZModPow.mp
    intro n
    rw [map_zero]
    calc
      _ = (PadicInt.toZModPow n).comp (toPadicInt p) f := by sorry
      _ = (toZModPow p n) f := sorry
      _ = 0 := toZModPow_I_zero h

    -- rw [lift_spec _ n]

end toPadic
#check ZMod.ringEquiv
