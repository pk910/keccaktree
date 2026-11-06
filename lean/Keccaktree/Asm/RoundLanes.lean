import Keccaktree.Asm.Cut
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
The lanes of one spec round, as explicit expressions in the lanes of the
input state (`L A j` atoms): `L (Spec.round r A) k = …`.  These are
definitional (`rfl`); the kernel lane lemmas rewrite the spec side with them
and leave the rest to `bv_decide`.  Generated from the FIPS 202 step
mappings: θ (column parities / `D`), ρ (the offsets), π (`B[y, 2x+3y]`),
χ, ι (the round constant on lane 0).
-/
namespace Keccaktree.Asm.X86
open Keccak

theorem round_lane_0 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 0 = ((L A 0 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 0 ^^^ (~~~ ((L A 6 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 44) &&& ((L A 12 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 43))) ^^^ Spec.RC r := rfl

theorem round_lane_1 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 1 = (L A 6 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 44 ^^^ (~~~ ((L A 12 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 43) &&& ((L A 18 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 21)) := rfl

theorem round_lane_2 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 2 = (L A 12 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 43 ^^^ (~~~ ((L A 18 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 21) &&& ((L A 24 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 14)) := rfl

theorem round_lane_3 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 3 = (L A 18 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 21 ^^^ (~~~ ((L A 24 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 14) &&& ((L A 0 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 0)) := rfl

theorem round_lane_4 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 4 = (L A 24 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 14 ^^^ (~~~ ((L A 0 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 0) &&& ((L A 6 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 44)) := rfl

theorem round_lane_5 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 5 = (L A 3 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 28 ^^^ (~~~ ((L A 9 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 20) &&& ((L A 10 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 3)) := rfl

theorem round_lane_6 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 6 = (L A 9 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 20 ^^^ (~~~ ((L A 10 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 3) &&& ((L A 16 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 45)) := rfl

theorem round_lane_7 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 7 = (L A 10 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 3 ^^^ (~~~ ((L A 16 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 45) &&& ((L A 22 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 61)) := rfl

theorem round_lane_8 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 8 = (L A 16 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 45 ^^^ (~~~ ((L A 22 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 61) &&& ((L A 3 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 28)) := rfl

theorem round_lane_9 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 9 = (L A 22 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 61 ^^^ (~~~ ((L A 3 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 28) &&& ((L A 9 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 20)) := rfl

theorem round_lane_10 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 10 = (L A 1 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 1 ^^^ (~~~ ((L A 7 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 6) &&& ((L A 13 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 25)) := rfl

theorem round_lane_11 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 11 = (L A 7 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 6 ^^^ (~~~ ((L A 13 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 25) &&& ((L A 19 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 8)) := rfl

theorem round_lane_12 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 12 = (L A 13 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 25 ^^^ (~~~ ((L A 19 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 8) &&& ((L A 20 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 18)) := rfl

theorem round_lane_13 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 13 = (L A 19 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 8 ^^^ (~~~ ((L A 20 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 18) &&& ((L A 1 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 1)) := rfl

theorem round_lane_14 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 14 = (L A 20 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 18 ^^^ (~~~ ((L A 1 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 1) &&& ((L A 7 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 6)) := rfl

theorem round_lane_15 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 15 = (L A 4 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 27 ^^^ (~~~ ((L A 5 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 36) &&& ((L A 11 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 10)) := rfl

theorem round_lane_16 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 16 = (L A 5 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 36 ^^^ (~~~ ((L A 11 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 10) &&& ((L A 17 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 15)) := rfl

theorem round_lane_17 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 17 = (L A 11 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 10 ^^^ (~~~ ((L A 17 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 15) &&& ((L A 23 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 56)) := rfl

theorem round_lane_18 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 18 = (L A 17 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 15 ^^^ (~~~ ((L A 23 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 56) &&& ((L A 4 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 27)) := rfl

theorem round_lane_19 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 19 = (L A 23 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 56 ^^^ (~~~ ((L A 4 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 27) &&& ((L A 5 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 36)) := rfl

theorem round_lane_20 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 20 = (L A 2 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 62 ^^^ (~~~ ((L A 8 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 55) &&& ((L A 14 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 39)) := rfl

theorem round_lane_21 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 21 = (L A 8 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 55 ^^^ (~~~ ((L A 14 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 39) &&& ((L A 15 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 41)) := rfl

theorem round_lane_22 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 22 = (L A 14 ^^^ ((L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23) ^^^ (L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20).rotateLeft 1)).rotateLeft 39 ^^^ (~~~ ((L A 15 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 41) &&& ((L A 21 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 2)) := rfl

theorem round_lane_23 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 23 = (L A 15 ^^^ ((L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24) ^^^ (L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21).rotateLeft 1)).rotateLeft 41 ^^^ (~~~ ((L A 21 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 2) &&& ((L A 2 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 62)) := rfl

theorem round_lane_24 (r : Nat) (A : Spec.State) :
    L (Spec.round r A) 24 = (L A 21 ^^^ ((L A 0 ^^^ L A 5 ^^^ L A 10 ^^^ L A 15 ^^^ L A 20) ^^^ (L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22).rotateLeft 1)).rotateLeft 2 ^^^ (~~~ ((L A 2 ^^^ ((L A 1 ^^^ L A 6 ^^^ L A 11 ^^^ L A 16 ^^^ L A 21) ^^^ (L A 3 ^^^ L A 8 ^^^ L A 13 ^^^ L A 18 ^^^ L A 23).rotateLeft 1)).rotateLeft 62) &&& ((L A 8 ^^^ ((L A 2 ^^^ L A 7 ^^^ L A 12 ^^^ L A 17 ^^^ L A 22) ^^^ (L A 4 ^^^ L A 9 ^^^ L A 14 ^^^ L A 19 ^^^ L A 24).rotateLeft 1)).rotateLeft 55)) := rfl

end Keccaktree.Asm.X86
